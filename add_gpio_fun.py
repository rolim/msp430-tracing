#!/usr/bin/env python3
# to profile script: python3 -m cProfile -o profile add_gpio_fun.py
# to browse profile: python3 -m pstats profile
#  or ./pyprof2calltree-1.3.2/pyprof2calltree.py -k -i profile
#  or snakeviz profile
# to debug script: python3 -m pdb add_gpio_fun.py
import os, sys, shutil
sys.path.append("%s/lib" % os.path.dirname(os.path.realpath(__file__)))
sys.path.append("%s/lib/coding" % os.path.dirname(os.path.realpath(__file__)))
sys.path.append("%s/lib/elffile" % os.path.dirname(os.path.realpath(__file__)))
import elffile
import optparse
import itertools
import glob
import pprint
import struct
import copy
import fractions
import pickle as pickle
import time
import operator
import math
import json
from tracing import *

LOOP_MULTIPLIER = 10 # for weighting heuristic
FAKEADDRESS_OFFSET = 0x10000
USE_UNIQUE_MARKERS = False # Globally unique markers, usefull for debugging
USE_CFG_UNIQUE_MARKERS = True # Unique markers for each CFG. This is needed for the none_and_reduction method, since we don't know in advance which markers are going to be left out.
CPU_SPEED_ERROR = 0.01 # if value bigger than 0: include error in speed estimate when checking for feasible instrumentation. '0.01' means '1%'
#ALLOW_LOOPS_IN_TIMED = (CPU_SPEED_ERROR == 0) # allow loops without markers, needs very precise time measurements to be accurate, or upper bounds.
ALLOW_LOOPS_IN_TIMED = True
#TIME_METHOD = 'timegraph'
#TIME_METHOD = 'reduction'
TIME_METHOD = 'none' # Standard method using spanning tree, no time information
#TIME_METHOD = 'none_and_reduction' # Instrumentation using spanning tree, lookup table using time information. Used for verification of time method. Should only be used with unique markers

INDIRECT_CALL_NAMES = ['putchar'] # list of functions that are known to be called indirectly (must be adapted by the user)
ELF_SECTION_ABS = 0xfff1
    
def accumulateCycles(bbs):
    from tracing import LoopBlock
    cycles=[0]
    loopcycles=[0]
    for b in bbs:
        cycles.append(cycles[-1] + b.cycles)
        if isinstance(b,LoopBlock):
            loopcycles.append(loopcycles[-1] + b.loopcycles)
        else:
            loopcycles.append(loopcycles[-1])
    return list(zip(cycles[1:],loopcycles[1:]))
    
def totalCycles(bbs):
    r = accumulateCycles(bbs)
    return r[-1]

class IndirectCallException(Exception):
    pass
      
class Instruction(object):

    jumptg = None
    
    arg0 = None
    arg1 = None
    arg2 = None
    addr = None
    indtargets = None
    directtarget = None
    inbb = None
    
    def __init__(self, op, sreg, dreg, As, Ad, size):
        self.opcode = op
        self.sreg = sreg
        self.dreg = dreg
        self.As = As
        self.Ad = Ad
        self.size = size
        self.symtabptr = []
        self.modified = True # If instruction is modified (not location, but argument)
        
    def initArg0Type1(self):
        self.arg0 = (self.opcode & 0xf000) | (self.sreg << 8) | self.dreg | (self.Ad << 7) | (self.As << 4)
        
    def isCall(self):
        return self.opcode == 0x1280
        
    def isIndCall(self):
        return self.Ad != 3
        
    def setCallTarget(self, newtarget):
        assert(self.isCall())
        self.arg1 = newtarget
        self.modified = True
        self.updateDirectTarget()
    
    def isCondJmp(self):
        return self.opcode >= 0x2000 and self.opcode < 0x3c00
        
    def setCondJmpTarget(self, newtarget):
        assert(self.isCondJmp())
        #assert(newtarget - self.addr - 2 < 512 and newtarget - self.addr - 2 > -511, 'Conditional target too far for relative jump %x->%x' % (self.addr, newtarget))
        assert (newtarget - self.addr - 2 < 512 and newtarget - self.addr - 2 > -511), 'Conditional target too far for relative jump %x->%x' % (self.addr, newtarget)
        self.arg0 = (self.arg0 & ~(0x3ff)) | (((newtarget - self.addr - 2) >> 1) & 0x3ff)
        self.modified = True
            
    def isJmp(self):
        return (self.opcode & 0x3c00 == 0x3c00) or ((self.opcode >> 12) == 0x4 and self.dreg == 0 and self.sreg == 0)
        
    def setJmpTarget(self, newtarget):
        assert(self.isJmp())
        if self.opcode & 0x3c00 == 0x3c00: # rel jmp
            assert newtarget - self.addr - 2 < 512 and newtarget - self.addr - 2 > -511, 'Unconditional target too far for relative jump %x->%x' % (self.addr, newtarget)
            assert(newtarget - self.addr - 2 < 512 and newtarget - self.addr - 2 > -511)
            self.arg0 = (self.arg0 & ~(0x3ff)) | (((newtarget - self.addr - 2) >> 1) & 0x3ff)
        else:
            self.arg1 = newtarget
            self.modified = True
            self.updateDirectTarget()
        
    def isIndJmp(self):        
        return (self.opcode >> 12) == 0x4 and self.dreg == 0 and self.As == 1 and self.Ad == 0
        
    def isRet(self):
        return self.opcode == 0x4000 and self.sreg == 1 and self.dreg == 0 and self.As == 3
        
    def isReti(self):
        return self.arg0 == 0x1300
        
    def branchTargets(self):
        """
        returns target of branch (without fall through)
        """
        if self.isCondJmp():
            return [self.addr + self.jumptg]
        
        elif self.isJmp():
            if self.opcode & 0x3c00 == 0x3c00: # relative jump
                return [self.addr + self.jumptg]
            else:
                return [self.arg1] # absolute jump
    
    def targets(self):
        if self.isCall():
            #if self.Ad != 3: # not immediate
                #raise IndirectCallException()
            #else:
            return[self.addr + self.size * 2] #return [self.arg1]
                
        elif self.isCondJmp():
            return [self.addr + self.jumptg, self.addr + self.size * 2]
        
        elif self.isJmp():
            if self.opcode & 0x3c00 == 0x3c00:
                return [self.addr + self.jumptg]
            else:
                return [self.arg1]
        elif self.isRet() or self.isReti():
            return []
        elif self.isIndJmp() and not self.indtargets is None:
            return self.indtargets
        else:
            return [self.addr + self.size * 2]
            
    def __repr__(self):
        if self.addr:
            addr = self.addr
        else:
            addr = 0
        if self.size == 3:
            return '%x: %x %x %x' % (addr, self.arg0, self.arg1, self.arg2)
        elif self.size == 2:
            return '%x: %x %x' % (addr, self.arg0, self.arg1)
        else:
            return '%x: %x' % (addr, self.arg0)
    
    def getBytes(self):
        try:
            if self.size == 3:
                return struct.pack('<3H', self.arg0, self.arg1, self.arg2)
            elif self.size == 2:
                return struct.pack('<2H', self.arg0, self.arg1)
            else:
                return struct.pack('<1H', self.arg0)  
        except struct.error:
            print("could not pack instruction %s" % str(self))
            raise
            
    def setWordType(self):
        self.arg0 = self.arg0 & ~0x0040
    
    def setByteType(self):
        self.arg0 = self.arg0 | 0x0040
        
    def updateDirectTarget(self):
        if self.isCall() or self.isJmp() and self.size == 2:
            self.directtarget = self.arg1
    
    def cycleCountDbg(self):
        if self.isReti():
            return (5,'reti')
        cycles = 0
        t = ''
        # reg = 2 and As = 01 > abs address mode
        if self.Ad is None and self.As is None:
            #print '%s type III jump' % self
            cycles = 2
            t = 'type III jump'
        elif self.As is None:
            t = 'type II single operand'
            #print '%s type II single operand' % self
            if self.isCall(): # call
                if self.Ad == 0 or self.Ad == 2:
                    cycles = 4
                else:
                    cycles = 5
            elif self.opcode == 0x1200: # push
                if self.Ad == 0:
                    cycles = 3
                elif self.Ad == 2:
                    cycles = 4
                elif self.Ad == 3 and self.sreg == 2:
                    cycles = 4
                else:
                    cycles = 5
            else:
                if self.Ad == 0:
                    cycles = 1
                elif self.Ad == 1:
                    cycles = 4
                else:
                    cycles = 3            
        else:
            t = 'type I double operand'
            #print '%s type I double operand' % self
            #src
            if self.As == 0 or self.sreg == 3 or self.sreg == 2 and self.As >= 2: # reg, including constant generator
                cycles += 1
            elif self.As == 1: # abs / rel mem
                cycles += 3
            elif self.As >= 2: # r is pointer
                cycles += 2
            # dst
            if self.dreg == 0 and self.Ad == 0: # dst, PC
                if self.As == 0:
                    cycles += 1
                elif self.As == 3:
                    cycles += 1
            elif self.Ad == 1: # mem
                    cycles += 3
        return (cycles, t)
        
    def cycleCount(self):
        c,d = self.cycleCountDbg()
        return c
        
    def imm2const(self):
        """replace op1 immediate value with CG value if possible"""
        if self.size == 3:
            if self.arg1 in [-1,0,1,2,4,8]:
                if self.arg1 >= 4:
                    r=2
                    s=1 + (self.arg1 >> 2)
                else:
                    r=3
                    s=self.arg1
                    if s < 0:
                        s = 3
                self.As = s
                self.sreg = r
                self.arg0 = self.arg0 & 0xf0cf | r << 8 | s << 4
                self.arg1 = self.arg2
                self.arg2 = None
                self.size = self.size - 1
                
    def usesSr(self):
        return self.opcode in (0x6000, 0x7000, 0xa000, 0x1000, 0x2000, 0x2400, 0x2800, 0x2c00, 0x3400, 0x3800) or self.sreg == 2 and self.As == 0
        
    def modifiesSr(self):
        return self.opcode in (0x5000, 0x6000, 0x7000, 0x8000, 0x9000, 0xa000, 0xb000, 0xe000, 0xf000, 0x1000, 0x1040, 0x1100, 0x1140, 0x11c0) or self.dreg == 2 and self.As == 0
        
    def isWriteToSr(self):
        """
        Instructions that change the status register (potential LPM start)
        2           4280:       32 41           pop     r2                      <-- hwmul lib (very unlikely to enter LPM)
        2           4668:       22 d1           bis     @r1,    r2              <-- standard tinyos LPM
        2           468e:       32 d0 f0 00     bis     #240,   r2      ;#0x00f0<-- gcc stop program exec
        split bb having (direct) SR write instructions
        add blocking marker for SR write blocks (to remove timing ambiguity)
        add blocking marker to followup block to detect wakeup
        
        filter dint / eint instructions, i.e. set / clear GIE
        filter pop SR, very unlikely to enter LPM like this
        """
        return self.dreg == 2 and self.Ad == 0 and (not self.opcode in (0x9000, 0xb000)) and (not (self.opcode in (0xc000, 0xd000) and self.sreg in (2,3))) and not (self.sreg==1 and self.As==3)
    
class IMovImmAddr(Instruction):
    def __init__(self, imm, addr, bytemode=True):
        super(IMovImmAddr, self).__init__(0x4000, 0, 0, 3, 1, 3)
        self.arg0 = 0x40b2
        self.arg1 = imm
        self.arg2 = addr
        if bytemode:
            self.setByteType()
        self.imm2const()

class IXorImmAddr(Instruction):
    def __init__(self, imm, addr, bytemode=True):
        super(IXorImmAddr, self).__init__(0xe000, 0, 0, 3, 1, 3)
        assert(imm <= 0xffff)
        assert(addr <= 0xffff)
        self.arg0 = 0xe0b2
        self.arg1 = imm
        self.arg2 = addr
        if bytemode:
            self.setByteType()
            assert(imm <= 0xff)
        self.imm2const()
        
class IBitImmOfsReg(Instruction):
    def __init__(self, imm, ofs, reg):
        super(IBitImmOfsReg, self).__init__(0xb000, 0, reg, 3, 1, 3)
        self.initArg0Type1()
        self.arg1 = imm
        self.arg2 = ofs

class IXorRegAddr(Instruction):
    def __init__(self, reg, addr, bytemode=True):
        super(IXorRegAddr, self).__init__(0xe000, reg, 2, 0, 1, 2)
        self.initArg0Type1()
        self.arg1 = addr
        if bytemode:
            self.setByteType()

class IBr(Instruction):
    def __init__(self, addr):
        super(IBr, self).__init__(0x4000, 0, 0, 3, 0, 2)
        self.arg0 = 0x4030
        self.arg1 = addr

class IJmp(Instruction):
    def __init__(self, rel):
        super(IJmp, self).__init__(0x3c00, 0, 0, None, None, 1)
        self.arg0 = 0x3c00 & ~(0x3ff) | ((rel - 1) << 1) & 0x3ff

class IPushSr(Instruction):
    def __init__(self):
        super(IPushSr, self).__init__(0x1200, 2, 0, 0, 0, 1)
        self.arg0 = self.opcode | 2

class IPopSr(Instruction):
    def __init__(self):
        super(IPopSr, self).__init__(0x4100, 0, 2, 3, 0, 1)
        self.arg0 = self.opcode | 2 | self.As << 4

## instruction parsing functions ##
def op(val):
    # single op (format II) 8 bits opcode
    if val >= 0x1400 and val < 0x2000 or val < 0x1000:
        Ad = (val & 0x30) >> 4
        ret = Instruction((val & 0xff00), None, None, None, Ad, 1)
        #return 1 # exception format II (pushm, popm)
    elif val < 0x1400:
        Ad = (val & 0x30) >> 4
        Sreg = (val & 0x000F)
        if (Sreg == 3) or (Ad>1 and Sreg==2):
            ret = Instruction((val & 0xff80), Sreg, None, None, Ad, 1)
        else:
            ret = Instruction((val & 0xff80), Sreg, None, None, Ad, 1 + min(Ad,1))
    # jmp                   3 bits opcode
    elif val >= 0x2000 and val < 0x4000:
        I = Instruction((val & 0xff00), None, None, None, None, 1)        
        I.jumptg = val & 0x3ff
        if I.jumptg & 0x200 > 0:
            I.jumptg = I.jumptg | 0xfc00
            I.jumptg = struct.unpack('<h',struct.pack('<H',I.jumptg))
            I.jumptg = I.jumptg[0]
        I.jumptg = (I.jumptg + 1) * 2
        ret = I
    # double op (format I)  4 bits opcode
    elif val >= 0x4000:
        As = (val & 0x30) >> 4
        Ad = (val & 0x80) >> 7
        Sreg = (val & 0x0F00) >> 8
        Dreg = (val & 0x000F)
        Added = 0
        if As == 1 or (As == 3 and Sreg == 2):
            Added = 1
        elif As == 3:
            if Sreg == 0: # PC -> immediate value
                Added = 1
            else:
                Added = 0
        else:
            Added = 0
        if (Sreg == 2 or Sreg == 3) and not (As<=1 and Sreg==2): # constant register
            ret = Instruction((val & 0xf000), Sreg, Dreg, As, Ad, 1 + Ad)
        else:
            ret = Instruction((val & 0xf000), Sreg, Dreg, As, Ad, 1 + Ad + Added)
    ret.modified = False
    return ret

def getCGValue(reg, As):
    ret = 0
    if reg == 3:
        if As == 3:
            return -1
        else:
            return As
    else:
        return (As - 1)*4

"""
select case patterns for reference (msp430-gcc 4.6.3):
    MultiHopOscilloscopeLPL <Msp430Adc12ImplP__SingleChannel__getData>
    64b8:       7f 92           cmp.b   #8,     r15     ;r2 As==11   <-- limit (cmp) ?
    64ba:       4d 2c           jc      $+156           ;abs 0x6556
    64bc:       0e 4f           mov     r15,    r14     
    64be:       3e f0 0f 00     and     #15,    r14     ;#0x000f     <-- limit (and)
    64c2:       0e 5e           rla     r14                          <-- *2
    64c4:       5f 42 37 00     mov.b   &0x0037,r15     
    64c8:       10 4e f8 ac     br      -21256(r14)     ;0xacf8(r14) <-- branch
    
    MultiHopOscilloscopeLPL <VirtualizeTimerC__0__fireTimers>
    7012:       75 90 0c 00     cmp.b   #12,    r5      ;#0x000c     <-- limit (cmp)
    7016:       02 28           jnc     $+6             ;abs 0x701c
    7018:       30 40 72 72     br      #0x7272 
    701c:       4f 45           mov.b   r5,     r15     
    701e:       0f 5f           rla     r15                          <-- *2 
    7020:       10 4f 08 ad     br      -21240(r15)     ;0xad08(r15) <-- branch

    Blink <Msp430TimerP__1__Event__fired>
    46b4:       7f 92           cmp.b   #8,     r15     ;r2 As==11   <-- limit (cmp)
    46b6:       50 2c           jc      $+162           ;abs 0x4758
    46b8:       4f 4f           mov.b   r15,    r15     
    46ba:       0f 5f           rla     r15                          <-- *2
    46bc:       10 4f e8 49     br      18920(r15)      ;0x49e8(r15) <-- branch
    
    CountToLeds <SchedulerBasicP__TaskBasic__runTask>
    5bf4:       7f 90 0e 00     cmp.b   #14,    r15     ;#0x000e     <-- limit (cmp)
    5bf8:       02 28           jnc     $+6             ;abs 0x5bfe
    5bfa:       30 40 a8 63     br      #0x63a8 
    5bfe:       4f 4f           mov.b   r15,    r15     
    5c00:       0f 5f           rla     r15                          <-- *2
    5c02:       10 4f 8e 6c     br      27790(r15)      ;0x6c8e(r15) <-- branch
    ...
    5e0e:       7b 90 05 00     cmp.b   #5,     r11     ;#0x0005     <-- limit (cmp)
    5e12:       02 28           jnc     $+6             ;abs 0x5e18
    5e14:       30 40 a8 63     br      #0x63a8 
    5e18:       4f 4b           mov.b   r11,    r15                  <-- swap register
    5e1a:       0f 5f           rla     r15                          <-- *2
    5e1c:       10 4f aa 6c     br      27818(r15)      ;0x6caa(r15) <-- branch

    Glossy CC430 <radio_interrupt>
    9de0:       38 90 0d 00     cmp     #13,    r8      ;#0x000d     <-- limit (cmp)
    9de4:       d3 2c           jc      $+424           ;abs 0x9f8c
    9de6:       58 02           rlam    #1,     r8                   <-- *2
    9de8:       10 48 24 b0     br      -20444(r8)      ;0xb024(r8)  <-- branch
    
    Dozer <SchedulerBasicP__TaskBasic__runTask>
    a338:       f2 90 12 00     cmp.b   #18,    &0x1172 ;#0x0012     <-- limit (cmp)
    a33c:       72 11 
    a33e:       02 28           jnc     $+6             ;abs 0xa344
    a340:       30 40 4a a7     br      #0xa74a                      
    a344:       5f 42 72 11     mov.b   &0x1172,r15                  <-- copy to register
    a348:       0f 5f           rla     r15                          <-- *2
    a34a:       10 4f 30 c1     br      -16080(r15)     ;0xc130(r15) <-- branch

"""

def testSwitchPattern(insts):
    insts = list(insts)
    testreg = insts[-1].sreg # register that limits branch, could be different from brreg
    brreg   = insts[-1].sreg # register involved in branch instruction
    # test for reassignments
    for i in reversed(range(len(insts))):
        if insts[i].opcode == 0x4000 and insts[i].dreg == testreg and insts[i].As == 0 and insts[i].Ad == 0:
            #print "%x: testreg %d > %d" % (insts[i].addr, testreg, insts[i].sreg)
            testreg = insts[i].sreg
            break
        if insts[i].opcode == 0x4000 and insts[i].dreg == testreg and insts[i].As == 1 and insts[i].Ad == 0 and insts[i].sreg == 2:
            #print("%x: testreg %d > addr %x" % (insts[i].addr, testreg, insts[i].arg1))
            testreg = insts[i].arg1
            break
        if insts[i].opcode == 0x9000: # found compare
            break
    testval = None
    # look out for limiting value
    for i in range(len(insts)):
        #print '%x' % insts[i].arg0
        # try 'cmp' limit
        if insts[i].opcode == 0x9000 and (insts[i].dreg == testreg or testreg > 15 and insts[i].arg2 == testreg): # compare
            if insts[i].sreg==2 or insts[i].sreg==3: # constant generator 
                testval = getCGValue(insts[i].sreg, insts[i].As)
            else:
                testval = insts[i].arg1
            #print '%x: compare r%d to %d' % (insts[i].addr, testreg, testval)
            break
    if i + 1 >= len(insts):
        return None
    if (insts[i+1].opcode & 0x2800) != 0x2800:
        print("no jump %s" % insts[i+1])
        return None
        
    # times 2 rla or rlam
    for k in range(i+2,len(insts)-1):
        #print '%x' % insts[k].arg0
        if insts[k].opcode == 0x5000 and insts[k].dreg == brreg and insts[k].sreg == brreg:
            #print 'rla %s' % str(map(lambda x: insts[-1].arg1 + x * 2, xrange(0,testval-1)))
            return [insts[-1].arg1 + x * 2 for x in range(0,testval)]
        if insts[k].arg0 == (0x250 | testreg):
            #print 'rlam'
            return [insts[-1].arg1 + x * 2 for x in range(0,testval)]
    
    #print 'not times 2'
    return None
    
#def isPointer(prog, checkpath, dwarf):
    #"""
    #This is a very simple pointer check function. For serious work, it should be extended to find more cases.
    #For example it could extract the function template from debug information
    #"""
    #print('\ncheck %s' % (hexlist(checkpath)))
    #stack = [] # if value is put on stack, 1 for values to check, 0 for other values
    #regcheck = {} # if value is propagated, save the register number in here
    #if prog[checkpath[0]].opcode & 0xff00 == 0x1200:
        #stack.insert(0,1)
        ##print('%x: push %s' % (checkpath[0], stack))
    #elif prog[checkpath[0]].dreg > 3:
        #regcheck[prog[checkpath[0]].dreg]=True
    #else:
        #assert('isPointer: could not check for pointer')
    ##print('stack %s regs: %s'% (str(stack), str(list(regcheck.keys()))))
    #for addr in checkpath[1:]:
        #if prog[addr].isCall():
            #funaddr = prog[addr].directtarget
            #print('call %x' % funaddr)
            #ap = dwarf.getAddressParameters(funaddr)
            #if ap is None:
                #print('warning: missing debug information for function at %x' % funaddr)
                #return False
            #plocs, alllocs = ap
            #print(alllocs)
            ## check registers
            #if any(['r%d' % r in alllocs for r in regcheck.keys()]) or 1 in stack and 'fbreg + %d' % (stack.index(1)*2) in alllocs:
                #print(alllocs)
                #print(regcheck)
                #if any(['r%d' % r in plocs for r in regcheck.keys()]):
                    #print('isPointer: call to %x, value (in reg) at %x is pointer' % (funaddr, checkpath[0]))
                    #return True
                ## check stack
                #if 1 in stack and 'fbreg + %d' % (stack.index(1)*2) in plocs:
                    #print('isPointer: call to %x, value (on stack) at %x is pointer' % (funaddr, checkpath[0]))
                    #return True
                #print('isPointer: call to %x, value at %x is not a pointer' % (funaddr, checkpath[0]))
                #return False
        #else:
            ## 1) check for indexed mode, indirect register, indirect increment using a tracked value
            #if prog[addr].sreg in regcheck and prog[addr].As is not None and prog[addr].As > 0:
                #print('isPointer: memory access r%d: %s' % (prog[addr].sreg, prog[addr]))
                #return True
            ## 2) do transfer
            #if prog[addr].opcode & 0xff00 == 0x1200: # push
                #if prog[addr].sreg in regcheck.keys():
                    #stack.insert(0,1) # value from register to stack
                    
                #else:
                    #stack.insert(0,0)
                #print('%x: push %s' % (checkpath[0], stack))
            ## TODO ...
    #return False
    
    
def progToBytes(prog):
    startaddr = min(prog.keys())
    size = max(prog.keys()) - startaddr + prog[max(prog.keys())].size * 2
    buf = bytearray(size)
    for addr, inst in prog.items():
        buf[addr - startaddr:addr - startaddr + inst.size * 2] = inst.getBytes()
    return buf
   
# TODO: more efficient program mapping
#class ProgramMapping(object):
    
    #_orig = {}
    #_added = {}
    #_offsetsOld2New = {} # ordered list (oldaddr, offset)
    #_offsetsNew2Old = {} # ordered list (newaddr, offset)

    #def __init__(self, prog):
        #self._orig = prog
        
    #def old2NewAddr(self, oldaddr):
        #return oldaddr + sum([offset for addr, offset in self._offsetsOld2New.items() if addr <= oldaddr])
    
    #def new2OldAddr(self, newaddr):
        #return newaddr + sum([offset for addr, offset in self._offsetsNew2Old.items() if addr <= newaddr])
    
    #def getInsFromNewAddr(self, newaddr):
        #try:
            #return self._added[newaddr]
        #except KeyError:
            #return self._orig[self.new2OldAddr(newaddr)]
    
    #def getInsFromOldAddr(self, oldaddr):
        #return self._orig[oldaddr]
        
    #def insert(self, newaddr, ins):
        ## move down added instructions
        #offset = ins.size * 2
        #for addr in sorted([k for k in self._added.keys() if k >= newaddr], reverse = True):
            #self._added[addr + offset] = self._added.pop(addr)
        
        ## insert ins to added
        #self._added[newaddr] = ins
        
        ## update offsets
        #oldaddr_break = self.new2OldAddr(newaddr)
        #v = self._offsetsOld2New.setdefault(oldaddr_break, 0)
        #self._offsetsOld2New[oldaddr_break] = v + offset
            
        #for addr,offs in self._offsetsOld2New.items():
            #if addr >= oldaddr_break:
                #self._offsetsOld2New[addr] = offs + offset

        #for addr,offs in self._offsetsNew2Old.items():
            #if addr >= newaddr:
                #self._offsetsNew2Old[addr] = offs - offset
    
    #def getProg(self):

## main ########################################
def main():
    global TIME_METHOD, USE_UNIQUE_MARKERS, USE_CFG_UNIQUE_MARKERS, CPU_SPEED_ERROR, ALLOW_LOOPS_IN_TIMED, BOUNDFILE
    
    main_start_time = time.time()
    progname = sys.argv[0]
    u = 'usage: %prog objfile [list of entry points]'

    parser = optparse.OptionParser(usage = u)
    parser.add_option("-m", "--method", action="store", type="string", dest="TIME_METHOD")
    parser.add_option("-U", "--uniquemarkers", action="store_true", dest="USE_UNIQUE_MARKERS")
    parser.add_option("-u", "--nouniquemarkers", action="store_false", dest="USE_UNIQUE_MARKERS")
    parser.add_option("-C", "--cfguniquemarkers", action="store_true", dest="USE_CFG_UNIQUE_MARKERS")
    parser.add_option("-c", "--nocfguniquemarkers", action="store_false", dest="USE_CFG_UNIQUE_MARKERS")
    parser.add_option("-t", "--tolerance", action="store", type="float", dest="CPU_SPEED_ERROR")
    parser.add_option("-b", "--boundtrace", action="store", type="string", dest="BOUNDFILE")
    parser.add_option("-l", "--handleloops", action="store_true", dest="ALLOW_LOOPS_IN_TIMED", default=False)
    options, args = parser.parse_args()
    
    if len(sys.argv) == 1:
      parser.print_help()
      exit(1)
    
    if options.TIME_METHOD:
        if options.TIME_METHOD in ('none', 'reduction', 'none_and_reduction'):
            TIME_METHOD = options.TIME_METHOD
        else:
            print('unknown method %s' % options.TIME_METHOD)
            exit(1)
    
    if options.USE_UNIQUE_MARKERS is not None:
        USE_UNIQUE_MARKERS = options.USE_UNIQUE_MARKERS
    
    if options.USE_CFG_UNIQUE_MARKERS is not None:
        USE_CFG_UNIQUE_MARKERS = options.USE_CFG_UNIQUE_MARKERS
    
    # check config
    if USE_UNIQUE_MARKERS and USE_CFG_UNIQUE_MARKERS:
        print('specify either USE_UNIQUE_MARKERS or USE_CFG_UNIQUE_MARKERS')
        exit(1)
    if TIME_METHOD == 'none_and_reduction' and not(USE_UNIQUE_MARKERS or USE_CFG_UNIQUE_MARKERS):
        print('Method \'none_and_reduction\' requires either USE_UNIQUE_MARKERS or USE_CFG_UNIQUE_MARKERS')
        exit(1)
        
    if options.CPU_SPEED_ERROR is not None:
        CPU_SPEED_ERROR = options.CPU_SPEED_ERROR / 100
        #ALLOW_LOOPS_IN_TIMED = (CPU_SPEED_ERROR == 0)
        
    BOUNDFILE = options.BOUNDFILE
    ALLOW_LOOPS_IN_TIMED = options.ALLOW_LOOPS_IN_TIMED

    elffilename = args[0]
        
    entrypoints = [int(x, 16) for x in args[1:]]
    
    if elffilename == 'last':
        dolast = True
    else:
        dolast = False
    
    debugfiles = {'cycle_counts': True, 'basic_block_cycle_counts': True, 'marker_info': True, 'lookup_table': True, 'loop_bounds': True}
    
    if not dolast:
        print('========= parse elf file ================')
        elf = elffile.open(name=elffilename)
        for h in elf.sectionHeaders:
            print(h)
        for h in elf.programHeaders:
            print(h)
        
        prog = {}
        rodata = {}
        functg = []
        funcaddrs = []
        funccalls = []
        funcrets = []
        funcends = []
        jumptg = []
        jumpelse = []
        lpmpossible = [] # tuples containing potential lpm entry and exit (two consecutive instructions)
        elfaddrs = {}
        elfsections = {}
        elfsections_idx = {}
        
        for i,h in enumerate(elf.sectionHeaders):
            elfaddrs[h.name] = h.addr
            elfsections[h.name] = h
            elfsections_idx[h.name] = i
        
        h = elfsections[b'.rodata']
        for p in range(0,h.section_size, 2):
            d = struct.unpack('<H', h.content[p:p+2])
            rodata[p + h.addr] = d[0]

        # format of rela section:  32 bit addr r_offset; 32 bit r_info; 32 bit r_addend;
        # r_info: 24 bit symtable offset?, 8 bit type
        #Relainfo = namedtuple('Relainfo', ['offset', 'info_sym', 'info_type', 'addend'])
        rela_totext = [] # adresses pointing to .text, need to be adapted later (+variable offset)
        rela_torodata = [] # adresses pointing to .rodata, need to be adapted later (+delta)
        paddrs = list([h.paddr for h in elf.programHeaders])
        for s in (b'.text', b'.rodata', b'.data'):
            try:
                h = elfsections[b'.rela'+s]
            except KeyError:
                print("WARNING: could not find relocation table %s" % str(b'.rela'+s, 'utf-8'))
                continue
            for p in range(0,h.section_size, 12):
                r_offset, r_info, r_addend = struct.unpack('<3I', h.content[p:p+12])
                r_info_sym = r_info >> 8
                r_info_type = r_info & 0xff
                s_offset = r_info_sym * 16
                r_section = struct.unpack('<H',elfsections[b'.symtab'].content[s_offset+14:s_offset+16]) # section of symbol
                r_value = struct.unpack('<I',elfsections[b'.symtab'].content[s_offset+4:s_offset+8]) # address of symbol
                if r_section[0] == elfsections_idx[b'.text']:
                    #print('%x %x +%x, %x %d %d to .text' % (r_offset, r_info, r_addend, r_info_sym, r_info_type, r_section[0]))
                    rela_totext.append(r_offset)
                elif r_section[0] == elfsections_idx[b'.rodata'] or r_section[0] == ELF_SECTION_ABS and r_value[0] in paddrs:
                    #print('%x %x +%x, %x %d %d to .rodata' % (r_offset, r_info, r_addend, r_info_sym, r_info_type, r_section[0]))
                    rela_torodata.append(r_offset)
                #else:
                    #print('%x %x +%x, %x %d %d value %x' % (r_offset, r_info, r_addend, r_info_sym, r_info_type, r_section[0], r_value[0]))
        print('totext: %s' % hexlist(rela_totext))
        print('torodata: %s' % hexlist(rela_torodata))

        indcalls = []
        h = elfsections[b'.text']
        if debugfiles['cycle_counts']:
            ccfile = open('%s.cycles' % elffilename, 'w')
        text = h
        # print str(b[h.offset:h.offset+h.section_size]).encode('hex')
        text_end = text.addr + text.section_size
        text_start = text.addr
        skip = 0
        for p in range(0, text.section_size, 2):
            if skip == 0:
                instr = struct.unpack('<H', text.content[p:p+2])
                instr = op(instr[0])
                olen = instr.size
                fullinstr = struct.unpack('<%dH' % olen, text.content[p:p+2*olen])
                instr.arg0 = fullinstr[0]
                if olen > 1:
                    instr.arg1 = fullinstr[1]
                if olen > 2:
                    instr.arg2 = fullinstr[2]                        
                addr = p + text.addr
                instr.addr = addr
                instr.originaladdr = addr
                #print '%x: %d %s op %x' % (addr, olen, str(b[p:p+2*olen]).encode('hex'), instr.opcode)
                prog[addr]=instr
                if instr.isCondJmp():
                    #print 'cond jump'
                    jumptg.append(addr + instr.jumptg)
                    jumpelse.append(addr + instr.size * 2)
                elif instr.isJmp():
                    #print 'jump'
                    jumptg.extend(instr.targets())
                    jumpelse.append(addr + instr.size * 2)
                elif instr.isCall():
                    #print 'call 0x%x' % addr
                    try:
                        functg.extend(instr.targets())
                        if not instr.isIndCall():
                            funcaddrs.append(instr.arg1)
                        else:
                            indcalls.append(addr)
                        #print 'call 0x%x' % instr.arg1
                    except IndirectCallException:
                        print("%x: indirect call" % instr.addr)
                    funccalls.append(addr)
                    funcrets.append(addr + instr.size * 2)
                elif instr.isRet() or instr.isReti():
                    funcends.append(addr + instr.size * 2)
                elif instr.isIndJmp():
                    print('%x: indirect jump' % addr)
                    p_addrs = sorted(prog.keys())
                    tg = testSwitchPattern(prog[i] for i in p_addrs[-7:])
                    if not tg is None:
                        print('target adresses located at: %s' % hexlist(tg))
                        print(map(lambda x: '%x' % rodata[x], tg))
                        jumptg.extend([rodata[x] for x in tg])
                        instr.indtargets = list(set([rodata[x] for x in tg]))
                        instr.indroaddr = tg
                    else:
                        print("%x: indirect jump: could not match to template" % instr.addr)
                        for i in p_addrs[-6:]:
                            print(prog[i])
                else:
                    if instr.dreg == 0 and instr.Ad == 0:
                        print('%x: modify PC' % instr.addr)
                if instr.isWriteToSr():
                    print('%x: write to SR' % instr.addr)
                    lpmpossible.append((instr.addr, instr.addr + instr.size * 2))
                instr.updateDirectTarget()
                if debugfiles['cycle_counts']:
                    c,d = instr.cycleCountDbg()
                    print('%d %x %s' % (c, instr.addr,d), file=ccfile)
                #print instr.cycleCount()
                skip = olen - 1
                
            else:
                skip = skip - 1
        if debugfiles['cycle_counts']:
            ccfile.close()
               
        h=elfsections[b'.vectors']
        vectors = list(struct.unpack('<%dH' % (h.section_size / 2), h.content[0:h.section_size]))
       
        strtab = bytes(elfsections[b'.strtab'].content)

        symtab = {}
        h = elfsections[b'.symtab']
        for offset in range(0, h.section_size, 16):
            st_name, st_value, st_size, st_info, st_other, st_shndx = struct.unpack('<IIIBBH', h.content[offset:offset+16])
            #print('%d: %x, %x, %x, %x, %x, %x, %s' % (offset / 16, st_name, st_value, st_size, st_info, st_other, st_shndx, strtab[st_name:st_name+strtab[st_name+1:].index(b'\x00')+1]))
            if st_shndx in (elfsections_idx[name] for name in (b'.rodata', b'.text')) and st_value in prog:
                prog[st_value].symtabptr.append(offset)
                symtab[st_value] = strtab[st_name:st_name+strtab[st_name+1:].index(b'\x00')+1]
                #print(list(['%x' % x for x in struct.unpack('<IIIBBH', h.content[offset:offset+16])]))

        for i in indcalls:
            maxaddr = 0
            for funaddr in symtab.keys():
                if funaddr < i and funaddr > maxaddr:
                    maxaddr = funaddr
            if maxaddr > 0 and maxaddr in symtab:
                print("%x: indirect call in <%s>" % (i, symtab[maxaddr].decode('utf-8')))
            else:
                print("%x: indirect call" % i)
                
        #print prog
        #print set(jumptg).union(set(jumpelse))
        #print funccalls
        #print funcrets
        #print map(lambda x: '%x' %x, sorted(funcends))
        #print map(lambda x: '%x' %x, sorted(jumptg))
        #print map(lambda x: '%x' %x, sorted(jumpelse))
        #print set(functg)    
        #print 'funcaddrs: %s' % hexlist(sorted(funcaddrs))
        #print 'vectors: %s' % hexlist(sorted(vectors))
        #################################################
        print('========= generate basic blocks =========')
        # generate basic blocks
        #bbleader = set([text_start]).union(set(jumptg).union(set(jumpelse)).union(set(funcrets)).union(set(functg))).union(set(funcends))
        bbleader = set(vectors).union(set([text_start])).union(set(jumptg)).union(set(jumpelse)).union(set(funcends)).union(set(functg)).union(set([i[1] for i in lpmpossible]))
        bbstarts = sorted(list(bbleader.difference(set([text_end]))))
        bbends = sorted(list(set(bbstarts[1:]).union(set([text_end]))))
        
        bbs = {}
        progkeys = set(prog.keys())
        for start,end in zip(bbstarts, bbends):
            #insts = filter(lambda x: x >= start and x < end, progkeys)
            insts = set(range(start,end,2)).intersection(progkeys)
            #print '%x-%x %s' % (start,end,str(insts))
            endinst = max(insts)
            bb = BasicBlock(start, endinst, prog[endinst].size)
            for i in insts:
                prog[i].inbb = start
            if not (prog[endinst].isRet() or prog[endinst].isReti()):
                bb.isCall = prog[endinst].isCall()
                bb.isIndirectCall = prog[endinst].isCall() and prog[endinst].isIndCall()
                bb.callTarget = prog[endinst].arg1
                try:
                    bb.setSuccessors(prog[endinst].targets())
                except IndirectCallException:
                    pass
            #print "%x %x %s %d" % (start, endinst, map(lambda x:"%x" % x, bb.successors), len(insts))
            bb.cycles = sum([prog[addr].cycleCount() for addr in insts])
            #print bb.cycles
            bbs[bb.start]=bb
        referenced_bb = set(sum([b.successors for b in list(bbs.values())],[]))
        unreferenced_bb = set([b.start for b in list(bbs.values())]).difference(referenced_bb).difference(set(vectors)).difference(set(funcaddrs))
        if len(unreferenced_bb) > 0:
            print('There are %d unreferenced entry nodes:' % len(unreferenced_bb))
            for addr,name in sorted([(x, symtab[x].decode('utf-8')) for x in unreferenced_bb if x in symtab], key=operator.itemgetter(1)):
                print('%x <%s>' % (addr, name))
            for addr in sorted([x for x in unreferenced_bb if x not in symtab]):
                print('%x <UNKNOWN FUNCTION>' % (addr))

        indirect_call_functions = []
        indirect_call_functions.extend(unreferenced_bb)
        indirect_call_functions.extend([x for x in set(funcaddrs) if symtab[x].decode('utf-8') in INDIRECT_CALL_NAMES])
        print('List of functions that can be called indirectly: %s' % hexlist(indirect_call_functions))
        # add ret BBs for all functions
        funcaddrs.extend(indirect_call_functions)
        funcendbbs = {}
        for addr,bb in bbs.items():
            if prog[bb.end].isRet() or prog[bb.end].isReti():
                funendbbaddr = max([x for x in set(funcaddrs).union(set(vectors)) if x < bb.end]) + 1 # use fake address for exit node of function
                bb.setSuccessors([funendbbaddr])
                funcendbbs[funendbbaddr] = BasicBlock(funendbbaddr, funendbbaddr, 0)
        bbs.update(funcendbbs)
        bbcount = len([a for a in bbs.keys() if a % 2 == 0])
        funcount = len(set(funcaddrs).union(set(vectors)))
        print(hexlist(sorted(list(set(funcaddrs).union(set(vectors))))))
        inscount = len(prog.keys())
        
        #print('========= Check for pointer constants ====')
        #immediatepointers = []
        #dwarf = Msp430Dwarf(elffilename)
        #for addr,instr in prog.items():
            #if instr.isCall():
                #continue
            #if instr.size > 1 and (instr.As==3 or instr.Ad==3) and instr.sreg not in [2,3]:
                #if int(instr.arg1 / 2) * 2 in set(rodata.keys()).union(set(funcaddrs)):
                    #thisbb = bbs[instr.inbb]
                    #print('pointer check %s %x-%x' % (instr, addr, thisbb.end))
                    #checkpath = sorted([a for a in prog.keys() if a >=addr and a <= thisbb.end])
                    #while len(thisbb.successors) == 1:
                        #suc = thisbb.successors[0]
                        #checkpath = checkpath + sorted([a for a in prog.keys() if a >= bbs[suc].start and a <= bbs[suc].end])
                        #thisbb = bbs[suc]
                    #for suc in thisbb.successors:
                        #if isPointer(prog, checkpath + sorted([a for a in prog.keys() if a >= bbs[suc].start and a <= bbs[suc].end]), dwarf):
                            #immediatepointers.append(addr)
        #print('Memory references found at %s' % hexlist(immediatepointers))
        #exit()

        #################################################
        # calculate spanning tree
        print('========= create control flow graphs ====')
        cfgs = {}
        if len(entrypoints)==0: # if not given by user
            entrypoints = set(funcaddrs).union(set(vectors))
        for entry in entrypoints:
            cfg = ControlFlowGraph(entry, bbs, symtab[entry])
            cfgs[entry] = cfg
                        
        if True:
            print('========= calculate marker positions ====')
            treenum = 0
            tgnum = 0
            callswithmarkers = [g.entry for g in list(cfgs.values())] # all calls
            markers = {}
            if BOUNDFILE is not None:
                bounddb = TraceBounds(BOUNDFILE)
            else:
                bounddb = None

            print('non-trivial calls: %s' % hexlist(callswithmarkers))
            # for i in [0x851a]:
            m = 1
            for i in list(cfgs.keys()):
                if (not USE_UNIQUE_MARKERS) or USE_CFG_UNIQUE_MARKERS:
                    m = 1
                cfgs[i].addBlockingMarkersAtPredicates(callswithmarkers) # "required" for function call transitions
                cfgs[i].addBlockingMarkersLPM(lpmpossible)
                cfgs[i].blocking_functions_and_lpm = copy.copy(cfgs[i].blocking) # needed to restore later for 'none_and_reduction' method
                cfgs[i].spanningtrees()
                nontreeedges = set(cfgs[i].edges).difference(cfgs[i].tree)
                
                # v- Constructive approach
                if TIME_METHOD == 'timegraph':
                    # 1. Convert simple cycles to *-nodesset(funcaddrs).union(set(vectors))
                    # 2. Remove all directed cycles (feedback arcs) by selecting edges from trees
                    # 3. Separate *-nodes
                    cfgs[i].simplecycles()
                    # 5. Create time graph
                    # 6. Minimal spanning tree on time graph
                    cfgs[i].timegraph()
                # ^-
                
                # v- Destructive approach
                if TIME_METHOD == 'reduction':
                    cfgs[i].setReduceParameters(CPU_SPEED_ERROR, ALLOW_LOOPS_IN_TIMED, bounddb)
                    cfgs[i].reduceMarkers(True)
                # ^-

                # v- no time approach
                if TIME_METHOD == 'none' or  TIME_METHOD == 'none_and_reduction':
                    # add all existing markers to blocking set
                    cfgs[i].blocking = list(set(cfgs[i].blocking).union(nontreeedges))
                    cfgs[i].reduceMarkers(True)
                # ^-

                
                print('%d markers in %x' % (len(set(cfgs[i].blocking).union(set(cfgs[i].blockcycles)).union(set(cfgs[i].blockstar)).union(set(cfgs[i].tg_break))), cfgs[i].entry))
                #colortree(cfgs[i].tree, set(cfgs[i].edges).difference(set(cfgs[i].tree)))
                #cfgs[i].explorePathLengths(10)
                testedges = set(cfgs[i].blocking).union(set(cfgs[i].blockcycles)).union(set(cfgs[i].tg_break))
                print('markers: %x tg: %d, tree %d, in tg not in tree %d, <%s> ' % (cfgs[i].entry, len(testedges.union(set(cfgs[i].blockstar))), len(nontreeedges.union(set(cfgs[i].blocking))), len(testedges.difference(nontreeedges)), cfgs[i].name))
                treenum += len(nontreeedges.union(set(cfgs[i].blocking)))
                tgnum += len(testedges.union(set(cfgs[i].blockstar)))
                cfgs[i].markerColoring()
                m,markers[i] =cfgs[i].getMarkers(m)
                print(m)
                print("--\n")
            
            print('overall markers: tg %d, tree %d, %0.2f%%, %d blocking' % (tgnum, treenum, float(tgnum) / float(treenum) * 100, sum([len(cfg.blocking) for cfg in list(cfgs.values())])))
            blocks = sum([cfg.blocking for cfg in list(cfgs.values())], [])
            blocks = sum([cfg.blockcycles for cfg in list(cfgs.values())], blocks)
            blocks = sum([cfg.blockstar for cfg in list(cfgs.values())], blocks)
            blocks = sum([cfg.tg_break for cfg in list(cfgs.values())], blocks)
            treeedges =  sum([cfg.tree for cfg in list(cfgs.values())], [])
            nextmarkerid = m
                       
            # add interrupt markers
            m = 1
            for irqaddr in set(vectors):
                if not irqaddr in markers:
                    markers[irqaddr] = []
                markers[irqaddr].append(IrqMarker(irqaddr, None, irqaddr, m, True))
                m = m + 1
            # add indirect call markers
            m = 1
            for funaddr in set(indirect_call_functions):
                if not funaddr in markers:
                    markers[funaddr] = []
                markers[funaddr].append(IndirectCallMarker(funaddr, None, funaddr, m, True))
                print('add indirect call marker %d %x' % (m, funaddr))
                m = m + 1

            # write CFG information for visualization: Original CFG and 1st pass marker edges
            vertices = []
            f = open('vis/data.js','w')
            f.write('var links = [\n')
            #for bb in sum([c.bbs.values() for c in cfgs.values() if c.entry==0x5be4],[]):
            for bb in list(bbs.values()):
                if bb.start in prog and bb.end in prog:
                    #print '%x - %x: %x op %x %s' % (prog[bb.start].addr, prog[bb.end].addr, prog[bb.end].arg0, prog[bb.end].opcode, map(lambda x:'%x' % x, bb.successors))
                    pass
                if not bb.end in prog:
                    ltype = 'end'
                elif prog[bb.end].isJmp():
                    ltype = 'jump'
                elif prog[bb.end].isCondJmp():
                    ltype = 'conditionaljump'
                elif prog[bb.end].isIndJmp():
                    ltype = 'indirectjump'
                elif prog[bb.end].isCall():
                    ltype = 'call'        
                elif prog[bb.end].isRet() or prog[bb.end].isReti():
                    ltype = 'jump'
                else:
                    ltype = 'jump' # fall through
                #print ltype
                for s in bb.successors:     
                    f.write('{source: "%x", target:"%x", type: "%s", istree: %d},\n' % (bb.start, s, ltype, (bb.start, s) not in blocks))
                    if not bb.start in vertices:
                        vertices.append(bb.start)
                    if not s in vertices:
                        vertices.append(s)
                    
            f.write('];\n')
            f.write('var nodes = {\n')
            for fun in set(funcaddrs):
                if fun in indirect_call_functions:
                    f.write('"%x": {name: "%x", type: "function_entry", isIndirectCall: true},\n' % (fun,fun))
                else:
                    f.write('"%x": {name: "%x", type: "function_entry", isIndirectCall: false},\n' % (fun,fun))
                if (fun+1) in vertices:
                    f.write('"%x": {name: "%x", type: "function_exit"},\n' % (fun+1,fun+1))
            for fun in set(vectors):
                f.write('"%x": {name: "%x", type: "interrupt_entry"},\n' % (fun,fun))
                if (fun+1) in vertices:
                    f.write('"%x": {name: "%x", type: "interrupt_exit"},\n' % (fun+1,fun+1))
            f.write('};\n')
            f.close()
            
    if True:
        print('========= add instrumentation ====')
        if USE_UNIQUE_MARKERS:
            enc = GPIOEncoding(int(sum([len(m) for m in markers.values()]) * 1.2), 5)
        else:
            enc = GPIOEncoding(int(max([M.id for m in markers.values() for M in m]) * 1.2), 5)
        # DEBUG
        #lower_ch_bound = 0 # nok:7a20, 0x7f1a, 0x7f7e, 0x8060 # ok: 0xa264, 0x9d72, 0x8464, 0x8342
        #for i in cfgs.keys():
            ###if (i < lower_ch_bound or i == 0x5a3c or i == 0x50d2 or i == 0x5092 or i == 0x503c or i == 0x5022):
            #if i <  lower_ch_bound:
                #markers[i] = []
        # DEBUG

        print('<pickle>')
        if dolast:
            with open('_last', 'rb') as PickleFile:
                prog, funcaddrs, vectors, jumptg, rodata, markers, elf, text, elffilename, elfaddrs, cfgs = pickle.load(PickleFile)
        else:
            with open('_last', 'wb') as PickleFile:
                p = pickle.Pickler(PickleFile)
                p.dump((prog, funcaddrs, vectors, jumptg, rodata, markers, elf, text, elffilename, elfaddrs, cfgs, bbs))
        shutil.copy('_last', '%s.pickle' % elffilename)
        original_vectors = vectors
        print('<add markers>')
        
        newmarkers = None
        tg_pass = 0

        # ----- entry point for second pass time graph
        while True:
            tg_pass = tg_pass + 1
            print('<add markers pass %d>' % tg_pass)
            tg_breaks = {k: cfgs[k].tg_break for k in cfgs.keys()} # remember last tg_break markers
            with open('_last', 'rb') as PickleFile:
                up = pickle.Unpickler(PickleFile)
                prog, funcaddrs, vectors, jumptg, rodata, markers, elf, text, elffilename, elfaddrs, cfgs, bbs = up.load()
            if not newmarkers is None:
                markers = newmarkers
            for i in cfgs.keys(): # restore last tg_break markers for next reduction step
                cfgs[i].tg_break = tg_breaks[i]
            #markeropt = [0,1,2,4,8]
            #for i in filter(lambda x: x not in markeropt, xrange(32)):
                #markeropt.append(i)
            """
            XOR might be harmfull because it alters status register:
            
            """
            # add instrumentation ###########################        
            # based on list of markers
            # keep old and new structures in order:
            # prog: dict { addr -> instruction }
            # 
            # adresses: newprog
            # targets: dict { target address -> list of instructions <Instruction> / jumptables<(Instruction, List)> / interrupt vectors <int> that point to this address }
            # oldtonewprog: dict { address in old prog -> address in new prog }
            # newrealentry: dict { address in old prog -> original address in new prog }
            addinscount = 0
            addinsrelabsjmpcount = 0
            newprog = copy.deepcopy(prog)
            oldtonewprog = {}
            newtooldprog = {}
            newrealentry = {}
            for addr in list(prog.keys()):
                oldtonewprog[addr] = addr
                newtooldprog[addr] = addr
            #pmap = ProgramMapping(prog)
            
            print('<compile target dictionary>')
            targets = {}
            for a,i in newprog.items():
                # function calls
                if i.isCall() and i.directtarget in funcaddrs:
                    try:
                        t = targets[i.directtarget]
                    except KeyError:
                        t = []
                        targets[i.directtarget] = t
                    t.append(i)
                # jumps
                if i.isJmp() or i.isCondJmp():
                    for ta in i.branchTargets():
                        if not ta in jumptg:
                            continue
                        try:
                            t = targets[ta]
                        except KeyError:
                            t = []
                            targets[ta] = t
                        t.append(i)
                # indirect branches
                if i.isIndJmp():
                    for ta in i.targets():
                        try:
                            t = targets[ta]
                        except KeyError:
                            t = []
                            targets[ta] = t
                        t.append((i, [ra for ra in i.indroaddr if rodata[ra] == ta]))
            for i,a in enumerate(vectors):
                if not a in targets:
                    targets[a] = []
                targets[a].append(i)

            addedmarkers = {} # dict address -> marker
            longenc = 0
            savesrenc = 0
            m_portout = 0x0035 # P6
            m_portdir = 0x0036
            num_marker_inst = 0
            all_marker_size = 0
            #m_portout = 0x0031 # P5
            #m_portdir = 0x0032
        
            # -- start of add marker loop
            for marker in list(itertools.chain(*list(markers.values()))):
                try:
                    amlist = addedmarkers[marker.address]
                except KeyError:
                    amlist = []
                    addedmarkers[marker.address] = amlist
                if marker in amlist:
                    continue
                amlist.append(marker)
                print('add instrumentation at %x' % (marker.address))
                print(amlist)
                t = [0,0,0,0,0,0,0]
                t[0] = time.time()
                #mid = markeropt[marker.id]
                mid = marker.id
                newinst = []
                if isinstance(marker, IrqMarker):
                    if marker.address == vectors[-1]: # set port 6 pins to output
                        newinst.append(IMovImmAddr(0xc7, m_portdir))
                    newinst.append(IXorImmAddr(-1, m_portout)) # emit -1            
                    """
                    emit SR information from stack
                    SR: [15:9 reserved][8:V][7:SCG1][6:SCG2][5:OSCOFF][4:CPUOFF][3:GIE][2:N][1:Z][0:C]
                    P6:                     [LED1   , LED2 ]                           [LED3,INT2,INT1]
                    mov.b 0(SP), P6    2 words, 5 cycles
                    rra P6             2 words, 4 cycles
                    rra P6             2 words, 4 cycles
                                    6       13
                    or
                    push r4            1 word,  3 cycles
                    mov.b 1(SP), r4    2 words, 3 cycles
                    pop r4             1 word,  2 cycles
                    rra r4             1 word,  1 cycle
                    rra r4             1 word,  1 cycle
                    mov r4, P6         2 words, 4 cycles
                                    8       14
                    or
                    bit #0x10, 0(SP)   3 words, 5 cycles
                    xor.b SR, P6       2 words, 4 cycles    (CPUOFF: .. 01b not CPUOFF: .. 10b)
                                    5        9
                    """
                    newinst.append(IBitImmOfsReg(0x10, 0, 1))  # bit #0x10, 0(SP)
                    newinst.append(IXorRegAddr(2, m_portout))  # mov-b SR, P6

                code = enc.encode(mid)
                if len(code) > 1:
                    longenc = longenc + 1
                    print("long marker %d instructions" % len(code))
                for c in code:
                    newinst.append(IXorImmAddr((c & 0x7) | ((c & 0xf8) << 3), m_portout))
                if marker.targetAddress in prog and prog[marker.targetAddress].usesSr():
                    i = prog[marker.targetAddress]
                    print("remember status register for instruction %s" % str(i))
                    #print('%x %s %s %s' % (i.opcode, str(i.sreg), str(i.As), str(i.Ad)))
                    newinst.insert(0,IPushSr())
                    newinst.append(IPopSr())
                    savesrenc = savesrenc + 1
                
                offset = sum([i.size for i in newinst]) * 2
                insaddr = oldtonewprog[marker.address]
                #update marker cycles
                marker.cycles = sum([i.cycleCount() for i in newinst])
                if marker.needJmp:                
                    newinst[:0] = [Instruction(0x3c00, 0, 0, 0, 0, 1)] # unconditional jump
                    offset+=newinst[0].size * 2
                    if marker.address not in newrealentry:
                        newrealentry[marker.address] = insaddr
                    newinst[0].arg0 = 0x3c00 | ((((newrealentry[marker.address] - insaddr + offset) >> 1) - 1) & 0x03ff)               
                t[0] = time.time() - t[0]
                t[1] = time.time()
                
                all_marker_size+=sum([i.size for i in newinst])*2
                
                # move all following instructions down by offset
                breakaddr = oldtonewprog[marker.address]
                chlist = sorted([k for k in newprog.keys() if k >= breakaddr], reverse=True)
                t[1] = time.time() - t[1]
                t[2] = time.time()
                for addr in chlist:
                    #if addr < breakaddr:
                        #break
                    # adresses
                    newprog[addr + offset] = newprog[addr]
                    newprog[addr + offset].addr = addr + offset
                    del(newprog[addr])
                    try:
                        oldtonewprog[newtooldprog[addr]] = addr + offset
                        newtooldprog[addr + offset] = newtooldprog[addr]
                        del(newtooldprog[addr])
                    except KeyError:
                        pass
                    #if addr in newtooldprog:
                        #oldtonewprog[newtooldprog[addr]] = addr + offset
                        #newtooldprog[addr + offset] = newtooldprog[addr]
                        #del(newtooldprog[addr])
                t[2] = time.time() - t[2]
                t[3] = time.time()

                for addr in reversed(sorted(newrealentry.keys())):
                    if addr < marker.address:
                        break
                    newrealentry[addr] += offset
                t[3] = time.time() - t[3]
                t[4] = time.time()
                    
                # add new instruction(s)
                offset = 0
                for i in newinst:
                    newprog[insaddr + offset] = i
                    newprog[insaddr + offset].addr = insaddr + offset
                    offset += i.size * 2
                    addinscount = addinscount + 1
                    #pmap.insert(insaddr + offset, i)
                t[4] = time.time() - t[4]
                t[5] = time.time()
                # set new target
                if marker.targetAtInstrumentation:
                    newprog[insaddr].inbb = prog[marker.address].inbb
                    newprog[insaddr].symtabptr = prog[marker.address].symtabptr
                    newprog[insaddr + offset].symtabptr = []
                    oldtonewprog[marker.address] = insaddr
                    newtooldprog[insaddr] = marker.address
                    del(newtooldprog[insaddr + offset])
                t[5] = time.time() - t[5]
                t[6] = time.time()
                # adapt jump instruction target if needed
                if marker.needJmp:
                    # add mapping of newly added code at pseudo address
                    oldtonewprog[-addinscount] = insaddr + newinst[0].size * 2
                    newtooldprog[insaddr + newinst[0].size * 2] = -addinscount
                    # set bb for marker instruction
                    assert(newprog[insaddr + newinst[0].size * 2].inbb == None)
                    newprog[insaddr + newinst[0].size * 2].inbb = prog[marker.targetAddress].inbb
                    # move target
                    #print '%x' %marker.address
                    targets[-addinscount] = []
                    for i in targets[marker.address]:
                        # jumps
                        if isinstance(i,Instruction) and i.addr in newtooldprog and newtooldprog[i.addr]==marker.needJmp:
                            #print 'move jump %s' % str(i)
                            targets[-addinscount].append(i)
                        # indirect jumps
                        elif isinstance(i,tuple) and i[0].addr in newtooldprog and newtooldprog[i[0].addr]==marker.needJmp:
                            #print 'move indirect jump %s' % str(i)
                            targets[-addinscount].append(i)
                    #targets[-addinscount]=list([i for i in targets[marker.address] if isinstance(i,Instruction) and i.addr in newtooldprog and newtooldprog[i.addr]==marker.needJmp])               
                    #print 'moved targets: %s' % targets[-addinscount]
                    #print 'm1 %s' % str(targets[marker.address])
                    for i in targets[-addinscount]:
                        targets[marker.address].remove(i)
                    #print 'm2 %s' % str(targets[marker.address])
                t[6] = time.time() - t[6]
                t.append(marker.address)
                #print(t)
            # -- end of add marker loop
            
            # update basic blocks for marker effects
            for am in addedmarkers.values():
                mems = list([a for a in am if a.needJmp]) # multiple entry marker
                ants = list([a for a in am if a.address != a.targetAddress ])# adress not target addresses
                assert(len(ants)<2)
                if len(mems) > 0: # multiple entry marker (it is also possible that there are other markers in there, e.g. fall through markers)
                    # latent cycles
                    print('multiple entry marker: latent %d %s' % (-IJmp(0).cycleCount(), str(mems[0])))
                    mems[0].latentCycles = -IJmp(0).cycleCount()
                    # basic block: next block is longer
                    print(' update bb %x: %d -> %d' % (mems[0].targetAddress, bbs[mems[0].targetAddress].cycles, bbs[mems[0].targetAddress].cycles + IJmp(0).cycleCount()))
                    bbs[mems[0].targetAddress].cycles += IJmp(0).cycleCount()
                #elif len(am) == 1 and am[0].address != am[0].targetAddress: # jump exit marker / ret marker
                if len(ants) == 1: # jump exit marker / ret marker
                    print('jump / ret marker: latent %d %s, bb %x, target has %d cycles' % (prog[ants[0].address].cycleCount(), str(ants[0]), prog[ants[0].address].inbb, bbs[ants[0].targetAddress].cycles))
                    ants[0].latentCycles = prog[ants[0].address].cycleCount()
                    # basic block: this block is shorter
                    bbs[prog[ants[0].address].inbb].cycles -= prog[ants[0].address].cycleCount()
            
            # targets: calls, interrupts, jumps
            # replace relative jumps with branches if needed
            changes = 1
            while changes > 0:
                changes = 0
                for addr,insts in targets.items():
                    for i in insts:
                        if isinstance(i,Instruction):
                            newaddr = oldtonewprog[addr]
                            offset = 0
                            newinst = []
                            if i.isJmp():
                                if abs(i.addr - newaddr) > 509 and i.size == 1:
                                    print('jump too far @%x: %x -> %x %s' % (i.addr, addr, newaddr, str(i)))
                                    coffset = - i.cycleCount()
                                    # convert to branch
                                    i.opcode, i.arg0, i.arg1, i.dreg, i.sreg, i.size, i.As, i.Ad, i.modified = 0x4000, 0x4030, 0x0, 0, 0, 2, 3, 0, True
                                    # move down instructions                                
                                    offset = 2
                                    position = i.addr
                                    coffset += i.cycleCount()
                                    print('update cycle count: %x %d->%d' % (i.inbb, bbs[i.inbb].cycles, bbs[i.inbb].cycles + coffset))
                                    bbs[i.inbb].cycles += coffset # update jmp bb
                            elif i.isCondJmp():
                                if abs(i.addr - newaddr) > 509 and i.size == 1:
                                    print('condjump too far @%x (originally @%x): %x -> %x' % (i.addr, newtooldprog[i.addr], addr, newaddr))
                                    """
                                    here we add something like this:
                                    1 jmp $+6
                                    2 br <newaddr>
                                    3 j[n]c $-2
                                    bb cycle update: jmp bb: 1
                                                    target: 2
                                    if the destination can be reached from several places either
                                    a) all places need to be adapted
                                    or
                                    b) the fall through path in the source block needs a nop to equalize the cycle counts
                                    1 jmp $+6
                                    2 br <newaddr>
                                    3 j[n]c $-2
                                    4 nop (3 cycles, e.g. 1 nop, 1 jump +2)
                                    or
                                    c) we add an additional basic block containing only the branch instruction
                                    a) and b) introduce additional overhead, probably c) would be the best solution
                                    """
                                    position = i.addr
                                    br = IBr(newaddr)
                                    jc = copy.deepcopy(i)
                                    # instruction i (cond jump) becomes absolute branch, therefore it is later on handeled as an absolute jump to newaddr
                                    i.opcode, i.arg0, i.arg1, i.dreg, i.sreg, i.size, i.As, i.Ad, i.modified = br.opcode, br.arg0, br.arg1, br.dreg, br.sreg, br.size, br.As, br.Ad, True
                                    newinst = [IJmp(i.size), i, jc]
                                    offset = sum([ni.size for ni in newinst[:-1]]) * 2
                                    newinst[-1].setCondJmpTarget(newinst[-1].addr - sum([si.size for si in newinst[-2:-1]]) * 2)
                                    niaddr = i.addr
                                    for ni in newinst:
                                        ni.addr = niaddr
                                        niaddr = niaddr + ni.size * 2   
                                    addinsrelabsjmpcount = addinsrelabsjmpcount + len(newinst) - 1
                                    #print('update cycle counts: 1) %x %d->%d, 2) %x %d->%d' %(jc.inbb, bbs[jc.inbb].cycles, bbs[jc.inbb].cycles + newinst[0].cycleCount(), newprog[newaddr].inbb, bbs[newprog[newaddr].inbb].cycles, bbs[newprog[newaddr].inbb].cycles + newinst[1].cycleCount()) )
                                    print('update cycle counts: 1) %x %d->%d' %(jc.inbb, bbs[jc.inbb].cycles, bbs[jc.inbb].cycles + newinst[0].cycleCount()) )
                                    bbs[jc.inbb].cycles += newinst[0].cycleCount() # update jmp bb
                                    # bbs[newprog[newaddr].inbb].cycles += newinst[1].cycleCount() # update target bb, not needed for c)
                                    # add new bb
                                    fakeaddress = jc.inbb + FAKEADDRESS_OFFSET
                                    newbb = BasicBlock(fakeaddress,fakeaddress,br.size)
                                    newbb.cycles = br.cycleCount()
                                    newbb.incfg = bbs[newprog[newaddr].inbb].incfg
                                    # add bb to cfg
                                    assert (not (fakeaddress) in cfgs[newbb.incfg].bbs), 'new bb %x in cfg %x already taken by %s' % (fakeaddress, newbb.incfg, str(cfgs[newbb.incfg].bbs[fakeaddress]))
                                    assert (not (fakeaddress) in bbs)
                                    cfgs[newbb.incfg].addVertex(newbb)
                                    bbs[fakeaddress] = newbb
                                    # update cfg structure
                                    # old: jc.inbb (-a>) newprog[newaddr].inbb
                                    # new: jc.inbb (-b>) fakeaddress (-c>) newprog[newaddr].inbb
                                    # markers on (-a>) go to (-c>)
                                    w,t = cfgs[newbb.incfg].removeEdge((jc.inbb,newprog[newaddr].inbb))
                                    cfgs[newbb.incfg].addEdge((jc.inbb,fakeaddress), w, True)
                                    cfgs[newbb.incfg].addEdge((fakeaddress,newprog[newaddr].inbb), w, t)
                                    for b in (cfgs[newbb.incfg].blocking, cfgs[newbb.incfg].blocking_functions_and_lpm, cfgs[newbb.incfg].blockcycles, cfgs[newbb.incfg].blockstar, cfgs[newbb.incfg].tg_break):
                                        try:
                                            b.remove((jc.inbb, newprog[newaddr].inbb))
                                            b.append((fakeaddress, newprog[newaddr].inbb))
                                            print('update blocking edge from %x->%x to %x->%x' % (jc.inbb, newprog[newaddr].inbb, fakeaddress, newprog[newaddr].inbb))
                                        except ValueError:
                                            pass
                                    # update markers
                                    # marker from jump block to jump target: sourceAddress
                                    cm = [m for m in markers[bbs[jc.inbb].incfg] if m.sourceAddress == jc.inbb and m.targetAddress == newprog[newaddr].inbb]
                                    for m in cm:
                                        print('update marker source address: %s, source address: %x -> %x' % (str(m), m.sourceAddress, fakeaddress))
                                        m.sourceAddress = fakeaddress
                            if offset > 0: # move down following instructions by offset
                                for maddr in reversed(sorted(newprog.keys())):
                                    if maddr <= position:
                                        break
                                    # adresses
                                    newprog[maddr + offset] = newprog[maddr]
                                    newprog[maddr + offset].addr = maddr + offset
                                    del(newprog[maddr])
                                    if maddr in newtooldprog:
                                        oldtonewprog[newtooldprog[maddr]] = maddr + offset
                                        newtooldprog[maddr + offset] = newtooldprog[maddr]
                                        del(newtooldprog[maddr])
                                for maddr in reversed(sorted(newrealentry.keys())):
                                    if maddr <= position:
                                        break
                                    newrealentry[maddr] += offset
                                for ni in newinst:
                                    newprog[ni.addr] = ni
                                changes = changes + 1                            
            
            # adapt targets
            for addr,insts in targets.items():
                newaddr = oldtonewprog[addr]
                if newaddr != addr:
                    for i in insts:
                        if isinstance(i,int): # vector
                            #print 'target vector %d %x' % (i, newaddr)
                            vectors[i] = newaddr
                        elif isinstance(i,Instruction):
                            if i.isCall():
                                #print 'target call @%x: %x -> %x' % (i.addr, addr, newaddr)
                                i.setCallTarget(newaddr)
                            if i.isJmp():
                                #print('target jmp @%x: %x -> %x' % (i.addr, addr, newaddr))
                                i.setJmpTarget(newaddr)
                            if i.isCondJmp():
                                #print('target condjmp @%x (%x): %x -> %x' % (i.addr, newtooldprog[i.addr], addr, newaddr))
                                i.setCondJmpTarget(newaddr)
                        elif isinstance(i,tuple):
                            if i[0].isIndJmp():
                                # update rodata
                                for ofs in i[1]:
                                    #print 'ind %s %d' % (i[0], ofs)
                                    rodata[ofs] = newaddr
                                # update address to rodata
                                # done later
        
            # second pass on time graph ..
            # blocks might be different because of added basic blocks in relative->absolute jump conversion
            newmarkers = {}
            for i in list(cfgs.keys()):
                m_old = sum([cfgs[i].blocking,cfgs[i].blockcycles,cfgs[i].blockstar,cfgs[i].tg_break], [])
                if TIME_METHOD == 'timegraph': # time graph
                    # 5. Create time graph
                    # 6. Minimal spanning tree on time graph
                    cfgs[i].timegraph()
                if TIME_METHOD == 'reduction' or TIME_METHOD == 'none': # reduce markers
                    cfgs[i].reduceMarkers(False)
                if TIME_METHOD == 'none_and_reduction':
                    cfgs[i].oldblocking = cfgs[i].blocking
                    cfgs[i].blocking = cfgs[i].blocking_functions_and_lpm
                    cfgs[i].reduceMarkers(False, markers[i])
                    for e in (set(cfgs[i].oldblocking).difference(cfgs[i].tg_break)).difference(cfgs[i].blocking): # set flag for removed markers
                        for removemarker in [m for m in markers[i] if m.sourceAddress==e[0] and m.targetAddress==e[1]]:
                            removemarker.isTimedMarker = False
                            print("remove marker %s from timed set" % removemarker)
                    cfgs[i].updateMarkerEdges()
                    continue
                m_new = sum([cfgs[i].blocking,cfgs[i].blockcycles,cfgs[i].blockstar,cfgs[i].tg_break], [])
                for j in range(len(m_new)):
                    if m_new[j][0] > FAKEADDRESS_OFFSET:
                        m_new[j] = (m_new[j][0] - FAKEADDRESS_OFFSET, m_new[j][1])
                    assert(m_new[j][1] < FAKEADDRESS_OFFSET)
                for j in range(len(m_old)):
                    if m_old[j][0] > FAKEADDRESS_OFFSET:
                        m_old[j] = (m_old[j][0] - FAKEADDRESS_OFFSET, m_old[j][1])
                    assert(m_old[j][1] < FAKEADDRESS_OFFSET)
                m_diff = list(set(m_new).difference(set(blocks)))
                m_diff_rem = set(m_old).difference(set(m_new))
                try:
                    assert(len(m_diff_rem)==0), "removed markers %s" % hexlist(list(m_diff_rem))
                except:
                    print("old: %s"%hexlist(m_old))
                    print("new: %s"%hexlist(m_new))
                    raise
                if len(m_diff) > 0:
                    if (not USE_UNIQUE_MARKERS) or USE_CFG_UNIQUE_MARKERS:
                        nextmarkerid = max([m.id for m in markers[i]]) + 1
                    nextmarkerid, newmarkers[i] = cfgs[i].getMarkers(nextmarkerid, m_diff)
                    markers[i].extend(newmarkers[i])
                    blocks.extend(m_diff)
                else:
                    cfgs[i].updateMarkerEdges()
            print('End of pass %d, new blocking edges: %s' % (tg_pass,str(newmarkers)))
            if len(newmarkers) == 0:
                break
            newmarkers = markers
            #break
        
        prog = newprog
        
        # create lookup table for replay
        for i in cfgs.keys():
            if TIME_METHOD == 'none_and_reduction':
                # give removed markerset with cycles to the lookuptable function
                cycleedges = {(m.sourceAddress,m.targetAddress): m.cycles + m.latentCycles for m in markers[i] if not m.isTimedMarker}
                print('cycleedges: %s' % str(cycleedges))
                cfgs[i].createLookupTable(markers[i], cycleedges)
            else:
                cfgs[i].createLookupTable(markers[i], {})
                pass
        
        if debugfiles['basic_block_cycle_counts']:
            debugfile = open('%s.bbcycles' % elffilename, 'w')
            for a,bb in sorted(bbs.items()):
                print('%x-%x: %d' % (bb.start, bb.end, bb.cycles), file=debugfile)
            debugfile.close()
            
        if debugfiles['marker_info']:
            debugfile = open('%s.markers' % elffilename, 'w')
            for m in list(itertools.chain(*list(markers.values()))):
                if m.sourceAddress:
                    print('%x: %d, src: %x, tg: %x, latent: %d' % (m.address, m.id, m.sourceAddress, m.targetAddress, m.latentCycles), file=debugfile)
                else:
                    print('%x: %d, src:  -, tg: %x, latent: %d' % (m.address, m.id, m.targetAddress, m.latentCycles), file=debugfile)
            debugfile.close()
            
        if debugfiles['lookup_table']:
            debugfile = open('%s.lut' % elffilename, 'w')
            for k,v in [t for c in cfgs.values() for t in c.pathLookup.items()]:
                print('%x->%x (id %d): %s, cycles %s' % (k[0], v[0], k[1], hexlist([[bb.start for bb in p] for p in v[1]]), str([totalCycles([bb for bb in p]) for p in v[1]])), file=debugfile)
            debugfile.close()
            
        if debugfiles['loop_bounds']:
            debugfile = open('%s.loopbounds' % elffilename, 'w')
            json.dump({'(%s)'% ','.join('0x%x' % a for a in k):v for k,v in [i for c in cfgs.values() for i in c.loopbounds.items()]}, debugfile, indent=0)
            
            #for k,v in [i for c in cfgs.values() for i in c.loopbounds.items()]:
                #print('%s: ' % hexlist(k), file=debugfile)
            debugfile.close()
        
        print('<pickle2>')
        with open('%s.pickle2' % elffilename, 'wb') as PickleFile:
                pickle.dump((oldtonewprog, newtooldprog, markers, cfgs, enc, original_vectors), PickleFile)
        
    ##########################################################################
    # write modified binary
    psize_old = sum(s.section_size for s in [x for x in elf.sectionHeaders if x.name in [b'.text',b'.rodata']])
    text.content = progToBytes(prog)
    text.section_size = len(text.content)
    psize_new = sum(s.section_size for s in [x for x in elf.sectionHeaders if x.name in [b'.text',b'.rodata']])
    delta = psize_new - psize_old
    markercount = len([m for c in markers.values() for m in c])
    irqmarkercount = len(set(vectors))
    indirectmarkercount = len(set(indirect_call_functions))
    treenum = treenum + irqmarkercount + indirectmarkercount
    blockingmarkercount = sum([len(c.blocking) for c in cfgs.values()]) + irqmarkercount + indirectmarkercount
    if USE_CFG_UNIQUE_MARKERS:
        um = 'CFG unique markers'
    elif USE_UNIQUE_MARKERS:
        um = 'unique markers'
    else:
        um = 'no unique markers'
    if not (TIME_METHOD == 'reduction' or TIME_METHOD == 'none_and_reduction'):
        kmil = ''
    elif ALLOW_LOOPS_IN_TIMED:
        kmil = ' , remove markers in loops if possible'
    else:
        kmil = ' , keep markers in loops'
    print('Method: %s, %d passes, time %0.2f s, %s, tolerance %d%%%s' % (TIME_METHOD, tg_pass, time.time() - main_start_time, um, CPU_SPEED_ERROR * 100, kmil))
    print('Size: original %d, instrumented %d, added %d instructions (%d bytes, %0.2f%%)' % (psize_old, psize_new, addinsrelabsjmpcount+addinscount, delta, 100 * delta / psize_old))
    print('%d markers (%d instructions, %d bytes), %d long markers, %d blocking markers, %d stored sr, max marker id %d' % (markercount, addinscount, all_marker_size ,longenc, blockingmarkercount, savesrenc, max([m.id for ml in markers.values() for m in ml])))
    if TIME_METHOD != 'none':
        print('%d markers in non-time solution, %0.2f%% reduction, removed %0.2f%% non-blocking markers' % (treenum, (treenum-markercount) / treenum * 100, (treenum-markercount) / (treenum - blockingmarkercount) * 100))
    print('Numbers: %d & %d & %d & %d' % (psize_old, funcount, bbcount, inscount))
    # move .rodata section
    # move references to .rodata
    # src indirect with register

    # search for pointers in init data (.data)
    for ph in [x for x in elf.programHeaders if x.vaddr==elfaddrs[b'.data']]:
        initdatastart = ph.paddr
    #for i,h in enumerate(elf.sectionHeaders):
        #if h.name == b'.data':
    h = elfsections[b'.data']
    initdata = {}
    for p in range(0,h.section_size, 2):
        d = struct.unpack('<H', h.content[p:p+2])
        #print('.data -> .text / .rodata %x %x %d %d %d %d' % (d[0], p + initdatastart, d[0] in funcaddrs, p + elfsections[b'.data'].addr in rela_totext, d[0] in set(rodata.keys()).union(set([initdatastart])), p + elfsections[b'.data'].addr in rela_torodata))
        if d[0] in funcaddrs and p + elfsections[b'.data'].addr in rela_totext:
            initdata[p + initdatastart] = oldtonewprog[d[0]]
            if d[0] != oldtonewprog[d[0]]:
                print('adapt function pointer at %x in init data %x -> %x' % (p + initdatastart, d[0], oldtonewprog[d[0]]))
                pass
        elif d[0] in set(rodata.keys()).union(set([initdatastart])) and p + elfsections[b'.data'].addr in rela_torodata:
            initdata[p + initdatastart] = d[0] + delta
            print('adapt data pointer at %x in init data %x -> %x' % (p + initdatastart, d[0], d[0] + delta))
        else:
            initdata[p + initdatastart] = d[0]
            if d[0] in funcaddrs:
                print('keep value at %x in init data, possible function pointer %x -> %x' % (p + initdatastart, d[0], oldtonewprog[d[0]]))
            elif d[0] in set(rodata.keys()).union(set([initdatastart])):
                print('keep value at %x in init data, possible data pointer %x -> %x' % (p + initdatastart, d[0], d[0] + delta))
    elf.sectionHeaders[elfsections_idx[b'.data']].content = struct.pack('<%dH' % (h.section_size / 2), *[initdata[i] for i in sorted(initdata.keys())])
    
    check_rela_torodata = copy.copy(rela_torodata) # sanity check, do we adjust all pointers
    for addr,instr in prog.items():
        if instr.size > 1:
            # immediate values pointing to rodata
            # double op type I
            if instr.As==1 and instr.sreg not in [2,3]:
                if instr.arg1 in set(rodata.keys()).union(set([initdatastart])) and (instr.originaladdr + 2) in rela_torodata:
                    print('adapt immediate value of %s, %x pointer to mem' % (instr, instr.arg1))
                    prog[addr].arg1 += delta              
                    check_rela_torodata.remove(instr.originaladdr + 2)
                    continue
            # same for single op type II
            if not instr.modified and (instr.As==3 or instr.Ad==3) and instr.sreg not in [2,3]:
                if int(instr.arg1 / 2) * 2 in set(rodata.keys()).union(set([initdatastart])):
                    if instr.originaladdr and (instr.originaladdr + 2) in rela_torodata:
                        print('adapt immediate value of %s, %x pointer to mem' % (instr, instr.originaladdr))
                        prog[addr].arg1 += delta
                        check_rela_torodata.remove(instr.originaladdr + 2)
                        continue
                    else:
                        print('keep immediate value of %s, %x possible pointer to mem' % (instr, instr.originaladdr))
                        pass
            # immediate values pointing to text (function addresses)
            if not instr.modified and (instr.As==3 or instr.Ad==3) and instr.sreg not in [2,3]:
                if instr.arg1 in funcaddrs:
                    if instr.originaladdr and (instr.originaladdr+2) in rela_totext:
                        if prog[addr].arg1 != oldtonewprog[prog[addr].arg1]:
                            print('adapt immediate value of %s, %x, pointer to function' % (instr, instr.originaladdr))
                            pass
                        prog[addr].arg1 = oldtonewprog[prog[addr].arg1]
                        continue
                    else:
                        print('keep immediate value of %s, %x possible pointer to function' % (instr, instr.originaladdr))
                        pass
    if len(check_rela_torodata)>0:
        print("WARNING: there are still unticked items in rela_torodata: %s" % hexlist(check_rela_torodata))
    newrodata = rodata
                
    for vectorsection in [x for x in elf.sectionHeaders if x.name==b'.vectors']:
        vectorsection.content = struct.pack('<%dH' % len(vectors), *vectors)

    # update content
    text.content = progToBytes(prog)
    # move section
    for rosection in [x for x in elf.sectionHeaders if x.name==b'.rodata']:
        #rosection.offset += delta
        rosection.addr += delta
        rosection.content = struct.pack('<%dH' % (rosection.section_size / 2), *[newrodata[i] for i in sorted(newrodata.keys())])
    #for section in [x for x in elf.sectionHeaders if x.offset >= rosection.offset - delta]:
        #section.offset += delta
        
    # adjust program header
    for ph in [x for x in elf.programHeaders if x.offset==0]: # .text .rodata
        ph.filesz += delta
        ph.memsz += delta
        textoffset = ph.vaddr
        print('adjust programm header <.text .rodata>')
    for ph in [x for x in elf.programHeaders if x.vaddr + x.memsz == 0x10000]: # .vectors
        ph.offset += delta
        print('adjust programm header <.vectors>')
    for ph in [x for x in elf.programHeaders if x.vaddr > 0x1100 and x.vaddr < textoffset]: # .noinit
        ph.offset += delta
        print('adjust programm header <.noinit>')
    for ph in [x for x in elf.programHeaders if x.vaddr==0x1100]: # .data .bss
        ph.offset += delta
        ph.paddr += delta
        print('adjust programm header <.data .bss>')
    # adjust symbol addresses
    for i,st in enumerate(elf.sectionHeaders):
        if st.name == b'.symtab':
            content = bytearray(st.content)
            for addr, instr in prog.items():
                for ptr in instr.symtabptr:
                    content[ptr + 4:ptr + 8] = struct.pack('<I', addr)
            for offset in range(0, st.section_size, 16):
                st_name, st_value, st_size, st_info, st_other, st_shndx = struct.unpack('<IIIBBH', st.content[offset:offset+16])
                #print map(lambda x: '%x' % x, struct.unpack('<IIIBBH', content[offset:offset+16]))
                if st_shndx in (elfsections_idx[name] for name in (b'.data',b'.rodata', b'.text')) and st_value in rodata:
                    content[offset + 4:offset + 8] = struct.pack('<I', st_value + delta)
            elf.sectionHeaders[i].content = content
    
    b = elf.pack()
    modf = open('%s.mod.elf' % elffilename, 'wb')
    modf.write(b)
    modf.close()

        
if __name__ == '__main__':
    print(sys.version)
    main()