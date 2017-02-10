#!/usr/bin/env python3

import os, sys
import optparse
import pickle as pickle
from instrument import *
from tracing import *
import networkx as nx
import struct

GPIOCHANGETIME = 400e-9 # minimal time between GPIO changes
CPUFREQUENCY = 800e3    # initial CPU frequency estimate
IRQCYCLES = 6           # time to enter IRQ handler
IRQ_CONSECUTIVE_TIME = 100e-9
CACHE = True

class FrequencyEstimate(object):
    starttime = 0
    measurement_history = []
    lastfreq_min = 0
    lastfreq_max = 100e6
    stepthreshold = 5e3 # frequency estimation reset threshold in Hz
    freq = None
    lastestimate = 0
    estnum = 0
    
    # values normally used
    maxcycles = 10000
    mincycles = 200
    minhist = 100
    maxhist = 200   
    mintimebetweenestimates = 5e-3
    # values used for frequency example
    #maxcycles = 10000
    #mincycles = 10
    #minhist = 20
    #maxhist = 1000
    #mintimebetweenestimates = 10e-9
    
    def __init__(self):
        pass
    
    def addMeasurement(self, cycles, ts):
        """
        cycles: the number of cycles since the last measurement
        ts:     timestamp of measurement 
        """
        #print('addMeasurement %d %0.9f' % (cycles, ts))
        if len(self.measurement_history)==0:
            self.starttime = ts
            self.measurement_history.append((0, 0))
        else:
            self.measurement_history.append((self.measurement_history[-1][0]+cycles, ts - self.starttime))
            while self.measurement_history[-1][0] - self.measurement_history[0][0] > self.maxcycles or len(self.measurement_history) > self.maxhist:
                del(self.measurement_history[0])
            if self.measurement_history[-1][0] - self.measurement_history[0][0] >= self.mincycles and len(self.measurement_history)>= self.minhist:
                if ts - self.lastestimate > self.mintimebetweenestimates:
                    self.lastestimate = ts
                    self.doOls()
                    
            
    def doOls(self):
        # means
        cycles, times = zip(*self.measurement_history)
        mean_x = sum(cycles) / float(len(cycles))
        mean_y = sum(times)  / float(len(times))
        mean_xy = sum([c*t for c,t in self.measurement_history]) / float(len(self.measurement_history))
        mean_xx = sum([c*c for c,t in self.measurement_history]) / float(len(self.measurement_history))
        # slope
        slope = (mean_xy - mean_x * mean_y) / (mean_xx - mean_x * mean_x)
        #print('OLS, measurements: [')
        #lastc, lastt = (0,0)
        #for c,t in self.measurement_history:
            #if c-lastc > 0:
                #print('%d %0.9f %0.9f %0.9f'% (c,t,self.starttime + t,(t-lastt)/(c-lastc)))
            #else:
                #print('%d %0.9f %0.9f'% (c,t,self.starttime + t))
            #lastc, lastt = (c,t)
        #print('];')
        self.estnum = self.estnum + 1
        self.freq = 1.0/slope
        print('%d: %0.9f, %d measurements, slope is %f, frequency %f Hz' % (self.estnum, self.lastestimate, len(self.measurement_history), slope * 1e6, self.freq))
        if self.lastfreq_max - self.freq > self.stepthreshold or self.freq - self.lastfreq_min > self.stepthreshold:
            print("step, because above threshold")
            self.notifyAmbigeousPath()
            self.lastfreq_max = self.freq
            self.lastfreq_min = self.freq
        self.lastfreq_min= min(self.lastfreq_min, self.freq)
        self.lastfreq_max= max(self.lastfreq_max, self.freq)
     
    def notifyAmbigeousPath(self):
        # clear history
        self.measurement_history = []
    

class CFGState(object):
    """
    A Class to represent the parsing state within a CFG.
    """   
    def __init__(self, cfgentry, time):
        self.func = cfgentry # cfg
        self.addr = cfgentry # basic block
        self.marker = cfgentry # marker
        self.lastrealmarker = cfgentry # marker
        self.time = time # time of marker (also virtual marker on function call)
        self.isVirtualMarker = False # set to true if marker is computed based on cfg
        self.cycle = 0 # number of cycles since last marker, used when entering functions
        self.expectIndirectCallMarker = False

class Trace(object):
    
    _data_irq = []
    _data_normal = []
    _irq_intervals = [(-1,-1)]
    
    def __init__(self, folder, writebinary):
        if writebinary:
            self.bbfile = open('%s/trace.b' %  folder, 'wb')
        else:
            self.bbfile = open('%s/trace.txt' %  folder, 'w')
        self.writebinary = writebinary
        pass
    
    def log(self, inIrq, time, event):
        """
        Log the occurence of event at time.
        event: address
        """
        if inIrq:
            self._data_irq.append((time, event))
        else:
            self._data_normal.append((time, event))
        
    def irqStart(self, time):
        self.irqstarttime = time
        
    def irqEnd(self, time):
        self._irq_intervals.append((self.irqstarttime, time))
        
    def commit(self):
        """
        Sort events and write them to the file. All events logged after a commit have to occur later in time.
        """
        data = []
        self._data_irq = sorted(self._data_irq, key=operator.itemgetter(0))
        self._data_normal = sorted(self._data_normal, key=operator.itemgetter(0))
        keep = self._data_normal.pop(-1) # keep last element, because if the interrupt just kicked in after the marker, this element should be handled only after the interrupt
        irqoffset = 0
        #print(self._irq_intervals)
        
        while len(self._irq_intervals) > 0:
            irqstart, irqend = self._irq_intervals.pop(-1)
            # normal execution, up to irq end
            while len(self._data_normal) > 0 and self._data_normal[-1][0]-irqoffset >= irqend:
                event = self._data_normal.pop(-1)
                data.insert(0, ('n', event[0]-irqoffset, event[1]))            
                #print('trace: normal %0.9f %s %0.9f' % (event[0]-irqoffset, event[1], irqoffset))
            # check next non irq bb, it might as well be after the irq
            if len(self._data_normal) > 0 and len(self._irq_intervals) == 1 and self._data_normal[-1][0] >= irqstart:
                event = self._data_normal.pop(-1)
                data.insert(0, ('n', event[0]+irqend-irqstart, event[1]))            
                #print('trace: normal just before irq %0.9f %s' % (event[0]+irqend-irqstart, event[1]))
            # irq executionm up to irq start
            while len(self._data_irq) > 0 and self._data_irq[-1][0] >= irqstart:
                event = self._data_irq.pop(-1)
                data.insert(0, ('i', event[0], event[1]))
                #print('trace: irq    %0.9f %s %0.9f' % (event[0]-irqoffset, event[1], irqoffset))
            irqoffset = irqoffset + irqend - irqstart
        assert(len(self._data_irq)==0 and len(self._data_normal)==0)
        
        if self.writebinary:
            d = list((e[2] for e in data if e[2] <= 0xffff))
            print(d)
            self.bbfile.write(struct.pack('%dH' % len(d), *d))
        else:
            for e in data:
                print('%s %0.9f %x' % (e[0],e[1],e[2]),file=self.bbfile)
        
        self._data_irq = []
        self._data_normal = [keep]
        self._irq_intervals = [(-1,-1)]
        
    def flush(self):
        """
        Flush everything (up to last commit) and close file.
        """
        self.bbfile.close()
        
class NoTrace(object):
      
    def __init__(self, folder):
        pass
    
    def log(self, inIrq, time, event):
        pass        
        
    def irqStart(self, time):
        pass
        
    def irqEnd(self, time):
        pass
        
    def commit(self):
        pass
        
    def flush(self):
        pass
        
        
class ProgramState(object):
    
    enterIrq = False
    G = {}
    
    def __init__(self, nodeid, cfgs, markers, tracewriter, resultsfolder, writetrace, writebinarytrace, enc):
        self.nodeid = nodeid
        self.ts = -1
        self.last_marker_ts = -1
        self.lastts = 0
        self.lastgpio = 0
        self.gpio = 0
        self.gpiohist = [[],[]]
        self.gpioirq = 0
        self._stack = []
        self.stack = None
        self.cfgname = ''
        self.cfgs = cfgs
        self.currentcfg = None
        self.irqmarkers = {}
        self.indirectcallmarkers = {}
        self.indirectcalls = set([])
        self.tw = tracewriter
        self.pendingcycles = 0
        self.cpufrequency = CPUFREQUENCY
        self.latentCycles = [0,0]
        self.lastLPMWakeup = 0
        self.irqTime = 0
        self.inIrq = 0
        self.irqEnterTime = 0
        self.irqExitTime = 0
        self.cache = {} # (source, target) -> [(possible paths, cycles)]
        self.frqEst = FrequencyEstimate()
        self.markercount = 0
        self.ntmarkercount = 0
        self.cyclecount = [0] # number of cycles spent in program code not containing instrumentation
        self.markercyclecount = [0] # number of cycles spent in instrumentation
        self.resettime = 0
        self.sleeptime = 0
        self.ignoremarkers = {}
        self.tracebbcount = 0
        self.enc = enc
        
        for c, lm in markers.items():
            for im in lm:
                if isinstance(im,IrqMarker):
                    self.irqmarkers[im.id]=im
                elif isinstance(im,IndirectCallMarker):
                    self.indirectcallmarkers[im.id]=im
                    self.indirectcalls.update([im.targetAddress])
                    
        for i in cfgs.keys():
            cfgs[i].treemarkers={e: True for e in set(cfgs[i].edges).difference(cfgs[i].tree).union(cfgs[i].blocking)}
            self.ignoremarkers[i] = {m.id: True for m in markers[i] if not m.isTimedMarker}
            
        if writetrace or writebinarytrace:
            self.trace = Trace(resultsfolder, writebinarytrace)
        else:
            self.trace = NoTrace(resultsfolder)
        
    def setCfgName(self, name):
        if self.enterIrq:
            self.cfgname = 'interrupt: %s' % name
        else:
            self.cfgname = name
        #print([self.cfgs[x.func].name for x in self._stack])
    
    def getCfgName(self):
        tmp = self.cfgname
        self.cfgname = ''
        self.enterIrq = False
        return tmp
        
    def count_nt_markers(self, bbpath, lastnode):
        lastaddr = -1
        count = 0
        countloop = 0
        for bb in bbpath:
            if isinstance(bb, LoopBlock):
                looppath = [b.start for b in bb.loop_bb if b.start != 0]
                looppath.append(bb.loop_bb[0].start)
                for ei in range(len(looppath)-1):
                    if tuple(looppath[ei:ei+2]) in self.cfgs[self.currentcfg].treemarkers:
                        countloop = countloop + 1
                lastaddr = bb.loopexit
            else:
                if (lastaddr, bb.start) in self.cfgs[self.currentcfg].treemarkers:
                    count = count + 1
                lastaddr = bb.start
        if (lastaddr, lastnode) in self.cfgs[self.currentcfg].treemarkers:
            count = count + 1
        return count, countloop
        
    def nextCfg(self):
        try:
            # follow unambigeous path
            self.stack.cycle = self.latentCycles[self.inIrq]
            print('nextCfg cycle update: %d latent cycles' % self.latentCycles[self.inIrq])
            while len(self.cfgs[self.currentcfg].bbs[self.stack.addr].successors)==1 and (self.stack.addr, self.cfgs[self.currentcfg].bbs[self.stack.addr].successors[0]) not in self.cfgs[self.currentcfg].markeredges:
                self.addProgramCycles(self.cfgs[self.currentcfg].bbs[self.stack.addr].cycles)
                if (self.stack.addr, self.cfgs[self.currentcfg].bbs[self.stack.addr].successors[0]) in self.cfgs[self.currentcfg].treemarkers:
                    self.ntmarkercount = self.ntmarkercount + 1
                self.stack.cycle += self.cfgs[self.currentcfg].bbs[self.stack.addr].cycles
                print('nextCfg cycle update: %x, %d cycles -> %d' % (self.stack.addr, self.cfgs[self.currentcfg].bbs[self.stack.addr].cycles, self.stack.cycle))
                if self.cfgs[self.currentcfg].bbs[self.stack.addr].isCall:
                    self.latentCycles[self.inIrq] = 0
                    # update time of parent cfg
                    lastmarkertime = self.stack.time
                    self.stack.time = self.stack.time + self.stack.cycle / self.getCpuFreq()                    
                    self.frqEst.addMeasurement(self.stack.cycle, self.stack.time)
                    if self.cfgs[self.currentcfg].bbs[self.stack.addr].isIndirectCall or self.cfgs[self.currentcfg].bbs[self.stack.addr].callTarget in self.indirectcalls:
                        print('%x is indirect call, %d cycles since last marker' % (self.stack.addr, self.stack.cycle))
                        print('expecting function marker')
                        self.stack.expectIndirectCallMarker = True # wait for the function marker
                        return
                    else:
                        print('%x is call to %x, %d cycles since last marker' % (self.stack.addr, self.cfgs[self.currentcfg].bbs[self.stack.addr].callTarget, self.stack.cycle))
                        # new cfg
                        self.pushNewState(CFGState(self.cfgs[self.currentcfg].bbs[self.stack.addr].callTarget, self.stack.time))
                        self.stack.isVirtualMarker = True
                        print('v---    %0.7f,%d,-,%d,%x,%x,-,<%s>' % (self.stack.time, self.nodeid, round((self.stack.time - lastmarkertime) * self.cpufrequency),self.currentcfg,self.currentcfg,self.cfgs[self.currentcfg].name))
                        self.tw.call(self.ts, self.cfgs[self.currentcfg].name, self.currentcfg)
                        self.trace.log(self.inIrq, self.stack.time, self.stack.addr)
                        self.tracebbcount = self.tracebbcount + 1
                else:
                    self.stack.addr = self.cfgs[self.currentcfg].bbs[self.stack.addr].successors[0]                    
        except Exception:
            print('cfg: %x, stack: %x %x' %(self.currentcfg, self.stack.func, self.stack.addr))
            raise
            
    def ignoremarker(self, m):
        if m in self.ignoremarkers[self.currentcfg]:
            return True
        return False
    
    def checkTransition(self, m):
        cfgentry = self.currentcfg
        source = self.stack.marker
        try:
            assert((self.stack.lastrealmarker, m) in self.cfgs[cfgentry].pathLookup)
        except:
            print('last marker address: %x, marker %d [%s] not found in lookup' % (self.stack.lastrealmarker, m, marker2gpiostring(m, self.enc)))
            print('last marker address: %x, marker %d [%s] not found in lookup, last timestamp was %0.9f' % (self.stack.lastrealmarker, m, marker2gpiostring(m, self.enc), self.ts), file=sys.stderr)
            raise
        path_candidates = self.cfgs[cfgentry].pathLookup[(self.stack.lastrealmarker, m)][1]
        try:
            target = path_candidates[0][-1]
        except:
            print(path_candidates)
            print(m)
            print("%x" % source)
            raise
        try:
            path_candidates, path_candidates_bb, cycles, thismarker, nt_markercount= self.cache[(source, target, m)]
        except KeyError:
            print('checkTransition')
            print(self.stack.lastrealmarker)
            print(path_candidates)
            print(m)
            print("%x" % source)
            if path_candidates[0][0].start != source: # remove nodes up to source
                path_candidates = copy.copy(path_candidates)
                for p in path_candidates:
                    while p[0].start != source:
                        del(p[0])
            nt_markercount = [self.count_nt_markers([bb for bb in c], self.cfgs[cfgentry].pathLookup[(self.stack.lastrealmarker, m)][0]) for c in path_candidates]
            print(path_candidates)
            print(nt_markercount)
            cycles  = list([totalCycles([bb for bb in c]) for c in path_candidates]) 
            path_candidates_bb = path_candidates
            path_candidates = list([[bb.start for bb in p] for p in path_candidates])
            thismarker = self.cfgs[cfgentry].pathLookup[(self.stack.lastrealmarker, m)][2]
            if CACHE:
                self.cache[(source, target, m)] = (path_candidates, path_candidates_bb, cycles, thismarker, nt_markercount)
        print('candidates %d: %s, latent cycles %d' % (len(path_candidates), hexlist(path_candidates), self.latentCycles[self.inIrq]))
        print('cycles: %s, id: %d, marker cycles: %d %s' % (str(cycles), m, thismarker.cycles, str(thismarker)))
        assert(m==thismarker.id)
        if self.inIrq:
            irqTimeComp = 0
        else:
            irqTimeComp = self.irqTime
            self.irqTime = 0
        cpufrequency = self.getCpuFreq()
        if len(cycles)==1 and cycles[0][1] == 0: # only one possible path, no loop cycles
            frq_num_cycles = cycles[0][0] + self.latentCycles[self.inIrq] + thismarker.cycles
            mindeltapos = 0
            loops=[0]
            if self.stack.time < self.lastLPMWakeup:
                print("no speed measurement due to LPM wakeup (at %0.7f)" % self.lastLPMWakeup)
                self.frqEst.notifyAmbigeousPath()
            elif self.stack.isVirtualMarker:
                print("no speed measurement because of virtual marker")
            else:
                for c in path_candidates[0]:
                    if c == 0:
                        continue # this is a marker basic block
                    print('%x-%x: %d' % (self.cfgs[cfgentry].bbs[c].start, self.cfgs[cfgentry].bbs[c].end, self.cfgs[cfgentry].bbs[c].cycles))
                print('latent cycles: %d, marker cycles: %d, t0: %0.7f, t1: %0.7f, Tirq: %0.7f' % (self.latentCycles[self.inIrq], thismarker.cycles, self.stack.time, self.ts, irqTimeComp))
                if (self.ts - self.stack.time - irqTimeComp) > 0:
                    frq_m = (cycles[0][0] + self.latentCycles[self.inIrq] + thismarker.cycles)/ (self.ts - self.stack.time - irqTimeComp)
                    self.updateFrequencyEstimate(frq_m)
                    print('measured clock speed %0.0f Hz, %0.7f, %d cycles, current estimate %0.0f Hz' % (frq_m, self.ts, cycles[0][0] + self.latentCycles[self.inIrq] + thismarker.cycles, self.cpufrequency))
        else:
            #self.frqEst.notifyAmbigeousPath()
            passedtime = self.ts - self.stack.time - irqTimeComp - (self.latentCycles[self.inIrq] + thismarker.cycles)/ cpufrequency
            # calculate deltas
            deltas = []
            loops = []
            mindelta = 100
            mindeltapos = -1
            i = 0
            for c,lc in cycles:
                if lc==0: # no loops
                    deltas.append(passedtime * cpufrequency - c)
                    loops.append(0)
                else:
                    d = passedtime * cpufrequency - c
                    loops.append(max([0,round(d / lc)]))
                    deltas.append(d - loops[-1] * lc)
                if mindeltapos < 0 or mindelta > abs(deltas[-1]):
                    mindeltapos = i
                    mindelta = abs(deltas[-1])
                i = i + 1
            i = 0
            for c,lc in cycles:
                if mindeltapos == i:
                    print("%d %d loops: %d, delta %0.7f <==" % (c,lc,loops[i], deltas[i]))
                else:
                    print("%d %d loops: %d, delta %0.7f" % (c,lc,loops[i], deltas[i]))
                i = i + 1
            print('best loop delta at %0.7f,%0.2f,%d,%d,%d' % (self.ts, mindelta,cycles[mindeltapos][0],cycles[mindeltapos][1],loops[mindeltapos]))
            if len(deltas) > 0 and len(set(deltas)) != len(deltas):
                print('WARNING: ambigeous path from %x to %x.' % (source, target))
                assert(False)
            frq_num_cycles = cycles[mindeltapos][0] + cycles[mindeltapos][1] * loops[mindeltapos] + self.latentCycles[self.inIrq] + thismarker.cycles
            if (self.ts - self.stack.time - irqTimeComp) > 0:
                printfreq = '%f' % (frq_num_cycles / (self.ts - self.stack.time - irqTimeComp))
            else:
                printfreq = 'NaN'
            print("path, %d cycles (%d + %d * %d + %d), freq %s Hz" % (frq_num_cycles,  cycles[mindeltapos][0], loops[mindeltapos], cycles[mindeltapos][1], thismarker.cycles, printfreq))
            if loops[mindeltapos] > 0:
                self.ntmarkercount = self.ntmarkercount + loops[mindeltapos] * nt_markercount[mindeltapos][1]
            ## NOTE: we need some good indicator for this..
            #if (frq_num_cycles / (self.ts - self.stack.time - irqTimeComp)) - cpufrequency > 1e5:
                #self.frqEst.notifyAmbigeousPath()
        self.frqEst.addMeasurement(frq_num_cycles, self.ts)
        if self.frqEst.freq:
            print('freq %0.7f,%d' % (self.ts, self.frqEst.freq))
        self.ntmarkercount = self.ntmarkercount + nt_markercount[mindeltapos][0]
        self.addProgramCycles(cycles[mindeltapos][0] + cycles[mindeltapos][1] * loops[mindeltapos])
        # return path taken
        ret = []
        totalcycles = 0
        for bb in path_candidates_bb[mindeltapos]:
            print(bb)
            if bb.start == 0:
                totalcycles = totalcycles + bb.cycles
                continue
            if isinstance(bb, LoopBlock):
                #print("path: loop: header %s, loop %s" % (looppaths[mindeltapos][bb.start].loopheader, looppaths[mindeltapos][bb.start].loop))
                for i in bb.getHeaderAddrAndCycles():
                    if i[0] != 0:
                        ret.append((i[0],totalcycles))
                    totalcycles = totalcycles + i[1]
                for j in range(loops[mindeltapos]):
                    for i in bb.getLoopAddrAndCycles():
                        if i[0] != 0:
                            ret.append((i[0],totalcycles))
                        totalcycles = totalcycles + i[1]
            else:
                print("path: no loop %x, %d" % (bb.start,bb.cycles))
                ret.append((bb.start, totalcycles))
                totalcycles = totalcycles + bb.cycles
        totalcycles = totalcycles + thismarker.cycles
        print('totalcycles %d' %totalcycles)
        print('path: %s' % ret)
        ret2 = []
        for r in ret:
            ret2.append((r[0], self.ts - (totalcycles - r[1]) / cpufrequency))
        print('path: %s' % ret2)
        return ret2[1:]
        
        
    def updateFrequencyEstimate(self, measurement):
        self.cpufrequency = self.cpufrequency * 0.8 + measurement * 0.2
        
    def getCpuFreq(self):
        if self.frqEst.freq:
            return self.frqEst.freq
        else:
            return self.cpufrequency
        
    def pushNewState(self, state):
        self._stack.append(state)
        self.stack = self._stack[-1]
        self.currentcfg = self.stack.func
        self.setCfgName(self.cfgs[self.currentcfg].name)
    
    def popState(self):
        lastcfg = self.stack.func
        del(self._stack[-1])
        self.stack = self._stack[-1]
        self.currentcfg = self.stack.func
        self.setCfgName('ret %s to %s' % (self.cfgs[lastcfg].name, self.cfgs[self.currentcfg].name))
        
    def flushtrace(self):
        self.trace.flush()
        
    def addProgramCycles(self, c):
        self.cyclecount[-1] = self.cyclecount[-1] + c
    
    def addMarkerCycles(self, c):
        self.markercyclecount[-1] = self.markercyclecount[-1] + c
        
    def wakeupFromIrq(self):
        self.cyclecount.append(0)
        self.markercyclecount.append(0)
        
class NoTraceWriter(object):

    def __init__(self, filename):
        pass
        
    def marker(self, time, id, address):
        pass

    def call(self, time, name, address):
        pass
        
    def callend(self, time, name, address):
        pass
        
    def flush(self):
        pass
        
def marker2gpiostring(mm, enc):
    m = enc.encode(mm)
    for i in range(len(m)):
        m[i] = str((m[i] & 0x07) + ((m[i] & 0x18) << 3))
    return ','.join(m)
        
## main ########################################
def main():
    u = 'usage: %prog gpiotracefile elffile'

    parser = optparse.OptionParser(usage = u)
    parser.add_option("-s", "--start", action="store", type="float", dest="starttime", help="ignore events before this time")
    parser.add_option("-e", "--end", action="store", type="float", dest="endtime", help="ignore events after this time")
    parser.add_option("-O", "--stdin", action="store_true", dest="usestdin", default=False, help="read event from stdin instead of file")
    parser.add_option("-t", "--tracefile", action="store_true", dest="writetrace", default=False, help="write trace to trace.txt (text file)")
    parser.add_option("-b", "--binarytracefile", action="store_true", dest="writebinarytrace", default=False, help="wite trace tp trace.b (binary file)")
    
    options, args = parser.parse_args()   
    
    if len(sys.argv) == 1:
      parser.print_help()
      exit(1)
      
    gpiofilename = args[0]
    elffilename = args[1]
    workingdir = os.path.dirname(gpiofilename)
    
    with open('%s.pickle2' % elffilename, 'rb') as PickleFile:
        oldtonewprog, newtooldprog, markers, cfgs, enc, vectors = pickle.load(PickleFile) # second markers should be annotated with cycle count for instructions, second cfgs with updated cycles
        
    for key, value in cfgs.items():
        cfgs[key].name = str(cfgs[key].name, 'utf-8')
    
    tw = NoTraceWriter('%s/trace.ctf' % workingdir)
    count = 0
    gpio2bit = {'LED1': 16,'LED2': 8,'LED3': 4,'INT1': 1,'INT2': 2}
    states = {}
    debug = False
    
    if options.usestdin:
        gpiofile = sys.stdin
    else:
        gpiofile = open(gpiofilename)
        
    with gpiofile as f:
        for line in f:
            s = line.strip().split(',')
            time = float(s[0])
            if options.starttime and time < options.starttime:
                continue
            if options.endtime and time > options.endtime:
                break
            obsid = int(s[1])
            nodeid = int(s[2])
            gpiobit = gpio2bit[s[3]]
            gpiolevel = int(s[4])
            #print [time, obsid, nodeid, gpiobit, state]
            if not nodeid in states:
                states[nodeid] = ProgramState(nodeid, cfgs, markers, tw, workingdir, options.writetrace, options.writebinarytrace, enc)
            state = states[nodeid]
            if (time < state.ts): # bug in daq ??
                time = time + 0.2
            assert(time - state.ts >= 0) # ordered data
            
            if time > state.ts + GPIOCHANGETIME:
                if state.ts > 0:
                    g = state.gpio ^ state.lastgpio
                    #print(g)
                    #print(state.gpiohist[state.gpioirq])
                    mIsIrq = False
                    #mIsIrqEnd = False
                    if g == 31:
                        m = None
                        assert(state.gpioirq==0 or state.currentcfg is None) # ignore multiple interrupts after reset
                        state.gpioirq = 1
                        if state.currentcfg is None:
                            state.gpiohist[state.gpioirq] = []
                        state.gpiohist[state.gpioirq].append(g)
                        assert(len(state.gpiohist[state.gpioirq])==1)
                    elif g >= enc.longrangestart and len(state.gpiohist[state.gpioirq])==0:
                        state.gpiohist[state.gpioirq].append(g)
                        m = None
                    #elif g == ENDMARKER and state.gpioirq == 1 and len(state.gpiohist[state.gpioirq])==0 and state.stack.func in vectors:
                        #m = g
                        #print('end of interrupt')
                        #mIsIrqEnd = True
                        #assert(len(state.gpiohist[state.gpioirq])==0)
                        #state.gpioirq = 0
                    else:
                        if len(state.gpiohist[state.gpioirq]) > 0 and len(state.gpiohist[state.gpioirq]) < 4:
                            #if state.gpiohist[state.gpioirq][0] == 31 and len(state.gpiohist[state.gpioirq]) == 1:
                                #state.gpiohist[state.gpioirq].append(state.gpio)
                            #else:
                            state.gpiohist[state.gpioirq].append(g)
                            #print("long or irq (%d) %s" % (state.gpioirq, str(state.gpiohist[state.gpioirq])))
                            if state.gpiohist[state.gpioirq][0] == 31 and len(state.gpiohist[state.gpioirq]) == 3:
                                mIsIrq = True
                                m = state.gpiohist[state.gpioirq][-1]
                                mWasLPM = (state.gpiohist[state.gpioirq][-2] & 0x3) == 1
                                if mWasLPM:
                                    state.lastLPMWakeup = state.ts
                                    if not state.stack is None:
                                        state.sleeptime = state.sleeptime + state.ts - state.stack.time
                                        print('wakeup from LPM at %0.7f, previous marker at %0.7f, sleeptime %0.7fs' % (state.ts, state.stack.time, state.ts-state.stack.time))
                                    else:
                                        print('wakeup from LPM at %0.7f' % (state.ts))
                                    print('freq %0.7f,Nan' % (state.ts))
                                    state.wakeupFromIrq()
                                #print('markers: %s' % str(state.gpiohist[state.gpioirq]))
                                state.gpiohist[state.gpioirq] = []
                            else:
                                #if len(state.gpiohist[state.gpioirq]) == 4:
                                if state.gpiohist[state.gpioirq][0] != 31 and state.gpiohist[state.gpioirq][-1] < enc.longrangestart:
                                    m = enc.decode(state.gpiohist[state.gpioirq])
                                    #print("decoded %s to %d" %(str(state.gpiohist[state.gpioirq]), m))
                                    #m = (state.gpiohist[state.gpioirq][1] - 1) * 30 + state.gpiohist[state.gpioirq][2] - 1 + 30
                                    #m = (state.gpiohist[state.gpioirq][1] - 1) * 900 + (state.gpiohist[state.gpioirq][2] - 1) * 30 + state.gpiohist[state.gpioirq][3] - 1 + 30
                                    #print 'long marker %d %s' % (state.gpioirq,str(state.gpiohist[state.gpioirq]))
                                    state.gpiohist[state.gpioirq] = []
                                else:
                                    m = None
                        else:
                            m = g
                    #print('%d %d' % (state.gpioirq,g))
                    if debug and m:
                        print('d---    %0.7f,%d,%d,%d' % (state.ts, nodeid, m, round((state.ts - state.last_marker_ts) * CPUFREQUENCY)))
                    if not m is None and not debug:
                        """
                        state.ts is time of last gpio change
                        time taken by marker is:
                            all nodes: gpio instructions (XOR)
                            for multiple entry nodes: possibly one or more jump instructions, depending from where the flow enters
                        """  
                        state.markercount = state.markercount + 1
                        if (not mIsIrq) and state.currentcfg and state.ignoremarker(m) and (not state.stack.expectIndirectCallMarker): # for double instrumentation, ignore non-time markers
                            print("marker %d is not timed marker %s" % (m, str([mm for mm in markers[state.currentcfg] if mm.id==m])))
                            state.markercount = state.markercount - 1
                        elif mIsIrq:
                            print('irqmarker')
                            state.enterIrq = True
                            state.pushNewState(CFGState(state.irqmarkers[m].targetAddress, state.ts))
                            tw.call(state.ts, cfgs[state.stack.func].name, state.stack.func)
                            if state.currentcfg == vectors[-1]: # reset vector
                                state.gpiohist = [[],[]]
                                state.gpioirq = 0
                                state.markercount = 0
                                state.ntmarkercount = 0
                                state.resettime = state.ts
                                state.markercyclecount = [0]
                                state.cyclecount = [0]
                            else:
                                state.inIrq = 1
                                state.latentCycles[state.inIrq] = 0
                                irqEnterTime = state.ts - (state.irqmarkers[m].cycles + IRQCYCLES) / state.getCpuFreq()
                                if (abs(irqEnterTime - state.irqExitTime) <= IRQ_CONSECUTIVE_TIME):
                                    state.irqTime = state.irqTime - (state.irqExitTime - state.irqEnterTime) # keep the old entry time
                                else:
                                    state.irqEnterTime = state.ts - (state.irqmarkers[m].cycles + IRQCYCLES) / state.getCpuFreq()
                                print("time between irqs: %0.7f %0.7f %0.3fns" % (state.irqEnterTime, state.irqExitTime, (state.irqEnterTime - state.irqExitTime) * 1e9))
                                state.addMarkerCycles(state.irqmarkers[m].cycles)
                            if state.currentcfg:
                                print('I---    %0.7f,%d,%d,%d,%x,%x,<%s>,%d' % (state.ts, nodeid, m, round((state.ts - state.stack.time) * CPUFREQUENCY) ,state.currentcfg,state.stack.addr,state.getCfgName(),state.irqmarkers[m].cycles ))
                                tw.marker(state.ts, m, state.stack.addr)
                                state.trace.irqStart(state.ts - (state.irqmarkers[m].cycles + IRQCYCLES) / state.getCpuFreq())
                                state.trace.log(state.inIrq, state.ts, state.stack.addr)
                                state.tracebbcount = state.tracebbcount + 1
                                state.last_marker_ts = state.ts
                                state.frqEst.notifyAmbigeousPath()
                            state.nextCfg()
                        elif state.currentcfg:
                            #try:
                                state.wasinIrq = state.inIrq
                                # check if we expect an indirect call marker
                                if state.stack.expectIndirectCallMarker:
                                    state.stack.expectIndirectCallMarker = False
                                    thismarker = state.indirectcallmarkers[m]
                                    state.addMarkerCycles(thismarker.cycles)
                                    state.pushNewState(CFGState(thismarker.targetAddress, state.ts))
                                    print('----    %0.7f,%d,%d[%s],%d,%x,%x,%x,<%s>,%d' % (state.ts, nodeid, m, marker2gpiostring(m, enc), thismarker.cycles, state.currentcfg,state.stack.addr,newaddr,state.getCfgName(), state.tracebbcount))
                                    state.last_marker_ts = state.ts
                                    state.latentCycles[state.inIrq] = thismarker.latentCycles
                                    state.nextCfg()
                                    if not state.inIrq: # since we expect an indirect call marker, there are no ambigeous paths to resolve, hence irqTime should be neglected
                                        state.irqTime = 0
                                else:                               
                                    path = state.checkTransition(m)
                                    print("path: %s" % hexlist(path))
                                    for bb in path:
                                        state.trace.log(state.inIrq, bb[1], bb[0])
                                        state.tracebbcount = state.tracebbcount + 1
                                    lookup = cfgs[state.currentcfg].pathLookup[(state.stack.lastrealmarker,m)]
                                    state.stack.lastrealmarker = lookup[0]
                                    thismarker = lookup[2]
                                    state.addMarkerCycles(thismarker.cycles)
                                    state.stack.addr = thismarker.targetAddress
                                    assert(state.stack.lastrealmarker == state.stack.addr)
                                    state.stack.marker = state.stack.addr
                                    latentCycles = thismarker.latentCycles
                                    state.stack.cycle = 0
                                    lastmarkertime = state.stack.time
                                    state.stack.time = state.ts
                                    if state.stack.addr in oldtonewprog:
                                        newaddr = oldtonewprog[state.stack.addr]
                                    else:
                                        newaddr = -1
                                    if not isinstance(thismarker, RetMarker): # normal marker
                                        #assert(m>1)
                                        calccycles = round((state.stack.time - lastmarkertime) * state.getCpuFreq()) - thismarker.cycles - state.latentCycles[state.inIrq]
                                        state.stack.isVirtualMarker = False
                                        print('----    %0.7f,%d,%d[%s],%d,%d,[%d],%x,%x,%x,<%s>,%d' % (state.ts, nodeid, m, marker2gpiostring(m, enc), thismarker.cycles, round((state.stack.time - lastmarkertime) * CPUFREQUENCY), calccycles ,state.currentcfg,state.stack.addr,newaddr,state.getCfgName(), state.tracebbcount))
                                        tw.marker(state.ts, m, state.stack.addr)
                                        state.trace.log(state.inIrq, state.ts, state.stack.addr)
                                        state.tracebbcount = state.tracebbcount + 1
                                        state.last_marker_ts = state.ts
                                        state.latentCycles[state.inIrq] = latentCycles
                                        state.nextCfg()
                                    else: # marker is return instruction
                                        #assert(m==1)
                                        lastcfg = state.stack.func
                                        markercycles = thismarker.cycles
                                        calccycles = round((state.stack.time - lastmarkertime) * state.getCpuFreq()) - markercycles - state.latentCycles[state.inIrq]
                                        state.popState()
                                        if state.gpioirq == 1 and lastcfg in vectors: # ret from irq
                                            print('end of interrupt')
                                            assert(len(state.gpiohist[state.gpioirq])==0)
                                            state.gpioirq = 0
                                            state.inIrq = 0
                                            state.irqExitTime = state.ts + latentCycles / state.getCpuFreq()
                                            state.irqTime = state.irqTime + state.irqExitTime - state.irqEnterTime
                                            state.trace.irqEnd(state.irqExitTime)
                                            print('irq time: %0.7f' % state.irqTime)
                                            state.frqEst.notifyAmbigeousPath()
                                        else:
                                            state.stack.time = state.ts
                                            state.last_marker_ts = state.ts
                                        state.stack.isVirtualMarker = False                                   
                                        print('----    %0.7f,%d,%d[%s],%d,%d,[%d],%x,%x,%x,<%s>,%d' % (state.ts, nodeid, m, marker2gpiostring(m, enc), markercycles, round((state.stack.time - lastmarkertime) * CPUFREQUENCY), calccycles, state.currentcfg,state.stack.addr,newaddr,state.getCfgName(), latentCycles))
                                        tw.marker(state.ts, m, state.stack.addr)
                                        tw.callend(state.ts, cfgs[lastcfg].name, lastcfg)
                                        print('last bb in %x was %x' % (state.stack.func, state.stack.addr))
                                        if cfgs[state.currentcfg].bbs[state.stack.addr].isCall and not state.stack.expectIndirectCallMarker:
                                            assert(len(cfgs[state.currentcfg].bbs[state.stack.addr].successors)==1)
                                            print('successor is %x' % cfgs[state.currentcfg].bbs[state.stack.addr].successors[0])
                                            state.stack.addr = cfgs[state.currentcfg].bbs[state.stack.addr].successors[0]
                                            state.stack.cycle = 0
                                            state.stack.marker = state.stack.addr
                                            state.latentCycles[state.inIrq] = latentCycles
                                            state.trace.log(state.inIrq, state.ts, state.stack.addr)
                                            state.tracebbcount = state.tracebbcount + 1
                                            state.nextCfg()
                                if not state.wasinIrq:
                                    state.trace.commit()        
                            #except:
                                #print 'skipping'
                                ##debug = False
                        state.lastmarkertime = state.ts
                    state.lastgpio = state.gpio
                state.lastts = state.ts
                state.ts = time
            if gpiolevel == 1:
                assert(not (gpiobit & state.gpio))
                state.gpio |= gpiobit
            else:
                assert((gpiobit & state.gpio))
                state.gpio &= ~(gpiobit)

            
            count = count + 1
            #if count == 50000:
                #break
                
    state.flushtrace()
    tw.flush()
    print('Total run time: %0.2f s, sleep time %0.2f s, duty cycle %0.2f%%' % (state.ts - state.resettime, state.sleeptime, (state.ts - state.resettime - state.sleeptime )/  (state.ts - state.resettime) * 100), file=sys.stderr)
    print('%d lines, %d time markers, %d non-time markers, %0.2f%% reduction' % (count, state.markercount, state.ntmarkercount, (state.ntmarkercount-state.markercount)/state.ntmarkercount * 100), file=sys.stderr)
    total_markercycles = sum(state.markercyclecount)
    total_programcycles = sum(state.cyclecount)
    print('%d program cycles, %d marker cycles, %0.2f%% overhead' % (total_programcycles, total_markercycles, total_markercycles / (total_markercycles + total_programcycles) * 100), file=sys.stderr)
    meandelay = sum(state.markercyclecount) / len(state.markercyclecount)
    maxdelay = max(state.markercyclecount)
    print('Induced latency: mean %d cycles (%d us), max %d cycles (%d us)' % (meandelay, meandelay * 0.25, maxdelay, maxdelay * 0.25), file=sys.stderr)
    # print stats
    statsfile = open('%s/stats.txt' % workingdir, 'w')
    print('programcycles = %s;' % state.cyclecount, file=statsfile)
    print('markercycles = %s;' % state.markercyclecount, file=statsfile)
    statsfile.close()
        
if __name__ == '__main__':
	main()