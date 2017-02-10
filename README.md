Instrumentation and replay for MSP430 based microcontrollers
============================================================

Folder structure
----------------
examples: example ELF files
lib: libraries

Libraries
---------
lib/tracing.py: common classes and functions
lib/elffile: library for elf files, originally from https://bitbucket.org/krp/elffile
lib/coding: library used in elffile, originally from https://bitbucket.org/krp/coding

Main tools
----------
  instrument.py: instruments a given ELF file
  replay.py: converts a recorded GPIO trace to program addresses

Intrumentation
--------------
Usage: instrument.py objfile [list of entry points]                                                                                                                                                  
                                                                                                                                                                                                     
Options:                                                                                                                                                                                             
  -h, --help            show this help message and exit
  -m TIME_METHOD, --method=TIME_METHOD
                        possible methods are: 'none' Ball and Larus without
                        time (default), 'reduction' with time,
                        'none_and_reduction' both
  -U, --uniquemarkers   use globally unique witness identifiers
  -u, --nouniquemarkers
                        reuse witness identifiers (default)
  -C, --cfguniquemarkers
                        use per function unique witness identifiers
  -c, --nocfguniquemarkers
                        reuse witness identifiers (default)
  -t CPU_SPEED_ERROR, --tolerance=CPU_SPEED_ERROR
                        target CPU speed uncertainty in % (default 1%), used
                        for time method
  -b BOUNDFILE, --boundtrace=BOUNDFILE
                        file containing upper bounds on basic block executions
  -l, --handleloops     keep loops between witnesses if possible

Example:
instrument.py -m reduction examples/tinyos_blink.elf
Ouput (in the same directory as the original file):
tinyos_blink.elf.bbcycles   basic blocks with annotated cycle count
tinyos_blink.elf.cycles     cycles and type for each instruction
tinyos_blink.elf.loopbounds 
tinyos_blink.elf.lut        lookup table for replay (used for debugging)
tinyos_blink.elf.markers    information about added witnesses (address, ID, ..)
tinyos_blink.elf.mod.elf    instrumented binary
tinyos_blink.elf.pickle     program structure and witness information used for consecutive passes when instrumenting (python pickled)
tinyos_blink.elf.pickle2    program structure and witness information used when replaying (python pickled)

Replay
------
Usage: replay.py gpiotracefile elffile                                                                                                                                                               
                                                                                                                                                                                                     
Options:                                                                                                                                                                                             
  -h, --help            show this help message and exit                                                                                                                                              
  -s STARTTIME, --start=STARTTIME                                                                                                                                                                    
                        ignore events before this time                                                                                                                                               
  -e ENDTIME, --end=ENDTIME                                                                                                                                                                          
                        ignore events after this time                                                                                                                                                
  -O, --stdin           read event from stdin instead of file                                                                                                                                        
  -t, --tracefile       write trace to trace.txt (text file)                                                                                                                                         
  -b, --binarytracefile                                                                                                                                                                              
                        wite trace tp trace.b (binary file) 

This script expects the pickle2 file to be stored in the same structure as it is generated by the instrumentation (i.e. in the same directory as the original elf).

Limitations
-----------
We tested these tools using msp430-gcc version 4.6.3 20120301. It might work with other compilers.
Depending on the compiler, some code structures might only be handled partially, e.g. case switches in C.

Prerequisites
-------------
Python 3.4.3
networkx 1.11
