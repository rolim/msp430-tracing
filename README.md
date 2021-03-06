Instrumentation and replay for MSP430 based microcontrollers
============================================================

These tools can be used to instrument an MSP430 program binary to emit
witness identifiers on a I/O port. This implementation specifically targets
the Tmote Sky node \[1\]. Trace can be recorded using FlockLab \[2\] (or a logic analyzer).
More information about the instrumentation algorithm is provided in \[3\].

This implementation serves as a proof of concept. Feel free to use it at your own risk.
Contributions are always welcome.

Folder structure
----------------
* examples: example ELF files
* lib: libraries

Libraries
---------
* lib/tracing.py: common classes and functions
* lib/elffile: library for elf files, originally from https://bitbucket.org/krp/elffile
* lib/coding: library used in elffile, originally from https://bitbucket.org/krp/coding

Main tools
----------
* instrument.py: instruments a given ELF file
* replay.py: converts a recorded GPIO trace to program addresses

Instrumentation
--------------
```
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
```

Example:
```
instrument.py -m reduction examples/tinyos_blink.elf
```
Output (in the same directory as the original file):

* tinyos_blink.elf.bbcycles   basic blocks with annotated cycle count
* tinyos_blink.elf.cycles     cycles and type for each instruction
* tinyos_blink.elf.loopbounds 
* tinyos_blink.elf.lut        lookup table for replay (used for debugging)
* tinyos_blink.elf.markers    information about added witnesses (address, ID, ..)
* tinyos_blink.elf.mod.elf    instrumented binary
* tinyos_blink.elf.pickle     program structure and witness information used for consecutive passes when instrumenting (python pickled)
* tinyos_blink.elf.pickle2    program structure and witness information used when replaying (python pickled)

Following I/O pins are used to encode witnesses: P6.0, P6.1, P6.2, P6.6, P6.7

Replay
------
```
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
                        write trace to trace.b (binary file) 
```

This script expects the pickle2 file to be stored in the same structure as it is generated by the instrumentation (i.e. in the same directory as the original elf).

Compiling ELF files
-------------------
In order to handle relocations during instrumentation properly, binaries should be compiled using
```
LDFLAGS += -Wl,-q
```

Limitations
-----------
We tested these tools using msp430-gcc version 4.6.3 20120301. It might work with other compilers.
Depending on the compiler, some code structures might only be handled partially, e.g. case switches in C.

Prerequisites
-------------
* Python 3.4.3
* networkx 1.11

References
----------
* [1] Moteiv Corporation, Tmote Sky : Datasheet 
* [2] http://flocklab.ethz.ch/
* [3] Roman Lim and Lothar Thiele: Testbed Assisted Control Flow Tracing for Wireless Embedded Systems, Proceedings of the 14th International Conference on Embedded Wireless Systems and Networks (EWSN 2017), Uppsala, Sweden
