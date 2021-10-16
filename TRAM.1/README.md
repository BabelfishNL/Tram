TRAM.1 is an implementation of term rewriting systems.  TRAM.1 is written in standard C using only a few standard libraries. TRAM.1 is small (~650 lines of code). The memory manager and garbage collector are in a certain sense efficient. TRAM.1 contains a naive, handcrafted sunny-day parser (i.e., almost without error handling). The rewrite engine is naive: rules are attempted sequentially without much compilation or optimization.

TRAM.1 is described in more detail in [Beginnings.blog--TRAM.1](https://www.beginnings.blog/trs/tram.1/)

## Distribution
The TRAM.1 distribution at  [Github](https://github.com/BabelfishNL/Tram.git) contains the following files:
* `TRAM.1.c`  
The single C source file. There are no headers; TRAM.1 only includes `stdio.h`,  `stdlib.h` and `stdint.h`.
* `test`  
A **bash** shell script containing many tests. The script
	* creates test files
	* executes TRAM
	* compares the output with expected output
* `Makefile`  
The Makefile handles three commands:
	* `make TRAM` compiles, and is dependent on TRAM.1.c
	* `make test` executes the test script
	* `make clean` removes all files generated by the test script

## Installation
Requirements: `gcc`, `sh`

Execute: `make test`

## Manual

### Tram.1 Syntax
```
TRS:         Rule+ EOF
Rule:        Term '=' Term ';'
Term:        Data
           | Var
           | Sym
           | Sym '(' Term ( ',' Term )* ')'
Data:        '#' '0x' [0-9a-fA-F]+
           | '#' '-'? [0-9]+
           | '\'' . '\''?
Var:         [*&A-Z] [^0-9a-zA-Z]{0-4}
Sym:         [@$a-z] [^0-9a-zA-Z]{0-5}
Whitespace:  [ \n\r\t\v\f]
Comment:     '!' .* \n
```

### Tram.1 Semantics
Tram's semantics is descibed in [Section Term Rewriting](https://www.beginnings.blog/trs/termrewriting/). Tram follows the right-most innermost reduction strategy. That is, 
* given a term, first its right-most innermost sub-term is considered for reduction
* then the left-hand sides of all rules are matched against that sub-term
* rules are attempted in the order in which they have been read, either using the `-P` flag, or in the order of modules (`-p` flag) followed by the order within that module
* if a match is found, and the substitution is established, the corresponding right-hand side is instantiated using that substitution
	* TRAM.1 assumes no variables occur multiple times in the left-hand side. If this occurs, the value matched against the last (right-most) occurence is used
	* TRAM assumes that for every variable in the right-hand side, a value has been matched in the left-hand side. This isn't checked; using a unmatched variable leads to erroneous results
	* The result of this instantiation is further normalised
	* Then, the next right-most innermost term is attempted
* if no match is found, the sub-term is built and the next right-most, innermost sub-term is considered
* this process continues until the entire subject-term has been processed. The result is the now normalised subject term
### TRAM.1 CLI 
TRAM.1 accepts the following CLI arguments
```
      Note that D and X must appear as 1st/2nd cli argument, when used
-D n         generate level n (1..3) debugging info
             Level 0: none
			 Level 1: only I/O (flattens string representations)
			 Level 2: Garbage Collection
			 Level 3: Reduction step information
			 Level 4: Engine cycle information
-X nnn       set memory size to nnn

-P <fname>   Load program
-p <fname>   Load program segment
-C           Compile all segments into one program
      Note that either -P or -p...-p -C should be used
-T <fname>   Read term as subject
-t <fname>   Read sub-term
-s <fname>   Read string sub-term
-b <fname> <todo> Read binary sub-term
-M <fname>   Read meta-term as subject
-m <fname> <todo> Read meta term as sub-term
-I <fname>   dump program
-i <fname>   dump subject term
-r           reduce subject using program
-O <fname>   dump result term
-S <fname> <todo> print result as text
-B <fname> <todo> print result as binary
```

### Formats 
TRAM.1 accepts these input formats:
* Source  
The TRAM.1 source language for terms and term rewriting systems;
* Text  
Any text stream (arbitrary text terminated by EOF). The text "ccccc...", where 'c' are arbitrary characters, is rendered as the term `str('c', str('c', ...str('c',eos)...))`;
* Meta-Source  
This language is the same as the source language with one extension: meta-variables `'%' [0-9]+`. As input is read, each source, text or binary stream is rendered as a sub-term, and is kept in a cache. As a meta-source input is read and the corresponding term is built, each meta-variable `%n` is immediately replaced by the `n`-th previously read term. Example: to transform a text file using some function, TRAM.1 might be called with arguments 
`-P <transformatinProgram> -s <textToTransform> -M <meta>`, where the meta-text is `transform(%1)`.

### Examples
The TRAM.1 distribution contains a large number of examples.

## Beginnings
TRAM.1 is described in more detail in [Beginnings.blog--TRAM.1](https://www.beginnings.blog/trs/tram.1/)