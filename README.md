# ModalZ3

This program has been tested on Windows 8/10 and Ubuntu 20.04.
It compiles at least with GCC 11.1.0 and VC++ 14.20 and 14.30.
The build-files can be generated by CMake 3.18.4 or higher.

# Dependencies

The program depends on the Z3 SMT-solver which can be downloaded from [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3).
As there is a bug in Z3 that may cause Z3 to give wrong results, you have to build it from source. Otw. the bug will be fixed in the version > 4.12.1

You need to put the libz3-library to a path where the program can find it. There are no additional libraries required.

The program can be started from CL. The relevant arguments are

  - -t=ms ... timeout in milliseconds
   - -r   ... run the program on all *.smt2 files in the given directory recursively
   
After these arguments you can give the path to an SMT-LIB file containing the problem or a directory where the program will look for all *.smt2 files

# Input format

The *.smt2 files have to be valid SMT-LIB files.
However, the program will automatically add `(check-sat)` so the input file should only contain the constant/function declarations and assertions. (See `examples` folder for examples)

In addition to the ordinary SMT sorts there is a `World` and a `Relation` sort predefined. (You can just use them as if they are defined in the SMT-LIB standard.)
Furthermore, there are the following additional functions

```
box       : Relation Bool -> Bool         (box operator)
dia       : Relation Bool -> Bool         (diamond operator)
global    : Bool -> Bool                  (global/TBox assertion)
reachable : Relation World World -> Bool  (ABox relations)
trans     : Relation -> Bool              (RBox transitivity)
world     : () -> World                   (current world)
```

We have the additional constraints: `reachable` may not occur nested in either `box`/`dia`/`global`.
`global` and `trans` may only occur as "top-level" assertions.

We may decare as many `Relation` constants as we want and constants/functions that have `World`-sorted paramter at the first position. This makes the respective symbol depending on the world.

e.g.,
```
(declare-fun p (World) Bool)
(declare-const w1 World)
(declare-const r Relation)
(assert (and (p w1) (dia r (p world))))
```
This can be read as "`p` is true in world `w1` and there is a r-reachable world from my initial world (implicitly `w0`) in which `p` is true". For more examples see the `examples` folder.

In our implementation we can express all problems of the S-description logic and additionally connectives over ABoxes (e.g., `(or (p w1) (p w2))`).
