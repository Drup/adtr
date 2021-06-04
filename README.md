# ADT rewriting

ADTs are generally represented by a spaghetti plate of pointers, for each
constructors of the algebraic data type. Furthermore, they are generally
manipulated persistently, by allocating new constructors.

This is an attempt at representing ADTs in a flat way and compiling a 
pattern match-like construction as a rewrite on the memory representation.
The goal is to then use this representation to optimize the rewriting and 
exploit parallelism.

## To compile:
```
opam install --deps .
make
```

## To run the tests
```
make test
```

## Run only one file
```
dune exec adtr -m batch path/to/file
```

You can use `--dot` to get dot files of the dependency graphs of the rewrite operations.
