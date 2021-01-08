## Compilation

All required files are specified in `_CoqProject` just run 
```
coq_makefile -f _CoqProject -o Makefile
make
```
## Overview 

This project proves the equivalence between classic and intuitionistic first order logic using deduction predicates defined over modular syntax.

The individual features of the syntax are contained in `*syntax.v` files, which are customized from output of autosubst2, with `syntax.sig` as input.

The deduction predicates, and the instances of lemmas and definitions, are defined feature-wise in `*_deduction.v` files.

The main results are in `core_deduction.v` and `full_deduction.v`, the former using a basic syntax containing only implication, falsity, and universal quantification,
while the latter using the complete syntax.

The development can be found on [github](https://github.com/RobertoAlvz/ModularFOL).
