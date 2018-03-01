### L. Paulson If-Then-Else normalisation in Coq through Simulated Induction-Recursion

### Copyright

```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*                 [*] Affiliation LORIA -- CNRS              *)
(*                 [+] Affiliation VERIMAG - Univ. Grenoble   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)
```

### What is this repository for? ###

* This repository is a Coq implementation and total correctness
  proof of L. Paulson If-Then-Else normalisation which is a nested
  recursive algorithm with a complicated scheme. The proof of
  partial correctness and termination is postponed after the
  domain and function have been defined together which their
  induction principle and fixpoint equations.

### How do I set it up? ###

* This should compile with Coq 8.6 with `make nm.vo`.
* For Coq 8.7, do not forget `Require Import Extraction.` before extracting code.

### Who do I talk to? ###

* This project was created by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey)
  in collaboration with [Jean François-Monin](http://www-verimag.imag.fr/~monin)

