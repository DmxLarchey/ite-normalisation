### L. Paulson's If-Then-Else normalisation in Coq through Simulated Induction-Recursion

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
  recursive algorithm with a complicated scheme.

```ocaml
type Ω = α | ω of Ω * Ω * Ω

let rec nm e = match e with
  | α                => α
  | ω (α,y,z)        => ω (α,nm y,nm z)
  | ω (ω(a,b,c),y,z) => nm (ω (a,nm(ω(b,y,z)),nm(ω(c,y,z)))
```

* The proof of partial correctness and termination is postponed after 
  the domain and function have been defined together which their
  constructors, induction principle, proof-irrelevance and fixpoint equations.

* The paper [Simulating Induction-Recursion for Partials Algorithms](http://www.loria.fr/~larchey/papers/TYPES_2018_paper_19.pdf)
  submitted to [TYPES 2018](http://w3.math.uminho.pt/types2018) describes the technique. 

### What does it contains

* `nm_defs.v`, definition of `𝔻 : Ω -> Prop` and `nm : forall e, 𝔻 e -> Ω` by simulated Induction-Recursion;
* `nm_correct.v`, partial correction of `nm`: when it terminates, `nm` produces a normal form of its input;
* `nm_domain.v`, termination of `nm`, i.e. totality of `d_nm`;
* `nm.v`, a fully specified normalisation function based on L. Paulson's `nm` algorithm. 

### How do I set it up? ###

* This should compile with Coq 8.6 with `make nm.vo`.
* For Coq 8.7, do not forget `Require Import Extraction.` before extracting code.

### Who do I talk to? ###

* This project was created by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey)
  in collaboration with [Jean François-Monin](http://www-verimag.imag.fr/~monin)

