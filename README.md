## L. Paulson's If-Then-Else normalisation in Coq

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
  | ω (ω(a,b,c),y,z) => nm (ω (a,nm (ω (b,y,z)),nm (ω (c,y,z)))
```

* The proof of partial correctness and termination is postponed after 
  the domain and function have been defined together which their
  constructors, induction principle, proof-irrelevance and fixpoint equations,
  simulating the following Inductive-Recursive definition:

```coq
Inductive Ω : Set := α : Ω | ω : Ω -> Ω -> Ω -> Ω.

Inductive 𝔻 : Ω -> Prop :=
  | d_nm_0 : 𝔻 α
  | d_nm_1 : forall y z, 𝔻 y -> 𝔻 z -> 𝔻 (ω α y z)
  | d_nm_2 : forall a b c y z (Db : 𝔻 (ω b y z)) (Dc : 𝔻 (ω c y z)),
                      𝔻 (ω a (nm (ω b y z) D1) (nm (ω c y z) D2)) 
                   -> 𝔻 (ω (ω a b c) y z)
with Fixpoint nm e (De : 𝔻 e) : Ω := match De with
  | d_nm_0 => α
  | d_nm_1 y z Dy Dz => ω α (nm y Dy) (nm z Dz)
  | d_nm_2 a b c y z Db Dc Da => nm (ω a (nm (ω b y z) Db) (nm (ω c y z) Dc)) Da
end.
```

* The paper [Simulating Induction-Recursion for Partials Algorithms](http://www.loria.fr/~larchey/papers/TYPES_2018_paper_19.pdf)
  submitted to [TYPES 2018](http://w3.math.uminho.pt/types2018) describes the technique. 

### What does it contains

* [`nm_defs.v`](nm_defs.v), definition of `𝔻 : Ω -> Prop` and `nm : ∀e, 𝔻 e -> Ω` by simulated Induction-Recursion;
* [`nm_correct.v`](nm_correct.v), partial correction of `nm`: when it terminates, `nm` produces a normal form of its input;
* [`nm_domain.v`](nm_domain.v), termination of `nm`, that is `∀e, 𝔻  e`;
* [`nm.v`](nm.v), a fully specified normalisation function based on L. Paulson's `nm` algorithm. 

### How do I set it up? ###

* This should compile with Coq 8.6 with `make nm.vo`.
* For Coq 8.7, do not forget `Require Import Extraction.` before extracting code.

### Who do I talk to? ###

* This project was created by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey)
  in collaboration with [Jean François-Monin](http://www-verimag.imag.fr/~monin)

