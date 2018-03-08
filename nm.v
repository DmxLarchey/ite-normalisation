(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*            [*] Affiliation LORIA -- CNRS                   *)
(*            [+] Affiliation VERIMAG - Univ. Grenoble-Alpes  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Export nm_defs     (* Definition of 𝔻 : Ω -> Prop and nm : forall e, 𝔻 e -> Ω by simulated IR *)
               nm_correct  (* Partial correction of nm : when it terminates, nm produces a normal form of its input *)
               nm_domain   (* Termination of nm (i.e. totality of d_nm) *)
               .

Set Implicit Arguments.

Hint Resolve nm_normal nm_equiv.

(* We deduce a fully specified total normalizer *)

Theorem normalize e : { n | e ~Ω n /\ ℕ n }.
Proof. exists (nm _ (d_nm_total e)); auto. Defined.

Recursive Extraction normalize.
