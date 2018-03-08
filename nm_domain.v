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

(** Using the simulated IR definition of 

            𝔻 : Ω -> Prop and nm : forall e, 𝔻 e -> Ω

    we show totality of 𝔻: 
 
      a) we define a measure [.] : Ω -> nat by structural induction

      b) we show that nm preserves the measure, ie

           forall e (De : 𝔻 e), [nm e De] <= [e]

         by dependent induction on De : 𝔻 e

      c) we show that 𝔻 is total
      
           forall e, 𝔻 e 
           
         by induction on [e] : nat
*)

Require Import Arith Omega Wellfounded.

Set Implicit Arguments.

Require Import nm_defs.

Section ce_size.

  Let c x y z := x *(1+y+z).

  (* The next properties are sufficient for the measure *)

  Let c_mono x x' y y' z z' : x <= x' -> y <= y' -> z <= z' -> c x y z <= c x' y' z'.
  Proof. intros; simpl; apply mult_le_compat; omega. Qed.

  Let c_smono_1 x x' y z : x < x' -> c x y z < c x' y z.
  Proof. intro; simpl; apply mult_lt_compat_r; omega. Qed.

  Let c_inc_1 x y z : x <= c x y z.
  Proof. unfold c; rewrite <- Nat.mul_1_r at 1; apply mult_le_compat; omega. Qed.

  Let c_sinc_1 x y z : 0 < x -> 0 < y + z -> x < c x y z.
  Proof. intros ? ?; unfold c; rewrite <- Nat.mul_1_r at 1; apply mult_lt_compat_l; omega. Qed.

  Let c_sinc_2 x y z : 0 < x -> y < c x y z.
  Proof. intros ?; unfold c, lt; rewrite <- Nat.mul_1_l at 1; apply mult_le_compat; omega. Qed.

  Let c_sinc_3 x y z : 0 < x -> z < c x y z.
  Proof. intros ?; unfold c, lt; rewrite <- Nat.mul_1_l at 1; apply mult_le_compat; omega. Qed.

  Let c_special a u v y z : 0 < a -> 0 < y + z -> c a (c u y z) (c v y z) < c (c a u v) y z.
  Proof.
    unfold c; intros ? ?.
    rewrite <- mult_assoc.
    apply mult_lt_compat_l; auto.
    simpl.
    generalize (S (y + z)); intros n.
    rewrite mult_plus_distr_r; omega.
  Qed.

  Reserved Notation "'[' e ']'" (at level 0).

  (** This is the decreasing measure *)

  Fixpoint ce_size e :=
    match e with
      | α => 1
      | ω x y z => c [x] [y] [z]
    end
  where "[ e ]" := (ce_size e).

  (* Some elementary properties of the measure *)

  Local Fact ce_size_mono x x' y y' z z' : 
     [x] <= [x'] -> [y] <= [y'] -> [z] <= [z'] -> [ω x y z] <= [ω x' y' z'].
  Proof. apply c_mono. Qed.

  Local Fact ce_size_smono_1 x x' y z : [x] < [x'] -> [ω x y z] < [ω x' y z].
  Proof. apply c_smono_1. Qed.

  Local Fact ce_size_ge_1 e : 1 <= [e].
  Proof.
    induction e as [ | x Hx y _  z _ ].
    simpl; auto.
    apply le_trans with (1 := Hx), c_inc_1.
  Qed.

  Hint Resolve ce_size_ge_1.

  Local Fact ce_size_sub_1 x y z : [x] < [ω x y z].
  Proof. simpl; apply c_sinc_1; auto; generalize (ce_size_ge_1 y); omega. Qed.

  Local Fact ce_size_sub_2 x y z : [y] < [ω x y z].
  Proof. simpl; apply c_sinc_2; auto. Qed.

  Local Fact ce_size_sub_3 x y z : [z] < [ω x y z].
  Proof. simpl; apply c_sinc_3; auto. Qed.

  (* The special properties that makes it a suitable measure for induction *)

  Local Fact ce_size_special a u v y z : [ω a (ω u y z) (ω v y z)] < [ω (ω a u v) y z].
  Proof. simpl; apply c_special; auto; generalize (ce_size_ge_1 y); omega. Qed.

End ce_size.

Section measure_ind.

  Variables (X : Type) (m : X -> nat) (P : X -> Prop)
            (HP : forall x, (forall y, m y < m x -> P y) -> P x).

  Theorem measure_ind : forall x, P x.
  Proof.
    apply (@well_founded_induction _ (fun x y => m x < m y)); auto.
    apply wf_inverse_image, lt_wf.
  Qed.

End measure_ind.

(* No we finish with the termination/totality of nm *)

Section d_nm_total.

  Notation "'[' e ']'" := (ce_size e) (at level 0).

  Hint Resolve ce_size_sub_2 ce_size_sub_3 ce_size_mono ce_size_smono_1.
  
  (** nm preserves the measure *)

  Local Fact nm_dec e D : [nm e D] <= [e].
  Proof.
    induction D as [ e D1 D2 | | y z D1 ID1 D2 ID2 | u v w y z D1 ID1 D2 ID2 D3 ID3 ].
    - rewrite (nm_pirr _ D1); auto.
    - rewrite nm_fix_0; auto.
    - rewrite nm_fix_1; simpl; omega.
    - rewrite nm_fix_2.
      apply le_trans with (1 := ID3),
            le_trans with (2 := ce_size_special _ _ _ _ _); auto.
  Qed.

  Hint Resolve nm_dec.

  (** Termination/totality by induction on [e] *)

  Theorem d_nm_total e : 𝔻 e.
  Proof.
    induction e as [ [ | [ | u v w ] y z ] IHe ] using (measure_ind ce_size).
    - apply d_nm_0.
    - apply d_nm_1; apply IHe; simpl; omega.
    - assert (D1 : 𝔻 (ω v y z)) by auto.
      assert (D2 : 𝔻 (ω w y z)) by auto.
      apply d_nm_2 with D1 D2.
      apply IHe, le_lt_trans with (2 := ce_size_special _ _ _ _ _); auto.
  Qed.
  
End d_nm_total.
