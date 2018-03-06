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

  Reserved Notation "'[' e ']'" (at level 0).

  (** This is the decreasing measure *)

  Fixpoint ce_size e :=
    match e with
      | α => 1
      | ω x y z => [x] * (1 + [y] + [z])
    end
  where "[ e ]" := (ce_size e).

  Local Fact ce_size_ge_1 : forall e, 1 <= [e].
  Proof.
    refine (fix loop e := _).
    destruct e as [ | [ | u v w ] y z ]; try (simpl; omega).
    simpl.
    change 1 with (1 * 1 * 1).
    do 2 (apply mult_le_compat; try omega).
    apply loop.
  Qed.

  Hint Resolve ce_size_ge_1.

  (** nm preserves the measure *)

  Local Fact nm_dec e D : [nm e D] <= [e].
  Proof.
    induction D as [ e D1 D2 | | y z D1 ID1 D2 ID2 | u v w y z D1 ID1 D2 ID2 D3 ID3 ].
    - rewrite (nm_pirr _ D1); auto.
    - rewrite nm_fix_0; auto.
    - rewrite nm_fix_1; simpl; omega.
    - rewrite nm_fix_2; simpl in * |- *.
      apply le_trans with (1 := ID3).
      rewrite <- mult_assoc.
      apply mult_le_compat_l.
      apply le_trans with (S ((ce_size v + ce_size w) * S (ce_size y + ce_size z))).
      * apply le_n_S; rewrite Nat.mul_add_distr_r; omega.
      * simpl mult at 2; omega.
  Qed.

  (** Termination/totality by induction on [e] *)

  Theorem d_nm_total e : 𝔻 e.
  Proof.
    induction e as [ [ | [ | u v w ] y z ] IHe ] using (measure_ind ce_size).
    - apply d_nm_0.
    - apply d_nm_1; apply IHe; simpl; omega.
    - assert (D1 : 𝔻 (ω v y z)).
      { apply IHe.
        simpl ce_size at 2.
        unfold lt.
        rewrite <- Nat.mul_1_l at 1.
        rewrite <- mult_assoc.
        apply mult_le_compat.
        apply ce_size_ge_1.
        simpl; apply le_n_S.
        generalize ([v]) ([y]) ([z]) ([w]).
        intros a b c d.
        rewrite Nat.mul_add_distr_r.
        generalize (a * S (b+c)) (d*S(b+c)). 
        intros; omega. }
      assert (D2 : 𝔻 (ω w y z)).
      { apply IHe.
        simpl ce_size at 2.
        unfold lt.
        rewrite <- Nat.mul_1_l at 1.
        rewrite <- mult_assoc.
        apply mult_le_compat.
        apply ce_size_ge_1.
        simpl; apply le_n_S.
        generalize ([v]) ([y]) ([z]) ([w]).
        intros a b c d.
        rewrite Nat.mul_add_distr_r.
        generalize (a * S (b+c)) (d*S(b+c)). 
        intros; omega. }
      apply d_nm_2 with D1 D2.
      apply IHe.
      simpl.
      rewrite <- mult_assoc.
      apply mult_lt_compat_l; auto.
      generalize (nm_dec D1) (nm_dec D2).
      simpl ce_size.
      assert (1+1 <= [y] + [z]) as H.
      { generalize (ce_size_ge_1 y) (ce_size_ge_1 z); omega. }
      revert H.
      generalize ([y] + [z]); intros a H H1 H2.
      apply le_lt_trans with (S (([v] + [w])*(S a))).
      apply le_n_S.
      rewrite Nat.mul_add_distr_r; omega.
      simpl mult at 2; omega.
  Qed.
  
End d_nm_total.
