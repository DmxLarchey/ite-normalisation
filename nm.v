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

(** From verify.rwth-aachen.de/giesl/papers/ibn96-30.ps

   type cexpr = at | if of cexpr*cexpr*cexpr

   let rec nm e = match e with
     | at          => at
     | if (at,y,z) => if (at,nm y,nm z)
     | if (if(u,v,w),y,z) => nm (if (u,nm(if(v,y,z)),nm(if(w,y,z)))

  We simulate the following Inductive/Recursive definition

  Inductive d_nm : cexpr -> Prop :=
    | d_nm_0 : d_nm α
    | d_nm_1 : forall y z, d_nm y -> d_nm z -> d_nm (ω α y z)
    | d_nm_2 : forall u v w y z (D1 : d_nm (ω v y z)) (D2 : d_nm (ω w y z)),
                      d_nm (ω u (nm (ω v y z) D1) (nm (ω w y z) D2)) 
                   -> d_nm (ω (ω u v w) y z)
  with Fixpoint nm e (D : d_nm e) : cexpr :=
    match D with
      | d_nm_0 => α
      | d_nm_1 y z Dy Dz => ω α (nm y Dy) (nm z Dz)
      | d_nm_2 u v w y z Dv Dw Du => nm (ω u (nm (ω v y z) Dv) (nm (ω w y z) Dw)) Du
    end.

  Then we show partial correctness:
    a) if De : d_nm e then nm e De is normal
    b) if De : d_nm e then nm e De is equivalent to e
  by induction on De

  Then we show totality: 
    a) for some given size measure |e| : nat, we have 
         forall e (De : d_nm e), |nm e De| <= |e|
       by induction on De
    b) forall e, d_nm e by induction on |e|

*)

Require Import Arith Omega Wellfounded.

Set Implicit Arguments.

Section measure_rect.

  Variables (X : Type) (m : X -> nat) (P : X -> Type)
            (HP : forall x, (forall y, m y < m x -> P y) -> P x).

  Theorem measure_rect : forall x, P x.
  Proof.
    apply (@well_founded_induction_type _ (fun x y => m x < m y)); auto.
    apply wf_inverse_image, lt_wf.
  Qed.

End measure_rect.

Definition measure_rec X m (P : X -> Set) := @measure_rect X m P.
Definition measure_ind X m (P : X -> Prop) := @measure_rect X m P.

Section nm.

  Inductive cexpr : Set := At : cexpr | If : cexpr -> cexpr -> cexpr -> cexpr.

  Notation α := At.
  Notation ω := If.

  Reserved Notation "x '-nm>' y" (at level 70, no associativity).

  Inductive g_nm : cexpr -> cexpr -> Prop :=
    | in_gnm_0 : α -nm> α
    | in_gnm_1 y ny z nz : y -nm> ny -> z -nm> nz -> ω α y z -nm> ω α ny nz
    | in_gnm_2 : forall u v w y z na nb nc, 
                     ω v y z -nm> na 
                  -> ω w y z -nm> nb 
                  -> ω u na nb -nm> nc
                  -> ω (ω u v w) y z -nm> nc
  where "x -nm> y" := (g_nm x y).

  Fact g_nm_fun e n1 n2 : e -nm> n1 -> e -nm> n2 -> n1 = n2.
  Proof.
    intros H; revert H n2.
    induction 1 as [ 
                   | y ny z nz H1 IH1 H2 IH2
                   | u v w y z na nb nc H1 IH1 H2 IH2 H3 IH3 ]; inversion 1; subst; auto.
    - f_equal; auto.
    - apply IH1 in H9; subst.
      apply IH2 in H10; subst.
      apply IH3 in H11; subst.
      auto.
  Qed.

  Unset Elimination Schemes.

  Inductive d_nm : cexpr -> Prop :=
    | in_dnm_0 : d_nm α
    | in_dnm_1 : forall y z, d_nm y -> d_nm z -> d_nm (ω α y z)
    | in_dnm_2 : forall a b c y z,
                 d_nm (ω b y z) 
              -> d_nm (ω c y z) 
              ->(forall nb nc, ω b y z -nm> nb  
                           ->  ω c y z -nm> nc 
                           ->  d_nm (ω a nb nc)) 
              -> d_nm (ω (ω a b c) y z).

  Set Elimination Schemes.
  
  Section nm.

    Let nm_rec : forall e, d_nm e -> { n | e -nm> n }.
    Proof.
      refine (fix loop e De { struct De } := _).
      revert De.
      refine (match e as e' return d_nm e' -> sig (g_nm e') with
        | α               => fun De => _
        | ω α y z         => fun De => _
        | ω (ω a b c) y z => fun De => _
      end); clear e.

      - exists α; constructor.
    
      - refine (match @loop y _ with exist _ ny Dy => _ end).
        { inversion De; assumption. }
        cbn in Dy. 
        refine (match @loop z _ with exist _ nz Dz => _ end).
        { inversion De; assumption. }
        cbn in Dz. 
        exists (ω α ny nz).
        subst; constructor; assumption.

      - refine (match @loop (ω b y z) _ with exist _ nb Db => _ end).
        { inversion De; assumption. }
        cbn in Db. 
        refine (match @loop (ω c y z) _ with exist _ nc Dc => _ end).
        { inversion De; assumption. }
        cbn in Dc.
        refine (match @loop (ω a nb nc) _ with exist _ na Da => _ end).
        { inversion De; auto. }
        exists na.
        subst; constructor 3 with nb nc; assumption. 
    Qed.

    Definition nm e D := proj1_sig (@nm_rec e D).
    
    Fact nm_spec e D : e -nm> @nm e D.
    Proof. apply (proj2_sig _). Qed.

  End nm.

  Arguments nm e D : clear implicits.

  Fact d_nm_0 : d_nm α.
  Proof. constructor; auto. Qed.

  Fact d_nm_1 y z : d_nm y -> d_nm z -> d_nm (ω α y z).
  Proof. constructor 2; assumption.  Qed.

  Fact d_nm_2 u v w y z Dv Dw :
       d_nm (ω u (nm (ω v y z) Dv) (nm (ω w y z) Dw)) -> d_nm (ω (ω u v w) y z).
  Proof.
    constructor 3; auto.
    intros na nb nma nmb. 
    rewrite (g_nm_fun nma (nm_spec Dv)).
    rewrite (g_nm_fun nmb (nm_spec Dw)).
    assumption.
  Qed.
 
  Section d_nm_ind.

    Variables (P : forall e, d_nm e -> Prop)
              (HPi : forall e D1 D2, @P e D1 -> @P e D2)
              (HP0 : P d_nm_0)
              (HP1 : forall y z D1 (_ : P D1) D2 (_ : P D2), P (@d_nm_1 y z D1 D2))
              (HP2 : forall u v w y z D1 (_ : P D1) D2 (_ : P D2) D3 (_ : P D3), P (@d_nm_2 u v w y z D1 D2 D3)).

    Fixpoint d_nm_ind e D { struct D } : @P e D.
    Proof.
      destruct D as [ | y z Dy Dz | a b c y z Db Dc Da ].
      - apply HPi with (1 := HP0).
      - apply HPi with (1 := HP1 (d_nm_ind _ Dy) (d_nm_ind _ Dz)).
      - generalize (Da _ _ (nm_spec Db) (nm_spec Dc)); intro Da'. 
        apply HPi with (1 := HP2 (d_nm_ind _ Db) (d_nm_ind _ Dc) (d_nm_ind _ Da')).
    Qed.

  End d_nm_ind.

  Fact nm_pirr e D1 D2 : nm e D1 = nm e D2.
  Proof. apply g_nm_fun with e; apply nm_spec. Qed.

  Fact nm_fix_0 : nm α d_nm_0 = α.
  Proof. apply g_nm_fun with α; [ | constructor ]; apply nm_spec. Qed.

  Fact nm_fix_1 y z D1 D2 : nm (ω α y z) (d_nm_1 D1 D2) = ω α (nm y D1) (nm z D2).
  Proof. apply g_nm_fun with (ω α y z); [ | constructor ]; apply nm_spec. Qed.

  Fact nm_fix_2 u v w y z D1 D2 D3 : 
            nm (ω (ω u v w) y z) (d_nm_2 D1 D2 D3) 
          = nm (ω u (nm (ω v y z) D1) (nm (ω w y z) D2)) D3.
  Proof. 
    apply g_nm_fun with (ω (ω u v w) y z).
    apply nm_spec.
    constructor 3 with (nm _ D1) (nm _ D2); apply nm_spec.
  Qed.

  (* Now we show the partial correctness of nm, independently of its termination *)

  Inductive normal : cexpr -> Prop :=
    | in_normal_0 : normal α
    | in_normal_1 : forall y z, normal y -> normal z -> normal (ω α y z).

  (* nm produces normal forms *)

  Theorem nm_normal e D : normal (@nm e D).
  Proof.
    induction D as [ e D1 D2 | | y z D1 ID1 D2 ID2 | u v w y z D1 ID1 D2 ID2 D3 ID3 ].

    rewrite (nm_pirr _ D1); auto.
    rewrite nm_fix_0; constructor.
    rewrite nm_fix_1; constructor; auto.
    rewrite nm_fix_2; auto.
  Qed.

  (** equiv is the congruence generated by

         ite (ite u v w) y z ~e ite u (ite v y z) (ite w y z)

    *)

  Reserved Notation "x '~e' y" (at level 70, no associativity).

  Inductive equiv : cexpr -> cexpr -> Prop :=
    | in_eq_0 : forall u v w y z, ω (ω u v w) y z ~e ω u (ω v y z) (ω w y z)
    | in_eq_1 : forall x x' y y' z z', x ~e x' -> y ~e y' -> z ~e z'-> ω x y z ~e ω x' y' z'
    | in_eq_2 : α ~e α
    | in_eq_3 : forall x y z, x ~e y -> y ~e z -> x ~e z
  where "x ~e y" := (equiv x y).

  Hint Constructors equiv.

  Fact equiv_refl e : e ~e e.
  Proof. induction e; auto. Qed.

  Hint Resolve equiv_refl.

  Notation equiv_trans := in_eq_3.

  (* nm preserves equivalence *)

  Fact nm_equiv e D : e ~e nm e D.
  Proof.
    induction D as [ e D1 D2 | | y z D1 ID1 D2 ID2 | u v w y z D1 ID1 D2 ID2 D3 ID3 ].

    rewrite (nm_pirr _ D1); auto.
    rewrite nm_fix_0; auto.
    rewrite nm_fix_1; auto.
    rewrite nm_fix_2.
    apply equiv_trans with (2 := ID3),
          equiv_trans with (1 := in_eq_0 _ _ _ _ _); auto.
  Qed.

  (* We finish with the termination of nm *)

  Reserved Notation "'[' e ']'" (at level 0).

  Fixpoint ce_size e :=
    match e with
      | α => 1
      | ω x y z => [x] * (1 + [y] + [z])
    end
  where "[ e ]" := (ce_size e).

  Fact ce_size_ge_1 : forall e, 1 <= [e].
  Proof.
    refine (fix loop e := _).
    destruct e as [ | [ | u v w ] y z ]; try (simpl; omega).
    simpl.
    change 1 with (1 * 1 * 1).
    do 2 (apply mult_le_compat; try omega).
    apply loop.
  Qed.

  Hint Resolve ce_size_ge_1.

  Fact nm_dec e D : [nm e D] <= [e].
  Proof.
    induction D as [ e D1 D2 | | y z D1 ID1 D2 ID2 | u v w y z D1 ID1 D2 ID2 D3 ID3 ].

    rewrite (nm_pirr _ D1); auto.
    rewrite nm_fix_0; auto.
    rewrite nm_fix_1; simpl; omega.

    rewrite nm_fix_2; simpl in * |- *.
    apply le_trans with (1 := ID3).
    rewrite <- mult_assoc.
    apply mult_le_compat_l.
    apply le_trans with (S ((ce_size v + ce_size w) * S (ce_size y + ce_size z))).
    apply le_n_S.
    rewrite Nat.mul_add_distr_r; omega.
    simpl mult at 2; omega.
  Qed.

  (* Termination/totality by induction on [e] *)

  Theorem d_nm_total e : d_nm e.
  Proof.
    induction e as [ [ | [ | u v w ] y z ] IHe ] using (measure_ind ce_size).
    apply d_nm_0.
    apply d_nm_1; apply IHe; simpl; omega.

    assert (D1 : d_nm (ω v y z)).
      apply IHe.
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
      intros; omega.
   assert (D2 : d_nm (ω w y z)).
      apply IHe.
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
      intros; omega.
    apply d_nm_2 with D1 D2.
    apply IHe.
    simpl.
    rewrite <- mult_assoc.
    apply mult_lt_compat_l.
    2: apply ce_size_ge_1.
    generalize (nm_dec D1) (nm_dec D2).
    simpl ce_size.
    assert (1+1 <= [y] + [z]) as H.
      generalize (ce_size_ge_1 y) (ce_size_ge_1 z); omega.
    revert H.
    generalize ([y] + [z]); intros a H H1 H2.
    apply le_lt_trans with (S (([v] + [w])*(S a))).
    apply le_n_S.
    rewrite Nat.mul_add_distr_r; omega.
    simpl mult at 2; omega.
  Qed.

  Theorem normalize e : { n | normal n /\ e ~e n }.
  Proof.
    exists (nm _ (d_nm_total e)); split.
    apply nm_normal.
    apply nm_equiv.
  Defined.
 
End nm.

Recursive Extraction normalize.
