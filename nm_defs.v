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

   type Ω = α | ω of Ω*Ω*Ω

   let rec nm e = match e with
     | α                => α
     | ω (α,y,z)        => ω (α,nm y,nm z)
     | ω (ω(a,b,c),y,z) => nm (ω (a,nm(ω(b,y,z)),nm(ω(c,y,z)))

  We simulate the following Inductive/Recursive definition

  Inductive 𝔻 : Ω -> Prop :=
    | d_nm_0 : 𝔻 α
    | d_nm_1 : forall y z, 𝔻 y -> 𝔻 z -> 𝔻 (ω α y z)
    | d_nm_2 : forall a b c y z (Db : 𝔻 (ω b y z)) (Dc : 𝔻 (ω c y z)),
                                            𝔻 (ω a (nm (ω b y z) D1) (nm (ω c y z) D2)) 
                   -> 𝔻 (ω (ω a b c) y z)
  with Fixpoint nm e (De : 𝔻 e) : Ω :=
    match De with
      | d_nm_0 => α
      | d_nm_1 y z Dy Dz => ω α (nm y Dy) (nm z Dz)
      | d_nm_2 a b c y z Db Dc Da => nm (ω a (nm (ω b y z) Db) (nm (ω c y z) Dc)) Da
    end.
*)

Set Implicit Arguments.

Inductive cexpr : Set := At : cexpr | If : cexpr -> cexpr -> cexpr -> cexpr.

Notation α := At.
Notation ω := If.
Notation Ω := cexpr.

Section nm_def.

  (** The graph 𝔾 : Ω -> Ω -> Prop of nm 
      with notation x -nm> y for (g_nm x y)
    *)

  Reserved Notation "x '-nm>' y" (at level 70, no associativity).

  Local Inductive 𝔾 : Ω -> Ω -> Prop :=
    | in_gnm_0 :     α -nm> α
    | in_gnm_1 y ny z nz : 
                     y -nm> ny 
                  -> z -nm> nz 
                  -> ω α y z -nm> ω α ny nz
    | in_gnm_2 : forall u v w y z na nb nc, 
                     ω v y z -nm> na 
                  -> ω w y z -nm> nb 
                  -> ω u na nb -nm> nc
                  -> ω (ω u v w) y z -nm> nc
  where "x -nm> y" := (𝔾 x y).

  Local Fact g_nm_fun e n1 n2 : e -nm> n1 -> e -nm> n2 -> n1 = n2.
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

  Inductive 𝔻 : Ω -> Prop :=
    | in_dnm_0 :                   𝔻 α
    | in_dnm_1 : forall y z,       𝔻 y 
                                -> 𝔻 z 
                                -> 𝔻 (ω α y z)
    | in_dnm_2 : forall a b c y z, 𝔻 (ω b y z) 
                                -> 𝔻 (ω c y z) 
                  ->(forall nb nc, ω b y z -nm> nb  
                                -> ω c y z -nm> nc 
                                -> 𝔻 (ω a nb nc)) 
                                -> 𝔻 (ω (ω a b c) y z).

  Set Elimination Schemes.
  
  Section nm_rec.
  
    (** In the five next lemmas, it is critically important
        that the output domain predicate of type 𝔻 is structurally
        simpler (ie. a sub-term) than the input domain predicate 
        of type 𝔻.

        Miraculously, inversion does the job ... this may not be 
        true with older version of the tactic ...
     *)
  
    Let d_nm_inv_1 y z : 𝔻 (ω α y z) -> 𝔻 y.
    Proof. inversion 1; trivial. Qed.
    
    Let d_nm_inv_2 y z : 𝔻 (ω α y z) -> 𝔻 z.
    Proof. inversion 1; trivial. Qed.
    
    Let d_nm_inv_3 a b c y z : 𝔻 (ω (ω a b c) y z) -> 𝔻 (ω b y z).
    Proof. inversion 1; trivial. Qed.
    
    Let d_nm_inv_4 a b c y z : 𝔻 (ω (ω a b c) y z) -> 𝔻 (ω c y z).
    Proof. inversion 1; trivial. Qed.
    
    Let d_nm_inv_5 a b c y z nb nc : 𝔻 (ω (ω a b c) y z)
                                  -> ω b y z -nm> nb
                                  -> ω c y z -nm> nc
                                  -> 𝔻 (ω a nb nc).
    Proof. inversion 1; intros; auto. Qed.

    (** We give the proof term directly (programming style)
        but it could be built progressively using refine tactics. 
        Using refine is the recommended method. Obtaining the code 
        directly is not for the faint of heart ... even though
        it looks nice in the end. 

        This proof term is a decoration of the OCaml code of nm 
        with extra typing information consisting in:

          1/ a pre-condition De : 𝔻 e which is a termination certificate
          2/ a post-condition relating the input e to the output n : e -nm> n
 
      *)

    Let nm_rec := fix nm_rec e (De : 𝔻 e) {struct De} : { n | e -nm> n } :=
      match e as e' return 𝔻  e' -> sig (𝔾 e') with
        | α               => fun _ => 

                          exist _ α in_gnm_0

        | ω α y z         => fun D => 
          let (ny,Dy) := nm_rec y (d_nm_inv_1 D) in
          let (nz,Dz) := nm_rec z (d_nm_inv_2 D) in

                          exist _ (ω α ny nz) (in_gnm_1 Dy Dz) 

        | ω (ω a b c) y z => fun D =>
          let (nb,Db) := nm_rec (ω b y z)   (d_nm_inv_3 D)       in
          let (nc,Dc) := nm_rec (ω c y z)   (d_nm_inv_4 D)       in
          let (na,Da) := nm_rec (ω a nb nc) (d_nm_inv_5 D Db Dc) in

                          exist _ na (in_gnm_2 Db Dc Da)
      end De.

    Definition nm e D := proj1_sig (@nm_rec e D).
    
    Fact nm_spec e D : e -nm> @nm e D.
    Proof. apply (proj2_sig _). Qed.

  End nm_rec.

  Arguments nm e D : clear implicits.

  Fact d_nm_0 : 𝔻 α.
  Proof. constructor; auto. Qed.

  Fact d_nm_1 y z : 𝔻 y -> 𝔻 z -> 𝔻 (ω α y z).
  Proof. constructor 2; assumption. Qed.

  Fact d_nm_2 u v w y z Dv Dw : 𝔻 (ω u (nm (ω v y z) Dv) (nm (ω w y z) Dw)) 
                             -> 𝔻 (ω (ω u v w) y z).
  Proof.
    constructor 3; auto.
    intros na nb nma nmb. 
    rewrite (g_nm_fun nma (nm_spec Dv)).
    rewrite (g_nm_fun nmb (nm_spec Dw)).
    assumption.
  Qed.
 
  Section d_nm_ind.

    Variables (P : forall e, 𝔻 e -> Prop)
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
  
End nm_def.

Definition 𝔻_ind := d_nm_ind.
Arguments nm e D : clear implicits.

Recursive Extraction nm.
