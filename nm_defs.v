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

  Inductive d_nm : Ω -> Prop :=
    | d_nm_0 : d_nm α
    | d_nm_1 : forall y z, d_nm y -> d_nm z -> d_nm (ω α y z)
    | d_nm_2 : forall a b c y z (Db : d_nm (ω b y z)) (Dc : d_nm (ω c y z)),
                      d_nm (ω a (nm (ω b y z) D1) (nm (ω c y z) D2)) 
                   -> d_nm (ω (ω a b c) y z)
  with Fixpoint nm e (De : d_nm e) : Ω :=
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

  (** The graph g_nm : Ω -> Ω -> Prop of nm 
      with notation x -nm> y for (g_nm x y)
    *)

  Reserved Notation "x '-nm>' y" (at level 70, no associativity).

  Local Inductive g_nm : Ω -> Ω -> Prop :=
    | in_gnm_0 : α -nm> α
    | in_gnm_1 y ny z nz : y -nm> ny -> z -nm> nz -> ω α y z -nm> ω α ny nz
    | in_gnm_2 : forall u v w y z na nb nc, 
                     ω v y z -nm> na 
                  -> ω w y z -nm> nb 
                  -> ω u na nb -nm> nc
                  -> ω (ω u v w) y z -nm> nc
  where "x -nm> y" := (g_nm x y).

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

  Inductive d_nm : Ω -> Prop :=
    | in_dnm_0 : d_nm α
    | in_dnm_1 : forall y z, 
                 d_nm y 
              -> d_nm z 
              -> d_nm (ω α y z)
    | in_dnm_2 : forall a b c y z,
                 d_nm (ω b y z) 
              -> d_nm (ω c y z) 
              ->(forall nb nc, ω b y z -nm> nb  
                           ->  ω c y z -nm> nc 
                           ->  d_nm (ω a nb nc)) 
              -> d_nm (ω (ω a b c) y z).

  Set Elimination Schemes.
  
  Section nm_rec.
  
    (** In the five next lemmas, it is critically important
        that the output domain predicate d_nm is structurally
        simpler (ie. a sub-term) than the input domain predicate
        
        Miraculously, inversion does the job ... this may not be 
        true with older version of the tactic ...
     *)
  
    Let d_nm_inv_1 y z : d_nm (ω α y z) -> d_nm y.
    Proof. inversion 1; trivial. Qed.
    
    Let d_nm_inv_2 y z : d_nm (ω α y z) -> d_nm z.
    Proof. inversion 1; trivial. Qed.
    
    Let d_nm_inv_3 a b c y z : d_nm (ω (ω a b c) y z) -> d_nm (ω b y z).
    Proof. inversion 1; trivial. Qed.
    
    Let d_nm_inv_4 a b c y z : d_nm (ω (ω a b c) y z) -> d_nm (ω c y z).
    Proof. inversion 1; trivial. Qed.
    
    Let d_nm_inv_5 a b c y z nb nc : 
                               d_nm (ω (ω a b c) y z)
                            -> ω b y z -nm> nb
                            -> ω c y z -nm> nc
                            -> d_nm (ω a nb nc).
    Proof. inversion 1; intros; auto. Qed.

    Let nm_rec : forall e, d_nm e -> { n | e -nm> n }.
    Proof.
      refine (fix loop e (De : d_nm e) { struct De } := _); revert De.
      refine (match e as e' return d_nm e' -> sig (g_nm e') with
        | α               => fun De      => exist _ α _
        | ω α y z         => fun De => 
        match loop _ (d_nm_inv_1 De), loop _ (d_nm_inv_2 De) with 
          | exist _ ny Dy, exist _ nz Dz => exist _ (ω α ny nz) _ 
        end
        | ω (ω a b c) y z => fun De =>
        match loop _ (d_nm_inv_3 De), loop _ (d_nm_inv_4 De) with 
          | exist _ nb Db, exist _ nc Dc =>
          match loop _ (d_nm_inv_5 De Db Dc) with
            | exist _ na Da              => exist _ na _
          end
        end
      end). 
      - constructor.
      - constructor; trivial.
      - constructor 3 with nb nc; auto.
    Qed.

    Definition nm e D := proj1_sig (@nm_rec e D).
    
    Fact nm_spec e D : e -nm> @nm e D.
    Proof. apply (proj2_sig _). Qed.

  End nm_rec.

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
  
End nm_def.

Arguments nm e D : clear implicits.
