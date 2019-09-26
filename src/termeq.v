Require Import Omega.
Require Import List.
Require Import Lists.ListTactics.
Require Import Ensembles.
Require Import String.

Definition place := nat.

Inductive term : Type :=
| KIM : nat -> term
| USM : nat -> term
| AT : place -> term -> term
| SEQ : term -> term -> term
| PAR : term -> term -> term
| SIG : term -> term.

Inductive teqR : term -> term -> Prop :=
| E_KIM (x y : nat): 
    x = y ->
    teqR (KIM x) (KIM y)     
| E_USM (x y : nat) : 
    x = y ->
    teqR (USM x) (USM y)
| E_AT (p1 p2 : place) (t1 t2 : term):
    p1 = p2 ->
    teqR t1 t2 ->
    teqR (AT p1 t1) (AT p2 t2)
| E_SEQ (t1 t2 : term) (t3 t4 : term):
    teqR t1 t3 ->
    teqR t2 t4 ->
    teqR (SEQ t1 t2) (SEQ t3 t4)
| E_PAR1 (t1 t2 : term) (t3 t4 : term):
    teqR t1 t3 ->
    teqR t2 t4 ->
    teqR (PAR t1 t2) (PAR t3 t4)
| E_PAR2 (t1 t2 : term) (t3 t4 : term):
    teqR t1 t4 ->
    teqR t2 t3 ->
    teqR (PAR t1 t2) (PAR t3 t4)
| E_SIG (t1 t2 : term) :
    teqR t1 t2 ->
    teqR (SIG t1) (SIG t2).

Compute teqR (KIM 3) (KIM 3).

Hint Constructors teqR. 

Theorem teq_refl : forall t1:term,
    teqR t1 t1.
Proof.
  induction t1.
  - apply E_KIM. reflexivity.
  - apply E_USM. reflexivity.
  - apply E_AT.
    -- reflexivity.
    -- apply IHt1.
  - apply E_SEQ.
    -- apply IHt1_1.
    -- apply IHt1_2.
  - apply E_PAR1.
    -- apply IHt1_1.
    -- apply IHt1_2.
  - apply E_SIG.
    -- apply IHt1.
Qed.

Theorem teq_sym : forall t1 t2:term,
    teqR t1 t2 -> teqR t2 t1.
Proof.
  induction t1; destruct t2; intros; inversion H.
  - apply E_KIM. rewrite <- H2. reflexivity.
  - apply E_USM. rewrite <- H2. reflexivity.
  - apply E_AT.
    -- rewrite <- H3. reflexivity.
    -- apply IHt1.  apply H5. 
  - apply E_SEQ.
    -- specialize IHt1_1 with t2_1. apply IHt1_1. apply H3.
    -- specialize IHt1_2 with t2_2. apply IHt1_2. apply H5. 
  - apply E_PAR1.
    -- specialize IHt1_1 with t2_1. apply IHt1_1. apply H3.
    -- specialize IHt1_2 with t2_2. apply IHt1_2. apply H5.
  - apply E_PAR2.
    -- specialize IHt1_2 with t2_1. apply IHt1_2. apply H5.
    -- specialize IHt1_1 with t2_2. apply IHt1_1. apply H3.
  - apply E_SIG.
    -- apply IHt1. apply H2.
Qed.

Theorem teq_sym2 : forall t1 t2:term,
    teqR t1 t2 = teqR t2 t1.
Proof.
  induction t1.
  - destruct t2. intros. 
    (* apply E_KIM. *)
Admitted.

Theorem teq_trans : forall t1 t2 t3 : term,
    teqR t1 t2 -> teqR t2 t3 -> teqR t1 t3.
Proof.
  induction t1; destruct t2; destruct t3; intros; inversion H; inversion H0.
  - apply E_KIM. rewrite -> H3. apply H6.
  - apply E_USM. rewrite -> H3. apply H6.
  - apply E_AT.
    -- rewrite -> H4. apply H10.
    -- specialize IHt1 with t2 t3. apply IHt1.
       --- apply H6.
       --- apply H12.
  - apply E_SEQ.
    -- specialize IHt1_1 with t2_1 t3_1. apply IHt1_1.
       --- apply H4.
       --- apply H10.
    -- specialize IHt1_2 with t2_2 t3_2. apply IHt1_2.
       --- apply H6.
       --- apply H12.
  - apply E_PAR1.
    --  specialize IHt1_1 with t2_1 t3_1. apply IHt1_1.
       --- apply H4.
       --- apply H10.
    -- specialize IHt1_2 with t2_2 t3_2. apply IHt1_2.
       --- apply H6.
       --- apply H12.
  - apply E_PAR2.
    --  specialize IHt1_1 with t2_1 t3_2. apply IHt1_1.
       --- apply H4.
       --- apply H10.
    -- specialize IHt1_2 with t2_2 t3_1. apply IHt1_2.
       --- apply H6.
       --- apply H12.
  - apply E_PAR2.
     --  specialize IHt1_1 with t2_2 t3_2. apply IHt1_1.
       --- apply H4.
       --- apply H12.
    -- specialize IHt1_2 with t2_1 t3_1. apply IHt1_2.
       --- apply H6.
       --- apply H10.
  - apply E_PAR1.
    -- specialize IHt1_1 with t2_2 t3_1. apply IHt1_1.
       --- apply H4.
       --- apply H12.
    -- specialize IHt1_2 with t2_1 t3_2. apply IHt1_2.
       --- apply H6.
       --- apply H10. 
  - apply E_SIG. specialize IHt1 with t2 t3. apply IHt1.
    -- apply H3.
    -- apply H6.
Qed.


