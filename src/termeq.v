Require Import Omega.
Require Import List.
Require Import Lists.ListTactics.
Require Import Ensembles.
Require Import String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sets.Ensembles.
Require Import Coq.MSets.MSetList.

(* From ~/Docmuments/EECS_research/CoqFolder/PierceBook Require Export Poly. *)

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

Fixpoint teq (t1 t2 : term) : bool :=
match t1, t2 with
| KIM x1, KIM x2 => x1 =? x2
| USM x1, USM x2 => x1 =? x2
| AT p1 x1, AT p2 x2 => andb (p1 =? p2) (teq x1 x2)
| SEQ x1 x2, SEQ x3 x4 => andb (teq x1 x3) (teq x2 x4)
| PAR x1 x2, PAR x3 x4 => if (andb (teq x1 x3) (teq x2 x4)) then true else (andb (teq x2 x3) (teq x1 x4))
| SIG x1, SIG x2 => teq x1 x2
| _, _ => false
end.

Compute teq (PAR (KIM 3) (KIM 4)) (PAR (KIM 4) (KIM 3)).

Theorem plus_1_1 : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

(*Theorem teq_if_teqR : forall t1 t2,
    teqR t1 t2 -> teq t1 t2 = true.
Proof.
  intros t1; induction t1; intros; destruct t2; inversion H.
  - rewrite -> H2. simpl. apply Nat.eqb_eq. reflexivity. 
  - rewrite -> H2. simpl. apply Nat.eqb_eq. reflexivity.
  - simpl. rewrite -> H3. specialize IHt1 with t2. 
    destruct H5. simpl. rewrite -> H5. *)

Theorem teqR_if_teq : forall t1 t2,
    teqR t1 t2 -> teq t1 t2 = true.
Proof.
  intros t1; induction t1; intros; destruct t2; inversion H.   
  - rewrite -> H2. simpl. apply Nat.eqb_refl.
  - rewrite -> H2. simpl. apply Nat.eqb_refl.
  - simpl. destruct (p =? p0) eqn:HA.
    specialize IHt1 with t2. apply IHt1. apply H5.
    rewrite H3 in HA. Search "=?". apply beq_nat_false in HA.
    destruct HA. reflexivity. 
  - simpl. destruct (teq t1_1 t2_1) eqn:HA.
    -- specialize IHt1_2 with t2_2. apply IHt1_2. apply H5.  
    -- destruct HA. apply Bool.andb_true_iff.
       split.
       --- specialize IHt1_1 with t2_1. apply IHt1_1.     
           apply H3.
       --- specialize IHt1_2 with t2_2. apply IHt1_2.     
           apply H5.
  - simpl. Search "||". apply Bool.orb_true_intro. left. 
    Search "&&". apply Bool.andb_true_iff. split. 
    -- specialize IHt1_1 with t2_1. apply IHt1_1. apply H3.      
    -- specialize IHt1_2 with t2_2. apply IHt1_2. apply H5.
  - simpl. Search "||". apply Bool.orb_true_intro. right. 
    Search "&&". apply Bool.andb_true_iff. split. 
    -- specialize IHt1_2 with t2_1. apply IHt1_2. apply H5.      
    -- specialize IHt1_1 with t2_2. apply IHt1_1. apply H3.
 - simpl. specialize IHt1 with t2. apply IHt1. apply H2. 
Qed. 

Theorem teq_if_teqR : forall t1 t2,
    teq t1 t2 = true -> teqR t1 t2.
Proof.
  intros t1; induction t1; intros; destruct t2; inversion H.
  - apply E_KIM. apply Nat.eqb_eq in H1.
    apply H1.
  - apply E_USM. apply Nat.eqb_eq in H1.
    apply H1.  
  - apply E_AT. specialize IHt1 with t2. destruct (p =? p0) eqn:HA.
    apply Nat.eqb_eq in HA. apply HA.
    discriminate.
    specialize IHt1 with t2. apply IHt1.
    destruct (p =? p0) eqn:HA. apply H1. discriminate.
  - apply E_SEQ.
    -- specialize IHt1_1 with t2_1. apply IHt1_1.
    destruct (teq t1_1 t2_1) eqn:HA.
    reflexivity. discriminate.
    -- specialize IHt1_2 with t2_2. apply IHt1_2.
    destruct (teq t1_1 t2_1) eqn:HA.
    apply H1.  discriminate. 
  - apply E_PAR1.
    -- specialize IHt1_1 with t2_1. Search "||". apply Bool.orb_true_iff in H1.
       apply IHt1_1.
       --- Admitted.

Inductive setterm : Type :=
| nil
| cons (t:term) (l:setterm).

Check setterm. 

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

(* evidence is a set of terms *)
(* take the interestion of the two sets 
   then if one set has elements leftover
   after the interestion then we could 
   say that set is "greater" *)
(* want to determine if x is a subclass
   of y *)
Definition setterms1 := (USM 5)::(USM 3)::nil .
Definition setterms2 := (USM 3)::nil. 

Check setterms1.
(*Compute Intersection setterms1 setterms2.*)

Fixpoint setlength (l:setterm) : nat :=
  match l with
  | nil => O
  | h :: t => S (setlength t)
  end.

Fixpoint member (t1:term) (l:setterm) : bool :=
  match t1, l with
  | _ , nil => false
  | t1, h::t => match teq t1 h with
               | true => true
               | false => member t1 t
               end
  end.

(*if s1 is lessthan s2 then return true*)

Definition relation (X: Type) := X -> X -> Prop.

Definition leqR (A: Type) (s1 s2 : Ensemble A) :=
  Included A s1 s2.

Check leqR.
Check leqR: forall (A:Type), Ensemble A -> Ensemble A -> Prop.
(*Check leqR: forall (A:Type), relation Ensemble A.*)

(* Pierce properties of relations REL *)
(* Partial order is relexive, antisymetric, transitive *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem leqR_reflexive : reflexive leqR.

(* Theorem lt_reflex : reflexive lt *)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b)  -> (R b c)  -> (R a c).

Definition symmetric {X: Type} (R: relation X) :=
  ∀a b : X, (R a b)  -> (R b a).

Definition antisymmetric {X: Type} (R: relation X) :=
  ∀a b : X, (R a b) → (R b a) → a = b.

Definition order {X:Type} (R: relation X) :=
  (reflexive R) ∧ (antisymmetric R) ∧ (transitive R).


  
             
       


