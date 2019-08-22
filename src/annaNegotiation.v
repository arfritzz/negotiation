Require Import Omega.
Require Import List.
Require Import Lists.ListTactics.
Require Import Ensembles.
Require Import String.
(* Require Import PartialMap. *)
(*Require Import Poset.*)

(* Before understanding a request, a SA must
   be established using ISAKMP. The goal of
   ISAKMP is to define a procedure for authenticating
   a communicating peer as well as a procedure for key
   generation techniques.

   This is done through a series of headers that describe
   the payload types, and exchange types

 *)

(* Coq Inductive terms are used to create a data structure *)

Inductive SA : Type :=
| authMethod (a : string)
| encrypMethod (e : string)
| HMAC (h : string)
| DHgroup (g : nat)
| time (t : nat).


(* What can you prove about SA??*)
(* I want the security association to produce 
   a natural number, like that is is signed by a natural
   number. How do I do that? *)

Definition place := nat.

Inductive term : Type :=
| KIM : nat -> term
| USM : nat -> term
| AT : place -> term -> term
| SEQ : term -> term -> term
| PAR : term -> term -> term
| SIG : term -> term.

Check term.

Definition myterm1 := (KIM 3).
Definition myterm2 := (AT 4 (USM 4)).
Definition myterm3 := (SIG (KIM 3)).
Definition myterm4 := (SEQ (KIM 3)).
Definition myterm5 := (PAR (SIG (USM 4))).

(* A request is generated by the appraiser and 
   holds something in it. It is not necessarily evidence yet
   but something else that dictates was the appraiser wants
   to know about the target. For now, I will say that the request
   is composed of certificates that enforce the privacy policy
   of the appraiser. *)

(*Inductive request (term : Type) := 
| EV : term -> (request term)
| SUM : term -> (request term) -> (request term)
| PROD : term -> (request term) -> (request term). *)

(* I built a data structure with a base type of evidence
   where it can be composed of evidence as a sum
   or product. Still unsure how this differs from
   the other type of Inductive request definition *)

Inductive request : Type :=
| EV (t : term)
| SUM (t1 t2 : request)
| PROD (t1 t2 : request).      
    
(* We have now defined request as type SET
 *)

Definition protocol := term.

Check request.

Definition myrequest1 := EV (myterm1).
Definition myrequest := EV (myterm3).
Definition myrequest2 := SUM (myrequest1) (myrequest).
(*Definition myrequest3 := request (myterm1).*)

Definition myprotocol1 := PAR (KIM 3) (USM 3).

(* A protocol is  a list of terms 
   But those terms can be arranged in certain ways
   like parallel execution, *)

Definition proposal := list protocol.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* What about examples of protocols? *)
(* Not sure which definition works? *)

(* Definition proposal := (request) -> protocol. *)

(* Options to match a request with are nothing,
   evidence, sum, product. 

   When nothing, go to the empty list, otherwise, 
   add to the front of the list.
 *)

Inductive id : Type :=
| ID (r : request).

Check id.

(* Definition eqb_id (t1 t2 : id) :=
  match t1, t2 with
  | ID t1, ID t2 => Same_set t1 t2
  end. *)

(* Two ways to construct partial map, either empty or using record with an existing 
   partial map to construct a key-to-value mapping *)

(* For now, we will request a term. The map will be built upon terms that can be requested.
   You can look up the requested term in the map and the request protocol will be 
   returned. *)

Inductive partial_map : Type :=
| empty
| record (i : id) (p : protocol) (m : partial_map).

(* Where each entry of the map is
   an ID that is the request *)

(* For now we will assume there is only 
   one term being requested at a time *)

Definition my_partial_map_base := record (ID (EV (KIM 3))) ((KIM 3)) (empty).
Check my_partial_map_base.

Definition update (d: partial_map) (i : id) (t_value : protocol) : partial_map :=
  record i t_value d.

Definition my_partial_map_1 := update (my_partial_map_base) (ID (EV (USM 3))) (SEQ (USM 3) (KIM 3)).

(* Now we need to be able to find the value with the key. *)

Inductive requestoption : Type :=
| Some (t : request)
| None.

(* Now we need the option to return none. This can be done by seeing 
   if the two terms are equal. But we need an equality function to 
   tell if they are the same where the equality function returns
   the bool true if they are the same. *)

(* term is of the type SET. What equality relations hold over 
   set? *) 

Check request.

Definition conditional_eq {A} (x y : A) := x = y.
Check conditional_eq.

(* Definition eq_request (r1 r2 : request) := forall a : term , In a r1 <-> In a r2. *)

Definition eq_term (t1 t2 : term) : bool :=
match t1 with
| KIM x1 => match t2 with
            | KIM x2 => if eqb x1 x2 then true else false
            | _ => false
            end.
| USM x1  => match t2 with
            | USM x2 => if eqb x1 x2 then true else false
            | _ => false
            end.
(* | AT : place -> term -> term *)
| SEQ : term -> term -> term
| PAR : term -> term -> term
| SIG : term -> term.
end.

| KIM : nat -> term
| USM : nat -> term
| AT : place -> term -> term
| SEQ : term -> term -> term
| PAR : term -> term -> term
| SIG : term -> term.

Definition eq_request (r1 r2 : request) : bool :=
  match r1 with
  | EV x1 => match r2 with
               | EV x2 => 
  | SUM x1 x2 
  | PROD x1 x2
         
                   

Fixpoint find (x : id) (d : partial_map) : requestoption :=
  match d with
  | empty => None
  | record y r d' => if eqb_id x y
                     then Some r
                     else find x d'
  end.

(* to match the map option, we must, for now, just say the request is some
   natural number. *)



Fixpoint evalrequest (r : request) : proposal :=
  match r with
  | EV r1 => [r1]
  | SUM r1 r2 => 
  end.

(* How does request shape into the list?? *)

(* If I wanted to say "Compute request 5" idk how to do that
   or where I defined these things in this language. 
  
   Somewhere in PLUS someone came up with the notition of 
   (S (S n)) but where/how did they think to do this? *)

(* After a proposal is generated, the appraiser must then select 
   the appropriate protocol for the attestation manager. 
   This implies there must be some notion of best and some
   notion of worst and that the protocols must be ordered.

   This brings me back to my inital thoughts that I have no idea
   where the notion of ordering should begin. Somehow we must 
   define a hierarcy of protocols in order to make the 
   decision. Maybe a function is the best way to go about 
   establishing an ordering. *)

