Require Import Unicode.Utf8.
Require Import Utf8_core.
Require Import List.
Require Import Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Powerset_facts.
Require Import Coq.Sets.Constructive_sets.

(*
 This is how we say  " { (f a) | a in x } "
 Taken from http://www.alumnos.unican.es/ccc66/coq/EnsembleFacts.v
*)
(***********************)
Inductive apply_func (U1 U2:Type) (f:U1->U2) (S:Ensemble U1)
: Ensemble U2 :=
|In_apply_func: forall a:U1, In U1 S a->
  In U2 (apply_func U1 U2 f S) (f a).


Lemma apply_func_rec : forall (U1 U2:Type) (f:U1->U2)
(S:Ensemble U1) (a:U2),
In U2 (apply_func U1 U2 f S) a ->
exists ia:U1, In U1 S ia /\ f ia=a.
intros.
inversion H.
exists a0.
split.
assumption.
tauto.
Qed.

(*
  f({}) = {} (Empty sets remain empty when we map them.)
*)
Theorem apply_func_empty : forall (U1 U2:Type) (f:U1->U2)
(S:Ensemble U1),
 (apply_func U1 U2 f (Empty_set U1)) = Empty_set U2.
Proof.
intros.
apply Extensionality_Ensembles.
unfold Same_set.
split.
unfold Included.
intros.
inversion H.
inversion H0.
unfold Included.
intros.
inversion H.
Qed.

(***********************)

(*
  Notice the added (E t) term.
*)
Inductive term : Set :=
  | bottom : term
  | var : nat → term
  | e : term → term
  | k :  nat →  term → term
  | c : term → term
  | impl : term → term → term
  | and : term → term → term  
  | or : term → term → term.


(* 
  Helper definition for sets of terms.
*)
Definition Forms := Ensemble term.

Definition Si (t : term) : Forms := Singleton term t.
Definition In_si (t : term) : In term (Si t) t := In_singleton term t.
Definition EmptyE : Ensemble term := Empty_set term.
Definition Ut (u : Forms) (v : Forms) : Forms := Union term u v.
Definition Compt (x : Forms) (f : term -> term) : Forms :=
  apply_func term term f x.



(*
  The most important definition:   The Phi  ⊃  t 
*)
Definition Ent (x : Forms) (y : term) := Prop.


Notation "A ⊃ B" := (Ent A B)  (at level 0, no associativity).
Notation "A |_| B" := (Ut A B) (at level 50, left associativity).

Inductive Axb (a : term) (x : Forms) : (x ⊃ a) :=
 AxbE : Axb a x.
Inductive Axi (a : term) (x : Forms) : ((Ut x (Si a)) ⊃ a) :=
 AxiE : Axi a x.
Inductive EFix (i : nat) (a : term) (x : Forms) : (Ut x (Si (e a))) ⊃ (k i a) :=
EFixE : EFix i a x.
Inductive EFixR (i : nat) (a : term) (x : Forms) (v : (x ⊃ (e a))) :
  (x ⊃ (k i a)) :=
EFixRE : EFixR i a x v.
Inductive EFixL (i : nat) (a b : term) (x : Forms) (v : (Ut x (Si (e a))) ⊃ b) :
  ((Ut x (Si (k i a))) ⊃ b) :=
EFixLE : EFixL i a b x v.

Inductive Cut (a b : term) (x : Forms) (u : (x ⊃ a)) (v : ((Ut x (Si a)) ⊃ b)) :
   (x ⊃ b) :=
CutE : Cut a b x u v.

Inductive OrL (a b c : term) (x : Forms) 
  (u : (Ut x (Si a))  ⊃ c)  
  (v : (Ut x (Si b))  ⊃ c) : ((Ut x (Si (or a b)))  ⊃ c) :=
OrLE : OrL a b c x u v.


Inductive OrR1 (a b : term) (x : Forms) (u : (x ⊃ a)) : x ⊃ (or a b) :=
OrR1E : OrR1 a b x u.

Lemma triv : forall (a : term), (Si a) ⊃ a.
intros.
exact (Axi a (Si a) ).
Defined.
Inductive OrR2 (a b : term) (x : Forms) (u : (x ⊃ a)) : x ⊃ (or b a) :=
OrR2E : OrR2 a b x u.



Inductive AndL (a b c : term) (x : Forms) (u : (Ut (Ut x (Si a)) (Si b))  ⊃ c) : 
  (Ut x (Si (and a b)))  ⊃ c :=
AndLE : AndL a b c x u.


Lemma triv_orl2 : forall (a b : term), (Si a) ⊃ (or a b).
intros.
apply OrR1.
apply triv.
Defined.

Lemma xx : forall (a b c : term), 
  ((Ut (Si a) (Si b)) ⊃ c)
  -> ((Si (and a b)) ⊃ c).
intros.
apply (AndL a b c0 (EmptyE) X).
Defined.

Inductive AndR (a b : term) (x : Forms) 
  (u : (x ⊃ a)) (v : (x ⊃ b)) : 
    (x ⊃ (and a b)) :=
AndRE : AndR a b x u v.


Inductive ImplL (a b c : term) (x : Forms) 
  (u : (x ⊃ a)) 
  (v : ((Ut x (Si b)) ⊃ c)) : 
    (Ut x (Si (impl a b))) ⊃ c :=
ImplLE : ImplL a b c x u v.

Inductive ImplR (a b : term) (x : Forms) (u : (Ut x (Si a)) ⊃ b) : 
  (x ⊃ (impl a b)) :=
ImplRe : ImplR a b x u.


(*
  X,C(Y) ⊃ a
---------------------
Ki(X),C(Y),Z ⊃ Ki(a)
*)
Inductive Ki (i : nat) (a : term) (x y z : Forms) 
  (u : ((Ut x (Compt y (fun x => c x))) ⊃ a)) :
    (Ut (Ut (Compt x (fun x => k i x))
     (Compt y (fun x => c x))) z) ⊃ (k i a) :=
KiE : Ki i a x y z u.

Inductive CL (a b : term) (x : Forms) (u : ((Ut x (Si (e a))) ⊃ b )) :
   ((Ut x (Si (c a))) ⊃ b) :=
ClE : CL a b x u.

Inductive CR (a : term) (x y : Forms) (u : ((Compt x (fun x => c x)) ⊃ (e a))) :
  (Ut (Compt x (fun x => c x)) y) ⊃ (c a) :=
CLE : CR a x y u.

Inductive Ind (a b : term) (x y : Forms) 
  (u : ((Ut (Compt x (fun x => c x)) (Si b)) ⊃ (e a)))
  (v : ((Ut (Compt x (fun x => c x)) (Si b)) ⊃ (e b))) :
    ((Ut (Ut (Compt x (fun x => c x)) y) (Si b)) ⊃ (c a)) :=
IndE : Ind a b x y u v.



Lemma em : forall (A : Type) (e : Ensemble A), Union A (Empty_set A) e = e.
Proof.
intros.
auto with sets.
Defined.

Lemma one : forall (a : term), (Si a) ⊃ a.
Proof.
apply triv.
Defined.

Lemma two : forall (i : nat) (a b : term), 
  (Ut (Si (k i a)) (Si (k i (impl a b)))) ⊃ (k i b).
Proof.
intros.
apply (Ki i b ((Si a) |_| Si (impl a b)) EmptyE EmptyE ).
unfold Compt.
rewrite apply_func_empty.
rewrite (Union_commutative term).
rewrite (em term).
apply (ImplL a b b (Si a)).
apply triv.
apply (Axi b (Si a |_| Si b)).
exact (Si bottom).
Defined.

Check less_than_empty.
Check Noone_in_empty.
Check Union_commutative.
Check Included_Empty.
(*
Lemma comp_empty : forall (A : Type) (f : A -> A),
  (Compt (Empty_set A) f) = (Empty_set A).
Proof.
intros A f.
Check Compt A (Empty_set A) f.
Check (Included_Empty A (Comp A (Empty_set A) f)).
apply (less_than_empty A (Comp A (Empty_set A) f)).
unfold Comp.
red in ⊃ *.
intros.
unfold Comp.
destruct H .
apply (Comp A (Empty_set A) f).
exact (In_ A (Empty_set A) x0).

Qed.

(* unfold Same_set. *)
unfold Included.

intros.
absurd (In A (Empty_set A) x0).
apply ().

revert H.
unfold In.
intros.
destruct H.
revert H.
apply (fun x => absurd).
absurd (In A (Empty_set A) x0).
*)


Lemma three : forall (i : nat) (a : term), 
  (EmptyE ⊃ a) -> (EmptyE ⊃ (and (k i a) (c a))).
Proof.
intros.
apply (AndR).
apply (Ki i a EmptyE EmptyE EmptyE).
unfold Compt.
rewrite (apply_func_empty).
rewrite (em term).
assumption.
exact (Si a).
apply (CR a EmptyE EmptyE).
unfold Compt.
rewrite (apply_func_empty).
apply ((EFixR i a EmptyE) X).
exact (Si bottom).
Defined.

Definition In_ut (a : term) (x : Forms) : In term (Ut x (Si a)) a := 
  Union_intror term x (Si a) a (In_si a).


Lemma four : forall (a : term), (Si (and (e a) (e (c a)))) ⊃ (c a).
Proof.
intros.
Check (AndL).
apply (AndL (e a) (e (c a)) (c a) EmptyE).
rewrite (Union_commutative term).
rewrite (em term).
apply (CR a (Si (e a)) (Si (e (c a)))).
unfold Compt.



Check cut.
apply (cut (and (k 0 a) bottom) a (Si (e a))).
apply E_fix.
exact 0. exact bottom. exact (Si bottom).
apply (andl).
apply axb.
exact (In_ut bottom (Ut (Si (e a)) (Si (k 0 a)))).
exact (Si bottom).
apply axi.
unfold Compt.
*)

Lemma fife : forall (a : term), (Si (c a)) ⊃ (and (e a) (c (e a))).
Proof.
intros.
apply andr,  (ind (c a) (e a) EmptyE EmptyE).
apply (cl a (e a) EmptyE).
rewrite (em term).
apply axi. exact (In_si (e a)).
unfold Compt.
rewrite (apply_func_empty ).
rewrite (em term).
Check ind.
Check (ind 
apply (ind a EmptyE (Si (e a))).
rewrite (em term).
eauto with sets.
*)

Lemma six : forall (a b : term), 
  ((Si (c a)) ⊃ b) -> ((Si b) ⊃ (and (e a) (e b))).
Proof.
intros a b.
apply (cl a b EmptyE).
Defined.