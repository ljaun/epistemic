Section ICK.

Set Implicit Arguments.
Require Import Unicode.Utf8.
Require Import Utf8_core.
Require Import List.
Require Import Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Powerset_facts.
Require Import Coq.Sets.Constructive_sets.
Require Import EnsembleFacts.


(*
 This is how we say  " { (f a) | a in x } "
 Taken from http://www.alumnos.unican.es/ccc66/coq/EnsembleFacts.v

Inductive apply_func (U1 U2:Type) (f:U1->U2) (S:Ensemble U1)
: Ensemble U2 :=
|In_apply_func: forall a:U1, In U1 S a->
  In U2 (apply_func f S) (f a).
*)
(***********************)

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

Theorem  : forall (U1 U2:Type) (f:U1->U2)
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
*)
(***********************)

(*
  Notice the added (E t) Term.
*)
Inductive Term : Set :=
  | bottom : Term
  | var : nat → Term
  | e : Term → Term
  | k1 :  Term → Term
  | k2 :  Term → Term
  | c : Term → Term
  | impl : Term → Term → Term
  | and : Term → Term → Term  
  | or : Term → Term → Term.




(* 
  Helper definition for sets of Terms.
*)
Definition Forms := Ensemble Term.

Definition Si (t : Term) : Forms := Singleton Term t.
Definition In_si (t : Term) : In Term (Si t) t := In_singleton Term t.
Definition EmptyE : Ensemble Term := Empty_set Term.
Definition Ut (u : Forms) (v : Forms) : Forms := Union Term u v.
Definition Compt (x : Forms) (f : Term -> Term) : Forms :=
  apply_func Term Term f x.
Notation "a ∈ X" := (In Term X a) (at level 19).
Notation "A ∪ B" := (Ut A B) (at level 17, left associativity).
Notation "⊥" := bottom.
Notation "{{ A | F }}" := (Compt A F) (at level 18).

Reserved Notation "A ⊃ B" (at level 16).
Inductive S : Forms -> Term -> Type :=
| AxiS :  ∀ Γ a,      (a ∈ Γ) → (Γ ⊃ a)
| AxbS :  ∀ Γ a,      (⊥ ∈ Γ) → (Γ ⊃ a)
| EFix1S : ∀ Γ a,    (Γ ∪ (Si (e a))) ⊃ (k1 a)
| EFix2S : ∀ Γ a,    (Γ ∪ (Si (e a))) ⊃ (k2 a)
| EFixRS: ∀ Γ a,      (Γ ⊃ (and (k1 a) (k2 a))) → (Γ ⊃ e a)
| EFixLS: ∀ Γ a b,    ((Γ ∪ (Si (k1 a)) ∪ (Si (k2 a))) ⊃ b) → ((Γ ∪ (Si (e a))) ⊃ b)
| CutS :  ∀ Γ a b,    (Γ ⊃ a) → ((Γ ∪ (Si a)) ⊃ b) → (Γ ⊃ b)
| OrLS :  ∀ Γ a b c,  ((Γ ∪ (Si a))  ⊃ c) → ((Γ ∪ (Si b))  ⊃ c) → ((Γ ∪ (Si (or a b)))  ⊃ c)
| OrR1S : ∀ Γ a b  ,  (Γ ⊃ a) → (Γ ⊃ (or a b))
| OrR2S : ∀ Γ a b  ,  (Γ ⊃ a) → (Γ ⊃ (or b a))
| AndLS : ∀ Γ a b c,  (((Γ ∪ (Si a)) ∪ (Si b)) ⊃ c) → ((Γ ∪ (Si (and a b)))  ⊃ c)
| AndRS : ∀ Γ a b  ,  (Γ ⊃ a) → (Γ ⊃ b) → (Γ ⊃ (and a b))
| ImplLS: ∀ Γ a b c,  (Γ ⊃ a) → ((Γ ∪ (Si b)) ⊃ c) → ((Γ ∪ (Si (impl a b))) ⊃ c)
| ImplRS: ∀ Γ a b  ,  ((Γ ∪ (Si a)) ⊃ b) → (Γ ⊃ (impl a b))
| K1S   : ∀ Γ Δ Θ a,(( Γ ∪ {{ Δ | (fun x => c x) }}) ⊃ a) → 
   (( {{ Γ | (fun x => k1 x) }} ∪ ({{ Δ | (fun x => c x) }} ∪ Θ)) ⊃ (k1 a))
| K2S   : ∀ Γ Δ Θ a,(( Γ ∪ {{ Δ | (fun x => c x) }}) ⊃ a) → 
   (( {{ Γ | (fun x => k1 x) }} ∪ ({{ Δ | (fun x => c x) }} ∪ Θ)) ⊃ (k2 a))
| CLS :   ∀ Γ a b  ,  (( Γ ∪ (Si (e a))) ⊃ b ) → ((Γ ∪ (Si (c a))) ⊃ b)
| CRS   : ∀ Γ Θ a  ,  ( {{ Γ | (fun x => c x) }} ⊃ (e a)) → (( {{ Γ | (fun x => c x) }} ∪ Θ) ⊃ (c a))
| IndS :  ∀ Γ Θ a b,  ((Ut (Compt Γ (fun x => c x)) (Si b)) ⊃ (e a)) →
    ( ({{ Γ | (fun x => c x)}}) ∪ (Si b)) ⊃ (e b) →
    (((( {{ Γ | (fun x => c x) }}) ∪ Θ) ∪ (Si b)) ⊃ (c a))
where "A ⊃ B" := (S A B).

Definition ttt (Γ : Forms) (a : Term) : Type := (Γ ⊃ k1 a).
Goal ttt (Si bottom) (e bottom).
intros.
unfold ttt. unfold Si. apply AxbS. auto with sets. Defined.


Definition In_ut (a : Term) (x : Forms) : In Term (Ut x (Si a)) a := 
  Union_intror Term x (Si a) a (In_si a).

Lemma em : forall (A : Type) (e : Ensemble A), Union A (Empty_set A) e = e.
Proof.
intros.
auto with sets.
Defined.


Ltac simpl_empty :=
  intros;
  unfold Compt; unfold "∪"; unfold EmptyE; unfold Si;
  try rewrite apply_func_empty_simple;
  try rewrite em; try rewrite em;
  try reflexivity;
  try   exact (Si bottom);
  try   exact (Si bottom); auto with *.
 
Ltac simpl_empty_in id :=
  unfold Compt in id; unfold "∪" in id; unfold EmptyE in id; unfold Si in id;
  try rewrite apply_func_empty_simple in id;
  try rewrite em in id; try rewrite em in id.


Lemma triv : forall (a : Term), (Si a) ⊃ a.
intros.
apply AxiS.
simpl_empty.
Defined.


Lemma bla : forall (a : Term) (Γ Δ : Forms) (p : Γ = Δ),
(Γ ⊃ a) = (Δ ⊃ a).
intros.
rewrite -> p .
reflexivity.
Defined.


Require Export EnsembleFacts.
Check apply_func.

Theorem apply_func_union_singletons : forall (U1 U2:Type)
(f:U1->U2) (a b: U1), 
 (apply_func U1 U2 f (Union U1 (Singleton U1 a) (Singleton U1 b)))
  = Union U2
     (apply_func U1 U2 f (Singleton U1 a)) (apply_func U1 U2 f (Singleton U1 b)).
Proof.
intros U1 U2 f a b.
apply Extensionality_Ensembles.
unfold Same_set.
split.
unfold Included.
intros.
inversion H.
inversion H0.

rewrite -> (apply_func_singleton U1 U2 f b).
rewrite -> (apply_func_singleton U1 U2 f a).
inversion H2.
apply Union_introl.
auto with sets.
rewrite -> (apply_func_singleton U1 U2 f a).
rewrite -> (apply_func_singleton U1 U2 f b).
inversion H2.
apply Union_intror.
auto with sets.

unfold Included.
intros.
inversion H.
inversion H0.
inversion H2.
apply In_apply_func.
apply Union_introl.
exact (In_singleton U1 a0).
inversion H0.
inversion H2.
apply In_apply_func.
apply Union_intror.
exact (In_singleton U1 a0).
Defined.

Lemma simplify_stuff : (forall a b,(({{(Ut (Si a) (Si (impl a b))) | λ x : Term, k1 x}}) ∪ (({{EmptyE | λ x : Term, c x}}) ∪ EmptyE)) = (Si (k1 a) ∪ Si (k1 (impl a b)))).
Proof.
intros.
unfold Compt.
rewrite (apply_func_union_singletons  (λ x : Term, k1 x)).
apply Extensionality_Ensembles.
unfold Same_set.
split.
unfold Included.
intros.
unfold Si.
unfold "∪".
(* simplify H *)
unfold "∪" in H.
unfold EmptyE in H.
rewrite apply_func_empty_simple in H.
rewrite em in H.
rewrite (apply_func_singleton ) in H. 
rewrite (apply_func_singleton ) in H.
rewrite (Union_commutative Term) in H.
rewrite (em (Union Term (Singleton Term (k1 a))
           (Singleton Term (k1 (impl a b))))) in H.
(* --- *)
assumption.
unfold Included.
simpl_empty.
rewrite apply_func_singleton. rewrite apply_func_singleton. 
auto with sets.
Defined.


Lemma one : forall (a : Term), (Si a) ⊃ a.
Proof.
apply triv.
Defined.

Lemma two : forall (a b : Term), 
  (Ut (Si (k1 a)) (Si (k1 (impl a b)))) ⊃ (k1 b).
Proof.
intros.
unfold "∪".
Check simplify_stuff.
rewrite <- simplify_stuff.
apply K1S.
simpl_empty.
assert ((Union Term (Union Term (Singleton Term a) (Singleton Term (impl a b)))
  (Empty_set Term)) = (Si a ∪ Si (impl a b))).
  simpl_empty.  
  rewrite Union_commutative.
  simpl_empty.
rewrite  H.
apply ImplLS.
apply AxiS.
auto with *.
apply AxiS.  
simpl_empty.
Defined.

Check less_than_empty.
Check Noone_in_empty.
Check Union_commutative.
Check Included_Empty.



Lemma simplify_stuff_three :  ({{EmptyE | λ x : Term, k1 x}}) ∪ (({{EmptyE | λ x : Term, c x}}) ∪ EmptyE) = EmptyE.
Proof.
simpl_empty.
simpl_empty.
Defined.

Lemma three : forall (a : Term), 
  (EmptyE ⊃ a) -> (EmptyE ⊃ (and (k1 a) (c a))).
Proof.
intros.
apply (AndRS).
Check K1S.
rewrite <- (simplify_stuff_three).
apply (K1S).
simpl_empty.
assert ((({{EmptyE | λ x : Term, c x}}) ∪ EmptyE) = EmptyE).
  simpl_empty.
rewrite <- H.
apply CRS.
apply EFixRS.
apply AndRS.
simpl_empty.
assert ((({{EmptyE | λ x : Term, k1 x}}) ∪ (({{EmptyE | λ x : Term, c x}}) ∪ EmptyE)) = Empty_set Term).
simpl_empty.
rewrite <- H0.
apply K1S.
simpl_empty.
assert ((({{EmptyE | λ x : Term, k1 x}}) ∪ (({{EmptyE | λ x : Term, c x}}) ∪ EmptyE)) = ({{EmptyE | λ x : Term, c x}})).
simpl_empty. simpl_empty.
rewrite <- H0.
apply K2S.
simpl_empty. 
Defined.


(*
End ICK.

Extraction Language Haskell.
Extraction Language Ocaml.
Set Extraction Optimize.
Recursive Extraction three.
*)

Lemma assoc_si : forall (a b c : Term), (((Si a) ∪ (Si b)) ∪ (Si c)) = ((Si a) ∪ ((Si b) ∪ (Si c))).
Proof.
intros.
apply Extensionality_Ensembles.
unfold Same_set.
split.
unfold Included.
intros.
inversion H. inversion H0.
apply Union_introl. assumption.
apply Union_intror. apply Union_introl. assumption.
apply Union_intror. apply Union_intror. assumption.
unfold Included.
intros.
inversion H.
apply Union_introl. apply Union_introl. assumption.
inversion H0.
apply Union_introl. apply Union_intror. assumption.
apply Union_intror. assumption.
Defined.


Lemma four : forall (a : Term), (Si (and (e a) (e (c a)))) ⊃ (c a).
Proof.
intros.
Check (IndS).
assert (forall b, (({{EmptyE | λ x : Term, c x}}) ∪ EmptyE ∪ Si b) = Si b).
  simpl_empty.
rewrite <- H.  
apply IndS.
simpl_empty.
apply EFixRS.
intros.
(* assert (forall a, ((EmptyE ∪ (Si (and (e a) (e (c a))))) ⊃ e a) = (Si (and (e a) (e (c a))) ⊃ e a)). *)
assert (forall a, ((EmptyE ∪ (Si (and (e a) (e (c a))))) ⊃ and (k1 a) (k2 a)) = (Singleton Term (and (e a) (e (c a))) ⊃ and (k1 a) (k2 a))).
  simpl_empty.
rewrite <- H0.
apply AndLS.
Check EFixLS.
assert (((Si (e (c a))) ∪ Si (e a)) = (EmptyE ∪ Si (e a) ∪ Si (e (c a)))).
  simpl_empty. rewrite Union_commutative. reflexivity.
rewrite <- H1.
apply EFixLS.
apply AndRS.
apply AxiS. simpl_empty.
apply AxiS. simpl_empty.
(* end 1 *)
apply EFixRS.
apply AndRS.
apply AndLS.
apply EFixLS. 
Check EFixLS.
assert ((({{EmptyE | λ x : Term, c x}}) ∪ Si (e a) ∪ Si (k1 (c a)) ∪ Si (k2 (c a))) = 
((Si (k1 (c a)) ∪ Si (k2 (c a))) ∪ Si (e a))).
  simpl_empty.  rewrite Union_commutative.  rewrite Union_commutative.
rewrite assoc_si.
simpl_empty. rewrite Union_commutative. reflexivity.
rewrite H0.
assert ((({{(Si (c a)) | λ x : Term, k1 x}}) ∪ (({{EmptyE | λ x : Term, c x}}) ∪ ((Si (k2 (c a)) ∪ Si (e a))))) =
(Si (k1 (c a)) ∪ Si (k2 (c a)) ∪ Si (e a))).
simpl_empty. rewrite apply_func_singleton. rewrite assoc_si. simpl_empty.
rewrite <- H1.
apply K1S.

Check EFix1S.
assert (forall a, ((Si (e (c a))) ∪ Si (e a)) = (EmptyE ∪ Si (e a) ∪ Si (e (c a)))).
simpl_empty.  rewrite Union_commutative. reflexivity.
rewrite <- H1.
apply EFix1S.
assert (forall a, ((Si (e (c a))) ∪ Si (e a)) = (EmptyE ∪ Si (e a) ∪ Si (e (c a)))).
simpl_empty.  rewrite Union_commutative. reflexivity.
rewrite <- H1.
apply EFix2S.
apply EFixRS.
apply AndRS.
assert ((({{EmptyE | λ x : Term, k1 x}}) ∪ (({{EmptyE | λ x : Term, c x}}) ∪ (Si (and (e a) (e (c a)))))) = (({{EmptyE | λ x : Term, c x}}) ∪ Si (and (e a) (e (c a))))).
  simpl_empty.
rewrite <- H0.
apply K1S.
apply AxiS.
simpl_empty.
auto with sets.
assert ((({{EmptyE | λ x : Term, k1 x}}) ∪ (({{EmptyE | λ x : Term, c x}}) ∪ (EmptyE ∪ Si (e a) ∪ Si (e (c a))))) = (EmptyE ∪ Si (e a) ∪ Si (e (c a)))).
simpl_empty. simpl_empty.
rewrite <- H1.
apply K1S.
 EFix1
S.
assert ((EmptyE ∪ Si (e a) ∪ Si (e (c a))) = ( Si (e (c a)) ∪ Si (e a))).
  simpl_empty.
  rewrite Union_commutative.
  reflexivity.
rewrite -> H1.
apply EFixS.
simpl_empty.
apply EFixRS.
intros.
Check KiS.
assert ((Singleton Term (and (e a) (e (c a)))) = (EmptyE ∪ Si (and (e a) (e (c a))))).
  simpl_empty.
rewrite H0.
apply AndLS.
apply EFixLS.
intros.
assert ((({{Si ((c a)) | λ x : Term, k i0 x}}) ∪ (({{EmptyE | λ x : Term, c x}})
  ∪ (Si (e a)))) 
  = (EmptyE ∪ Si (e a) ∪ Si (k i0 (c a)))).
  simpl_empty.
  rewrite apply_func_singleton.
  rewrite Union_commutative.  
  simpl_empty.
rewrite <- H1.
apply (KiS i0).
simpl_empty.
simpl_empty.
apply AxiS.
simpl_empty.
*)

(*
Lemma fife : forall (a : Term), (Si (c a)) ⊃ (and (e a) (c (e a))).
Proof.
intros.
(* AND right *)
apply AndRS.
assert (forall a, (Si (c a)) = (EmptyE ∪ Si (c a))).
  simpl_empty.
rewrite -> H.
(* C left *)
apply CLS.
(* ID Axiom *)
apply AxiS.
simpl_empty.
assert (forall a, (Si (c a)) = (({{EmptyE  | λ x : Term, c x}}) ∪ EmptyE ∪ Si (c a))).
  simpl_empty.
rewrite -> H.
(* C Induction *)
apply IndS.
simpl_empty.
(* E-Fix Right *)
apply EFixRS.
apply AndRS.
assert ((({{EmptyE | λ x : Term, k1 x}}) ∪ (({{(Si a) | λ x : Term, c x}}) ∪ EmptyE)) = (Singleton Term (c a))).
simpl_empty. rewrite apply_func_singleton.  rewrite Union_commutative. simpl_empty.
rewrite <- H0.
apply K1S.
apply EFixRS.
apply AndRS.
assert ((({{EmptyE | λ x : Term, k1 x}}) ∪ (({{(Si a) | λ x : Term, c x}}) ∪ EmptyE)) = (EmptyE ∪ ({{Si a | λ x : Term, c x}}))).
simpl_empty. rewrite apply_func_singleton.  rewrite Union_commutative. simpl_empty.
rewrite <- H1.
apply K1S.
simpl_empty.
rewrite apply_func_singleton.
assert ((EmptyE ∪ Si (c a)) = Singleton Term (c a)).
simpl_empty.
rewrite <- H2.
apply CLS.
apply EFixLS. 
intro.
assert (forall i, ((({{EmptyE | λ x : Term, k i x}})
   ∪ (({{(Si a) | λ x : Term, c x}}) ∪ EmptyE)) = (Singleton Term (c a)))).
  simpl_empty.
  rewrite apply_func_singleton.
  rewrite Union_commutative.
  simpl_empty.
rewrite <- (H0 i).
(* K rule *)
apply KiS. 
simpl_empty.    rewrite apply_func_singleton.
2: simpl_empty.
rewrite <- (H0 i).
(* E-Fix Left *)
apply EFixRS.
intros.
simpl_empty.
rewrite apply_func_singleton.
rewrite Union_commutative.
simpl_empty.
assert (forall i, (({{EmptyE | λ x : Term, k i x}})
   ∪ (({{(Si a) | λ x : Term, c x}}) ∪ EmptyE)) = (Singleton Term (c a))).
  simpl_empty.
  rewrite apply_func_singleton.
  rewrite Union_commutative.
  simpl_empty.
rewrite <- (H1 i0).
(* K rule *)
apply KiS.
simpl_empty.
rewrite apply_func_singleton.
assert (forall a, (EmptyE ∪ Si (c a)) = Singleton Term (c a)).
  simpl_empty.
rewrite <- H2.
(* C Left *)
apply CLS.
(* E-Fix Left *)
apply EFixLS.
intros.
simpl_empty.
(* C Induction *)
apply IndS.
rewrite (em Term).
eauto with sets.
*)


Lemma tlist_eq : forall (a b : Term), a ∈ Si b -> (Si a) = (Si b).
intros.
inversion H.
reflexivity.
Defined.


Lemma six : forall (a b : Term), 
  ((Si b) ⊃ (and (e a) (e (c b)))) -> ((Si b) ⊃ (c a)).
Proof.
intros x y H.
assert (Si y = (({{EmptyE | λ x : Term, c x}}) ∪ EmptyE ∪ Si y)).
  simpl_empty.
rewrite H0.
apply IndS.
apply AndRS with (b:=(e (c y))) in H .
dependent induction y.
apply AxbS.
auto with *.
assert (Si (var n) = (({{EmptyE | λ x : Term, c x}}) ∪ EmptyE ∪ Si (var n))).
  simpl_empty.
rewrite H0.
apply IndS.
apply EFixRS.

inversion H.
inversion H0.
Check IndS.
assert ((({{EmptyE | λ x : Term, c x}}) ∪ EmptyE ∪ Si y) = (Si y)).
simpl_empty.
assert ((EmptyE ∪ Si (and (e x) (e (c y)))) = Si (and (e x) (e (c y)))).
simpl_empty.
rewrite <- H5.
apply AndLS.
assert ((({{EmptyE | λ x : Term, c x}}) ∪ Si (e (c y)) ∪ (Si (e x))) = (EmptyE ∪ Si (e x) ∪ Si (e (c y)))).
  simpl_empty. simpl_empty.
  rewrite Union_commutative. reflexivity.
rewrite <- H6.
apply IndS.
apply AxiS.
simpl_empty.
(*rewrite <- H4.*)
apply EFixRS. apply AndRS. apply EFixLS.
assert ((({{(Si x) | λ x : Term, k1 x}}) ∪ (({{EmptyE | λ x : Term, c x}}) ∪ (Si (k2 x)))) = (({{EmptyE | λ x : Term, c x}}) ∪ Si (k1 x) ∪ Si (k2 x))).
  simpl_empty.  rewrite apply_func_singleton.  simpl_empty.
rewrite <- H7.
apply K1S.
apply EFixRS.
apply AndRS.
(*assert ((({{EmptyE | λ x : Term, c x}}) ∪ EmptyE ∪ Si (e x)) = (({{EmptyE | λ x0 : Term, c x0}}) ∪ Si (e x))).
  simpl_empty.
  rewrite <- H8.*)
apply IndS.
inversion H0.
rewrite H4.
apply AndLS.
apply AxiS.
simpl_empty.

apply EFixRS.
apply AndRS.
inversion H.
assert ((({{EmptyE | λ x : Term, c x}}) ∪ Si y) = Si y).
simpl_empty.
rewrite H1.
2:assert ((({{EmptyE | λ x : Term, c x}}) ∪ Si y) = Si y).
2:simpl_empty.
2: rewrite H1.
inversion H.
Check AndRS.
apply AndRS in H.


apply Extensionality_Ensembles.
unfold Same_set.
split.
unfold Included.
intros.
assert ( and (e x) (e (c x)) ∈ Si y).
unfold Si.
unfold Si in H.
exact H2.


Check AndRS.
simpl_empty.
assert (Included Term (EmptyE ∪ Si (and (e x) (e (c x)))) (Si y) = (and (e x) (e (c x)) ∈ Si y)).
simpl_empty.
rewrite H2.
unfold Included.

simpl_empty.

apply AndLS.

Check CRS.
assert ((({{EmptyE | λ x : Term, c x}}) ∪ (Si b)) = Si b).
simpl_empty.
rewrite <- H0.
apply CRS.
inversion H.
*)

