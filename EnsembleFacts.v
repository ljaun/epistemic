(***************************
 EnsembleFacts.v
 By Crist\u00f3bal Camarero Coterillo
 cristobal.camarero@alumnos.unican.es
 http://www.alumnos.unican.es/ccc66

 For therories requiring classical properties
 Elemental properties of sets, bijection, apply function to ensemble,
 bijective_eqcardinal, reductions of a set by a function (aka summatory).

 Depends on:
***************************)

Section EnsembleFacts.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Classical.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Sets.Finite_sets_facts.

Require Import Setoid.
Require Import Coq.omega.Omega.


Definition Operation (U:Type):Type := U->U->U.

Definition Associativity (U:Type) (f:Operation U):=
forall (a b c:U), f (f a b) c= f a (f b c).

Definition Commutativity (U:Type) (f:Operation U):=
forall (a b:U), f a b= f b a.
Implicit Arguments Associativity [U].
Implicit Arguments Commutativity [U].


(*  see  Library Coq.Logic.ClassicalChoice *)
(* Lo habia escrito exactamente (save rename) como choice *)
Theorem existsfunctions : forall (U1 U2:Type) (P:U1->U2->Prop),
(forall (a:U1), exists b:U2, P a b)->
(exists f:U1->U2, forall a:U1, P a (f a)).
Proof.
exact choice.
Qed.

Lemma selfincluded : forall (U:Type) (A:Ensemble U),
Included U A A.
Proof.
intros.
unfold Included.
intros.
assumption.
Qed.

(* repeat of Extension *)
Theorem Extensionality_Ensembles_rec:
forall (U:Type) (A B:Ensemble U), A=B -> Same_set U A B.
Proof.
intros.
rewrite H.
split.
apply selfincluded.
apply selfincluded.
Qed.

Lemma SameCouple: forall (U:Type) (a:U),
Couple U a a=Singleton U a.
Proof.
intros.
apply Extensionality_Ensembles.
split.
unfold Included.
intros.
inversion H.
apply In_singleton.
apply In_singleton.
unfold Included.
intros.
inversion H.
apply Couple_l.
Qed.

Lemma EqualCouples:
forall (U:Type) (e a b:U),
Couple U e a=Couple U e b -> a=b.
Proof.
intros U e a b H.
apply Extension in H.
destruct H as [L R].
unfold Included in *.
assert(eqae:a=e\/a<>e). apply classic.
destruct eqae as [eqae|neqae].
rewrite eqae in *.
rewrite SameCouple in *.
assert(bH:In U (Couple U e b) b).
apply Couple_r.
apply R in bH.
inversion bH.
tauto.
assert(bH:In U (Couple U e a) a).
apply Couple_r.
apply L in bH.
inversion bH.
symmetry in H. tauto.
tauto.
Qed.

Lemma CoupleComm: forall (U:Type) (a b:U),
Couple U a b=Couple U b a.
Proof.
intros.
apply Extensionality_Ensembles.
split.
unfold Included.
intros.
inversion H.
apply Couple_r.
apply Couple_l.
unfold Included.
intros.
inversion H.
apply Couple_r.
apply Couple_l.
Qed.


(* Bijective? Coq.Classes.Functions? *)
Definition Bijective (U1 U2:Type) (f:U1->U2):Prop:=
(forall a b:U1, a<>b -> f a<>f b) /\
(forall b:U2, exists a:U1, f a=b).

Theorem Bijective_rev : forall (U1 U2:Type) (f:U1->U2) (a b:U1),
 (Bijective U1 U2 f) -> f a=f b -> a=b.
Proof.
intros.
destruct H.
assert(a=b \/ a<>b).
apply classic.
destruct H2. assumption.
apply H in H2.
tauto.
Qed.

Inductive apply_func (U1 U2:Type) (f:U1->U2) (S:Ensemble U1)
:Ensemble U2 :=
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

Theorem apply_func_singleton : forall (U1 U2:Type) (f:U1->U2)
(x:U1),
 (apply_func U1 U2 f (Singleton U1 x))
  = Singleton U2 (f x).
Proof.
intros.
apply Extensionality_Ensembles.
split.
unfold Included.
intros.
inversion H.
inversion H0.
apply In_singleton.
unfold Included.
intros.
inversion H.
apply In_apply_func.
apply In_singleton.
Qed.


Theorem apply_func_add : forall (U1 U2:Type) (f:U1->U2)
(S:Ensemble U1) (x:U1),
 (apply_func U1 U2 f (Add U1 S x))
  = Add U2 (apply_func U1 U2 f S) (f x).
Proof.
intros.
apply Extensionality_Ensembles.
unfold Same_set.
split.
unfold Included.
intros.
inversion H.
inversion H0.
unfold Add.
apply Union_introl.
apply In_apply_func. assumption.
unfold Add.
apply Union_intror.
inversion H2.
apply In_singleton.

unfold Included.
intros.
inversion H.
inversion H0.
apply In_apply_func.
unfold Add.
apply Union_introl. assumption.
inversion H0.
apply In_apply_func.
unfold Add.
apply Union_intror.
apply In_singleton.
Qed.


Theorem apply_func_intersection : forall (U1 U2:Type)
(f:U1->U2) (A B:Ensemble U1), (Bijective U1 U2 f) ->
 (apply_func U1 U2 f (Intersection U1 A B))
  = Intersection U2
     (apply_func U1 U2 f A) (apply_func U1 U2 f B).
Proof.
intros U1 U2 f A B BJ.
apply Extensionality_Ensembles.
unfold Same_set.
split.
unfold Included.
intros.
inversion H.
inversion H0.
apply Intersection_intro.
apply In_apply_func. assumption.
apply In_apply_func. assumption.

unfold Included.
intros.
inversion H.
induction H0.
inversion H1.
apply Bijective_rev in H3.
apply In_apply_func.
apply Intersection_intro.
rewrite H3. assumption.
assumption.
assumption.
Qed.

Theorem apply_func_couple : forall (U1 U2:Type)
(f:U1->U2) (a b:U1), (Bijective U1 U2 f) ->
 (apply_func U1 U2 f (Couple U1 a b))
  = Couple U2 (f a) (f b).
Proof.
intros U1 U2 f a b BIJ.
apply Extensionality_Ensembles.
split.
unfold Included.
intros x Inx.
inversion Inx.
inversion H.
apply Couple_l.
apply Couple_r.
unfold Included.
intros x Inx.
inversion Inx.
apply In_apply_func.
apply Couple_l.
apply In_apply_func.
apply Couple_r.
Qed.


Theorem apply_func_equation : forall (U1 U2:Type) (f:U1->U2)
(A B:Ensemble U1), A=B ->
apply_func U1 U2 f A = apply_func U1 U2 f B.
Proof.
intros.
rewrite H.
trivial.
Qed.



Theorem bijective_eqcardinal : forall (U1 U2:Type) (f:U1->U2)
 (S:Ensemble U1), (Bijective U1 U2 f) ->
 (forall (n:nat),
   (cardinal U1 S n) ->(cardinal U2 (apply_func U1 U2 f S) n) ).
Proof.
intros.
revert H0. revert S.
induction n.
intros.
inversion H0.
rewrite apply_func_empty.
apply card_empty.
exact S.

intros.
inversion H0.
rewrite apply_func_add.
apply card_add.
apply IHn.
assumption.

intro.
inversion H5.
apply Bijective_rev in H6.
rewrite H6 in H7.
tauto.
assumption.
Qed.

Definition InverseFunction (U1 U2:Type) (f:U1->U2) (g:U2->U1)
:= forall (a:U1) (b:U2), f a =b -> g b =a.

Lemma UndoInverse :
forall (U1 U2:Type) (f:U1->U2) (g:U2->U1) (a:U1),
InverseFunction U1 U2 f g -> g (f a)=a.
Proof.
intros.
apply H.
tauto.
Qed.

Theorem InverseOfBijectiveIsBijective :
forall (U1 U2:Type) (f:U1->U2) (g:U2->U1),
Bijective U1 U2 f -> InverseFunction U1 U2 f g
-> Bijective U2 U1 g.
Proof.
intros U1 U2 f g BIJ INV.
inversion BIJ.
split.
intros.
intro.
destruct (H0 a) as [ia iaH].
destruct (H0 b) as [ib ibH].
rewrite<- iaH in H2.
rewrite<- ibH in H2.
(*rewrite UndoInverse in H2.*)
rewrite UndoInverse with (g:=g) in H2.
rewrite UndoInverse with (g:=g) in H2.
(*rewrite UndoInverse with(a:=ia) (U2:=U2) in H2.*)
rewrite H2 in iaH.
rewrite iaH in ibH.
tauto.
assumption. assumption.

intros.
exists (f b).
apply UndoInverse.
assumption.
Qed.

Lemma UndoInverseBijective :
forall (U1 U2:Type) (f:U1->U2) (g:U2->U1),
Bijective U1 U2 f->
(InverseFunction U1 U2 f g) -> (InverseFunction U2 U1 g f).
Proof.
intros U1 U2 f g BIJ INV.
unfold InverseFunction.
intros.
inversion BIJ.
destruct (H1 a) as [b' b'H].
assert(g(f b')=g a).
rewrite b'H. tauto.
rewrite H in H2.
rewrite<- H2.
rewrite UndoInverse with (a:=b') (U2:=U2).
assumption.
assumption.
Qed.

Lemma UndoInverseSym :
forall (U1 U2:Type) (f:U1->U2) (g:U2->U1) (b:U2),
Bijective U1 U2 f ->
InverseFunction U1 U2 f g -> f (g b)=b.
Proof.
intros U1 U2 f g b BIJf INVfg.
apply UndoInverse.
apply UndoInverseBijective.
assumption.
assumption.
Qed.

Theorem ExistsInverseOfBijective:
forall  (U1 U2:Type) (f:U1->U2), Bijective U1 U2 f ->
exists g:U2->U1, InverseFunction U1 U2 f g.
Proof.
intros.
unfold InverseFunction.
assert(EF:=existsfunctions U2 U1
 (fun (b:U2) (a:U1) => (f a=b))
 ).
assert(forall a : U2, exists b : U1,
 (fun (b0 : U2) (a0 : U1) => f a0 = b0) a b).
intros. inversion H.
apply H1.
apply EF in H0.
destruct H0 as [g gH].
exists g.
intros.
inversion H.
assert(B:=gH b).
rewrite <- H0 in B.
assert(X:=H1 (g (f a)) a).
assert(g(f a)=a \/ g(f a)<>a).
apply classic.
destruct H3.
rewrite H0 in H3.
assumption.
apply X in H3.
tauto.
Qed.

Lemma BijectionSimplify:
forall (U1 U2:Type) (f:U1->U2) (a b:U1),
Bijective U1 U2 f -> f a = f b -> a=b.
Proof.
intros.
destruct (ExistsInverseOfBijective U1 U2 f H) as [g gH].
assert(g(f a)=g(f b)).
rewrite H0. tauto.
(*rewrite UndoInverse in H1.
rewrite UndoInverse with (a:=a) (U2:=U2) in H1.*)
do 2 rewrite UndoInverse with (g:=g) in H1;auto.
Qed.


Definition Compose (U1 U2 U3:Type) (f:U2->U3) (g:U1->U2):=
fun (a:U1) => f (g a).

(* f(g(x)) is bijection *)
Theorem BijectionComposition :
forall (U1 U2 U3:Type) (f:U2->U3) (g:U1->U2),
Bijective U2 U3 f -> Bijective U1 U2 g -> 
Bijective U1 U3 (Compose U1 U2 U3 f g).
Proof.
intros U1 U2 U3 f g BIJf BIJg.
unfold Compose.
split.
intros.
intro.
apply BijectionSimplify in H0.
apply BijectionSimplify in H0.
tauto.
assumption.
assumption.

intros.
destruct (ExistsInverseOfBijective U2 U3 f BIJf) as [If IfH].
destruct (ExistsInverseOfBijective U1 U2 g BIJg) as [Ig IgH].
exists ((Compose U3 U2 U1 Ig If) b).
unfold Compose.
assert(If (f (g (Ig (If b)))) = If b).
rewrite UndoInverse with (g:=If).
rewrite UndoInverseSym with (f:=g).
tauto.
assumption.
assumption.
assumption.
apply BijectionSimplify in H.
assumption.
apply InverseOfBijectiveIsBijective with (f:=f).
assumption.
assumption.
Qed.


Lemma DifferentAdd_Empty : forall (U:Type) (x:U) (A:Ensemble U),
Add U A x <> Empty_set U.
Proof.
intros U x A H.
apply Extensionality_Ensembles_rec in H.
destruct H as [L R].
unfold Included in L.
specialize L with (x0:=x).
assert(In U (Empty_set U) x).
apply L.
apply Union_intror.
apply In_singleton.
inversion H.
Qed.

Lemma DisjointAddElim:
forall (U:Type) (A:Ensemble U) (a x:U),
In U (Add U A a) x -> ~ In U A a -> x<>a -> In U A x.
Proof.
intros U A a x Inx nIna neqxa.
inversion Inx.
assumption.
inversion H.
symmetry in H1.
tauto.
Qed.

Lemma DisjointAddEquation:
forall (U:Type) (A B:Ensemble U) (a b:U),
Add U A a=Add U B b-> ~ In U A a -> ~ In U B b ->
(a=b /\ A=B) \/ (a<>b /\ In U A b /\ In U B a).
Proof.
intros U A B a b H Na Nb.
apply Extensionality_Ensembles_rec in H.
assert(eqab:a=b\/a<>b).
apply classic.
destruct eqab as [eqab|neqab].
left.
split.
assumption.
rewrite<- eqab in Nb.
rewrite<- eqab in H.
inversion H as [HA HB].
apply Extensionality_Ensembles.
split.
unfold Included.
intros x Hx.
unfold Included in HA.
specialize HA with (x:=x).
assert(In U (Add U A a) x).
apply Union_introl. assumption.
apply HA in H0.
apply DisjointAddElim with (a:=a).
assumption. assumption.
assert(eqxa:x=a\/x<>a). apply classic.
destruct eqxa as [eqxa|neqxa].
rewrite eqxa in Hx.
tauto.
assumption.
unfold Included.
intros x Hx.
unfold Included in HB.
specialize HB with (x:=x).
assert(In U (Add U B a) x).
apply Union_introl. assumption.
apply HB in H0.
apply DisjointAddElim with (a:=a).
assumption. assumption.
assert(eqxa:x=a\/x<>a). apply classic.
destruct eqxa as [eqxa|neqxa].
rewrite eqxa in Hx.
tauto.
assumption.

right.
inversion H as [HA HB].
split. assumption.
split.
unfold Included in HB.
specialize HB with (x:=b).
apply DisjointAddElim with (a:=a).
apply HB.
apply Union_intror.
apply In_singleton.
assumption.
auto.
unfold Included in HA.
specialize HA with (x:=a).
apply DisjointAddElim with (a:=b).
apply HA.
apply Union_intror.
apply In_singleton.
assumption.
auto.
Qed.


Lemma EnsembleAddInto:
forall (U:Type) (A B:Ensemble U) (a x:U),
In U A x -> Add U B a = A -> a <> x -> In U B x.
Proof.
intros U A B a x InAx AB neqax.
rewrite<- AB in InAx. clear AB.
inversion InAx. assumption.
clear x0 H0.
inversion H. rewrite H0 in neqax.
tauto.
Qed.

Lemma EnsembleAddComm:
forall (U:Type) (A:Ensemble U) (a b:U),
Add U (Add U A a) b= Add U (Add U A b) a.
Proof.
intros U A a b.
apply Extensionality_Ensembles.
split.
unfold Included.
intros.
inversion H.
inversion H0.
apply Union_introl. apply Union_introl. assumption.
inversion H2. apply Union_intror. apply In_singleton.
inversion H0. apply Union_introl.
apply Union_intror. apply In_singleton.
unfold Included.
intros.
inversion H.
inversion H0.
apply Union_introl. apply Union_introl. assumption.
inversion H2. apply Union_intror. apply In_singleton.
inversion H0. apply Union_introl.
apply Union_intror. apply In_singleton.
Qed.

(* replica of Simplify_add *)
Lemma DisjointAddEquationElim:
forall (U:Type) (A B:Ensemble U) (x:U),
~ In U A x -> ~ In U B x -> Add U A x=Add U B x -> A=B.
Proof.
intros U A B x nInA nInB H.
apply Extension in H.
inversion H as [HL HR].
apply Extensionality_Ensembles.
split.
unfold Included.
intros c InAc.
assert(eqxc:x=c\/x<>c). apply classic.
destruct eqxc as [eqxc|neqxc].
rewrite eqxc in nInA. tauto.
apply EnsembleAddInto with (A:=Add U B x) (a:=x).
apply HL. apply Union_introl. assumption.
tauto. assumption.
unfold Included.
intros c InAc.
assert(eqxc:x=c\/x<>c). apply classic.
destruct eqxc as [eqxc|neqxc].
rewrite eqxc in nInB. tauto.
apply EnsembleAddInto with (A:=Add U A x) (a:=x).
apply HR. apply Union_introl. assumption.
tauto. assumption.
Qed.


(* We really need Finite? *)
Lemma NonEmptyAsAdd:
forall (U:Type) (A:Ensemble U),
Finite U A-> forall a:U,
In U A a ->
exists B:Ensemble U, A=Add U B a /\ ~ In U B a.
Proof.
(*intros U A FINITE a Ina.*)
intros U A FINITE.
destruct(finite_cardinal U A FINITE) as [n nH].
clear FINITE.
revert A nH.
induction n.
(*base*)
intros A CARD a Ina.
inversion CARD.
rewrite<- H in Ina.
inversion Ina.
(*induction*)
intros A CARD a Ina.
inversion CARD.
assert(IHS:=IHn A0 H0).
assert(eqxa:x=a\/x<>a). apply classic.
destruct eqxa as [eqxa|neqxa].
rewrite eqxa in *. clear x eqxa.
exists A0. tauto.
assert(In U A0 a).
apply EnsembleAddInto with (A:=A) (a:=x).
assumption. assumption. assumption.
specialize IHS with (a:=a).
apply IHS in H3.
destruct H3 as [B BH].
exists (Add U B x).
rewrite EnsembleAddComm.
destruct BH as [BL BR].
rewrite BL.
split.
tauto.
intro.
inversion H3. tauto.
inversion H4. tauto.
Qed.



Lemma EnsembleAddIncludes :
forall (U:Type) (A:Ensemble U) (a:U),
Included U A (Add U A a).
Proof.
intros U A a.
unfold Included.
intros x InAx.
apply Union_introl.
assumption.
Qed.

Lemma EnsembleSubFinite :
forall (U:Type) (A:Ensemble U) (a:U),
Finite U (Add U A a) -> Finite U A.
Proof.
intros U A a FINITEADD.
apply Finite_downward_closed with (A:=Add U A a).
assumption.
apply EnsembleAddIncludes.
Qed.


Lemma DisjointAddEquationCommon:
forall (U:Type) (A B:Ensemble U) (a b:U),
Finite U A-> Add U A a=Add U B b->
~ In U A a -> ~ In U B b -> a<>b ->
exists C:Ensemble U, A =Add U C b /\ B=Add U C a /\
~In U C a /\ ~In U C b /\ In U A b /\ In U B a.
Proof.
intros U A B a b FINITEA H Na Nb neqab.
assert(FINITEAA:Finite U (Add U A a)).
apply Add_preserves_Finite. assumption.
assert(FINITEB:Finite U B).
apply EnsembleSubFinite with (a:=b).
rewrite<- H. assumption.
assert(DAE:=DisjointAddEquation
 U A B a b H Na Nb).
destruct DAE as [DAE|DAE].
destruct DAE as [L R].
tauto.
destruct DAE as [_ DAE].
destruct DAE as [InAb InBa].
assert(exists C : Ensemble U, A = Add U C b /\ ~In U C b).
apply NonEmptyAsAdd.
assumption.
assumption.
destruct H0 as [C CH].
destruct CH as [CAdd Cb].
assert(exists C : Ensemble U, B = Add U C a /\ ~In U C a).
apply NonEmptyAsAdd.
assumption.
assumption.
destruct H0 as [D DH].
destruct DH as [DAdd Da].
assert(C=D).
apply Extensionality_Ensembles.
split.
unfold Included.
intros x xH.
assert(In U A x). rewrite CAdd.
apply Union_introl. assumption.
assert(In U (Add U B b) x).
rewrite<- H. apply Union_introl. assumption.
inversion H1.
rewrite DAdd in H2.
inversion H2. assumption.
inversion H4.
rewrite<- H6 in H0. tauto.
inversion H2.
rewrite<- H4 in xH. tauto.
unfold Included.
intros x xH.
assert(In U B x). rewrite DAdd.
apply Union_introl. assumption.
assert(In U (Add U A a) x).
rewrite H. apply Union_introl. assumption.
inversion H1.
rewrite CAdd in H2.
inversion H2. assumption.
inversion H4.
rewrite<- H6 in H0. tauto.
inversion H2.
rewrite<- H4 in xH. tauto.
(*C=D*)
rewrite<- H0 in *.
clear D H0.
exists C.
split. assumption.
split. assumption.
split. assumption.
split. assumption.
split. assumption.
assumption.
Qed.

Lemma EnsembleAddEmptyIsSingleton:
forall (U:Type) (A:Ensemble U) (a:U),
Add U (Empty_set U) a = Singleton U a.
Proof.
intros U A a.
apply Extensionality_Ensembles.
split.
unfold Included.
intros.
inversion H.
inversion H0.
assumption.
unfold Included.
intros.
inversion H.
apply Union_intror.
apply In_singleton.
Qed.

Lemma EnsemblesSingletonEqAdd:
forall (U:Type) (A:Ensemble U) (a b:U),
Singleton U b = Add U A a -> a=b.
Proof.
intros.
apply Extension in H.
inversion H.
unfold Included in *.
specialize H1 with (x:=a).
assert(In U (Add U A a) a).
apply Union_intror. apply In_singleton.
apply H1 in H2.
inversion H2.
rewrite H3 in *.
tauto.
Qed.

Lemma EnsemblesSingletonEqDisjAdd:
forall (U:Type) (A:Ensemble U) (a b:U),
~ In U A a -> Singleton U b = Add U A a ->
(a=b /\ A=Empty_set U) .
Proof.
intros U A a b nIna H.
assert(a=b).
apply EnsemblesSingletonEqAdd with (A:=A).
assumption.
split. assumption.
rewrite H0 in *. clear H0 a.
apply Extension in H.
inversion H.
apply Extensionality_Ensembles.
split.
unfold Included in *.
intros.
specialize H1 with (x:=x).
assert(In U (Add U A b) x).
apply Union_introl. assumption.
apply H1 in H3.
inversion H3.
rewrite<- H4 in H2. tauto.
unfold Included in *.
intros.
inversion H2.
Qed.


Lemma EnsembleAddToSub :
forall (U:Type) (A B:Ensemble U) (a:U),
~In U A a -> Add U A a=B -> A=Subtract U B a.
Proof.
intros U A B a nInAa H.
rewrite<- H.
apply Sub_Add_new.
assumption.
Qed.

Lemma EnsembleSubCardinal :
forall (U:Type) (A:Ensemble U) (a:U) (n:nat),
~In U A a -> cardinal U (Add U A a) (S n) -> cardinal U A n.
Proof.
intros U A a n nInAa.
intros CARD.
apply card_soustr_1 with (X:=Add U A a) (n:=S n) (x:=a) in CARD.
rewrite<- Sub_Add_new with (U:=U) (x:=a) in CARD.
rewrite<- pred_Sn in CARD.
assumption. assumption.
apply Union_intror.
apply In_singleton.
Qed.


Theorem apply_func_finite :
forall (U1 U2:Type) (f:U1->U2) (A:Ensemble U1),
Finite U1 A -> Finite U2 (apply_func U1 U2 f A).
Proof.
intros U1 U2 f A FINITEA.
destruct(finite_cardinal U1 A FINITEA) as [n nH].
revert A FINITEA nH.
induction n.
(*base*)
intros A FINITEA nH.
inversion nH.
assert(apply_func U1 U2 f (Empty_set U1)=Empty_set U2).
apply apply_func_empty.
assumption.
rewrite H0.
apply Empty_is_finite.
(*inductive case*)
intros A FINITEA nH.
inversion nH. clear n0 H.
assert(apply_func U1 U2 f (Add U1 A0 x)=
 Add U2 (apply_func U1 U2 f A0) (f x) ).
apply apply_func_add.
rewrite H.
apply Add_preserves_Finite.
apply IHn.
rewrite<- H1 in FINITEA.
apply EnsembleSubFinite in FINITEA.
assumption.
assumption.
Qed.





(* REDUCTION OF A SET BY A FUNCTION *)
Inductive EnsembleReduction (U:Type) (f:Operation U)
(S:Ensemble U) (zero:U): U -> Prop :=
|EnsembleReduction_empty: S=Empty_set U ->
  EnsembleReduction U f S zero zero
|EnsembleReduction_add: forall (A:Ensemble U) (x rA:U),
  (EnsembleReduction U f A zero rA) -> ~ In U A x ->
  S=Add U A x -> EnsembleReduction U f S zero (f rA x).

Lemma EnsembleReductionExistence :
forall (U:Type) (f:Operation U) (S:Ensemble U) (zero:U),
Finite U S -> exists red:U,
 EnsembleReduction U f S zero red.
Proof.
intros U f S zero FINITE.
destruct(finite_cardinal U S FINITE) as [n nH].
revert U f S zero FINITE nH.
induction n.
intros U f S zero FINITE nH.
inversion nH.
exists zero.
apply EnsembleReduction_empty. tauto.
intros U f S zero FINITE nH.
specialize IHn with (U:=U) (f:=f).
inversion nH.
assert(FINITEA:Finite U A).
apply EnsembleSubFinite with (a:=x).
rewrite H1. assumption.
specialize IHn with (S:=A) (zero:=zero).
assert(CARDA:cardinal U A n).
apply EnsembleSubCardinal with (a:=x).
assumption. rewrite H1. assumption.
assert(X:=IHn FINITEA CARDA).
destruct X as [r rH].
exists (f r x).
apply EnsembleReduction_add with (A:=A).
assumption. assumption. tauto.
Qed.


Theorem EnsembleReduction_unique :
forall (U:Type) (f:Operation U) (S:Ensemble U) (zero a b:U),
Associativity f -> Commutativity f-> Finite U S ->
EnsembleReduction U f S zero a ->
EnsembleReduction U f S zero b ->
a=b.
Proof.
intros U f S zero a b.
intros ASSOC COMM FINITE HA HB.
destruct(finite_cardinal U S FINITE) as [n nH].
revert a b S FINITE HA HB nH.
induction n.
intros a b S FINITE HA HB nH.
inversion nH.
rewrite<- H in HA.
rewrite<- H in HB.
inversion HA.
inversion HB.
rewrite<- H1.
rewrite<- H3.
tauto.
symmetry in H4. apply DifferentAdd_Empty in H4.
tauto.
symmetry in H2. apply DifferentAdd_Empty in H2.
tauto.

intros a b S FINITE HA HB nH.
inversion HA as [H H0|A x].
inversion HB as [H1 H2|B y].
rewrite<- H0.
rewrite<- H2.
tauto.
rewrite H3 in H.
apply DifferentAdd_Empty in H.
tauto.
inversion HB as [H3 H4|B y rB].
rewrite H3 in H1.
symmetry in H1. apply DifferentAdd_Empty in H1.
tauto.
rewrite H5 in H1.

(*Add U A0 x0 = Add U A x*)
assert(FINITEA:Finite U A).
apply EnsembleSubFinite with (a:=x).
rewrite<- H1. rewrite<-H5. assumption.
assert(CARDA:cardinal U A n).
apply EnsembleSubCardinal with (a:=x).
assumption.
rewrite<- H1. rewrite<-H5. assumption.
assert(CARDB:cardinal U B n).
apply EnsembleSubCardinal with (a:=y).
assumption.
rewrite<- H5. assumption.
assert(FINITEB:Finite U B).
apply EnsembleSubFinite with (a:=y).
rewrite<-H5. assumption.
assert(eqyx:y=x\/y<>x). apply classic.
destruct eqyx as [eqyx|neqyx].
rewrite eqyx in *.
assert(B=A).
apply DisjointAddEquationElim with (x:=x).
assumption. assumption. assumption.
rewrite H7 in *.
assert(rA=rB).
apply IHn with (S:=A).
assumption. assumption. assumption. assumption.
rewrite H8. tauto.
(* neqyx *)
assert(DAEC:=DisjointAddEquationCommon
 U B A y x FINITEB H1 H4 H0 neqyx).
destruct DAEC as [C CH].
destruct CH as [CAddx CH].
destruct CH as [CAddy CH].
destruct CH as [nInCy CH].
destruct CH as [nInCx CH].
destruct CH as [InA0x InAy].
assert(CARDC:cardinal U C (pred n) ).
apply EnsembleSubCardinal with (a:=y).
assumption. rewrite<- CAddy. rewrite<- S_pred with (m:=0).
assumption.
apply inh_card_gt_O with (U:=U) (X:=A).
apply Inhabited_intro with (x:=y).
assumption. assumption.
(*we have C with its cardinal*)
assert(FINITEC:Finite U C).
apply cardinal_finite with (n:=pred n).
assumption.
assert(exists rC:U, EnsembleReduction U f C zero rC).
apply EnsembleReductionExistence.
assumption.
destruct H7 as [rC rCH].
assert(RAC:EnsembleReduction U f A zero (f rC y)).
apply EnsembleReduction_add with (A:=C).
assumption. assumption. assumption.
assert(RBC:EnsembleReduction U f B zero (f rC x)).
apply EnsembleReduction_add with (A:=C).
assumption. assumption. assumption.
(*now we use the induction hypothesis*)
assert(RA:rA=f rC y).
apply IHn with (S:=A).
assumption. assumption. assumption. assumption.
assert(RB:rB=f rC x).
apply IHn with (S:=B).
assumption. assumption. assumption. assumption.
rewrite RA.
rewrite RB.
rewrite ASSOC.
rewrite COMM with (b:=x).
rewrite ASSOC.
tauto.
Qed.

(* Apply f to each element and then
   reduce with g
Note: this is not the same that apply_func
and then reduce
*)
Inductive EnsembleApplyReduction (U1 U2:Type)
(f:U1->U2) (g:Operation U2)
(S:Ensemble U1) (zero:U2): U2 -> Prop :=
|EnsembleApplyReduction_empty: S=Empty_set U1 ->
  EnsembleApplyReduction U1 U2 f g S zero zero
|EnsembleApplyReduction_add:
  forall (A:Ensemble U1) (x:U1) (rA:U2),
  (EnsembleApplyReduction U1 U2 f g A zero rA) ->
  ~ In U1 A x -> S=Add U1 A x ->
  EnsembleApplyReduction U1 U2 f g S zero (g rA (f x)).


Lemma EnsembleApplyReductionExistence :
forall (U1 U2:Type) (f:U1->U2) (g:Operation U2)
(S:Ensemble U1) (zero:U2),
Finite U1 S -> exists red:U2,
 EnsembleApplyReduction U1 U2 f g S zero red.
Proof.
intros U1 U2 f g S zero FINITE.
destruct(finite_cardinal U1 S FINITE) as [n nH].
revert U1 U2 f g S zero FINITE nH.
induction n.
intros U1 U2 f g S zero FINITE nH.
inversion nH.
exists zero.
apply EnsembleApplyReduction_empty. tauto.
intros U1 U2 f g S zero FINITE nH.
specialize IHn with (U1:=U1) (U2:=U2) (f:=f) (g:=g).
inversion nH.
assert(FINITEA:Finite U1 A).
apply EnsembleSubFinite with (a:=x).
rewrite H1. assumption.
specialize IHn with (S:=A) (zero:=zero).
assert(CARDA:cardinal U1 A n).
apply EnsembleSubCardinal with (a:=x).
assumption. rewrite H1. assumption.
assert(X:=IHn FINITEA CARDA).
destruct X as [r rH].
exists (g r (f x)).
apply EnsembleApplyReduction_add with (A:=A).
assumption. assumption. tauto.
Qed.

(*
TODO:

*)



End EnsembleFacts.

