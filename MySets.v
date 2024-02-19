Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.

(* Some bits to be possible used later for a created module hierarchy 

Module Type Elt.
  Parameter elt: Type.
End Elt. 

Module Type MySet (type : Elt).
  Parameter  setf: type.elt -> bool.  
End MySet.

Module Type MyRelation (S : MySet).
  Parameter U, W : Type.
  Definition T := U * W. 

Module MyRelations (S_module : MySet).
  Import S_Module.
*)


Module EB_structs.


Section MySets.

(* Arbitrary type as a module parameter -- type of set elements *)
Variable U : Type.

(* A set is defined as a function returning a Coq proposition 
   (a proof that the given element belongs to a set)
*)
Definition MySet := U -> Prop.

(* Definitions of membership and subset*)
Definition In (x:U) (A:MySet): Prop := A x.

Definition Included (B C:MySet) : Prop := forall x:U, In x B -> In x C.

(* Empty set associated with no possible proofs *)
Inductive Empty_set : MySet :=.

(* the maximal set -- membership of the whole type U *)
Inductive Full_set : MySet :=
    Full_intro : forall x:U, In x Full_set.

(* singleton set *)
Inductive Singleton (x:U) : MySet :=
    In_singleton : In x (Singleton x).

(* set union *)
Inductive Union (B C:MySet) : MySet :=
    | Union_introl : forall x:U, In x B -> In x (Union B C)
    | Union_intror : forall x:U, In x C -> In x (Union B C).

(* adding a single element in to an existing set *)
Definition Add (x:U) (B:MySet) : MySet := Union (Singleton x) B. 

(* Inductively building set intersection *)
Inductive Intersection (B C:MySet) : MySet :=
    Intersection_intro :
    forall x:U, In x B -> In x C -> In x (Intersection B C).

(* set complement *)
Definition Complement (A:MySet) : MySet := fun x:U => ~ In x A.

(* set difference *)
Definition Setminus (B C:MySet) : MySet :=
    fun x:U => In x B /\ ~ In x C.

(* removing a single element from a set *)
Definition Subtract (B:MySet) (x:U) : MySet := Setminus B (Singleton x).

(* a property (proposition) of being doisjoint sets *)
Inductive Disjoint (B C:MySet) : Prop :=
    Disjoint_intro : (forall x:U, ~ In x (Intersection B C)) -> Disjoint B C.

(* a property of being inhabited (i.e., non-empty) *)
Inductive Inhabited (B:MySet) : Prop :=
    Inhabited_intro : forall x:U, In x B -> Inhabited B.

(* a proper subset *)
Definition Strict_Included (B C:MySet) : Prop := Included B C /\ B <> C.

(* sets are the same if they are mutually included *)
Definition Same_set (B C:MySet) : Prop := Included B C /\ Included C B.

(* set terms are substitutable (equal) in Coq if they represent the same sets *)
Axiom Extensionality_MySets : forall A B:MySet, Same_set A B -> A = B.

(* excluded middle axiom for set membership *)
Axiom In_excluded : forall (x:U) (A: MySet), In x A \/ ~ In x A.  


(* one of the essential properties -- repeatedly adding already existing member 
   does not change a set *)
Lemma Add_existing: forall (x:U) (A: MySet), In x A -> (Add x A) = A.
Proof. Admitted.

End MySets.


(* For later: introduce more traditional notation 

Declare Scope set_scope.

Module SetNotations.
Notation "{ }" := Empty_set (format "{ }") : set_scope.
Notation "{ x }" := (Add x Empty_set) : set_scope.
Notation "{ x ; y ; .. ; z }" := (Add x (Add y .. (Add z Empty_set) ..))
  (format "{ '{' x ; '/' y ; '/' .. ; '/' z '}' }") : set_scope.
End SetNotations.
*)


(* Introducing finite sets as sets with additional finiteness property *)
Section FiniteSets.

Variable U : Type.

(* A set is finite is finite if it is empty or is built by adding a single element into a finite set *)
Inductive Finite : MySet U -> Prop :=
    | Empty_is_finite : Finite (Empty_set U)
    | Union_is_finite :
      forall A:Ensemble U,
        Finite A -> forall x:U, ~ In U x A -> Finite (Add U x A).

(* inductive set cardinality *)
Inductive cardinal : MySet U -> nat -> Prop :=
    | card_empty : cardinal (Empty_set U) 0
    | card_add :
      forall (A:Ensemble U) (n:nat),
        cardinal A n -> forall x:U, ~ In U x A -> cardinal (Add U x A) (S n).

(* all finite sets have cardinality *)
Lemma finite_cardinal :
    forall X:MySet U, Finite X -> exists n : nat, cardinal X n.
Proof.
  intros. induction H.
  - exists 0. apply card_empty.
  - destruct IHFinite. exists (S x0). apply card_add; assumption.
Qed.

(* cardinality means finiteness *)
Lemma cardinal_finite :
    forall (X:MySet U) (n:nat), cardinal X n -> Finite X.
Proof.
  intros. induction H.
  - apply Empty_is_finite.
  - apply Union_is_finite; assumption.
Qed.

(* adding a single element preserves finiteness *)
Theorem Add_preserves_Finite :
    forall (X:MySet U) (x:U), Finite X -> Finite (Add U x X).
Proof. 
  intros. pose (Hin := In_excluded U x X). destruct Hin.
  - apply Add_existing in H0. rewrite H0. assumption.
  - apply Union_is_finite; assumption.
Qed.

End FiniteSets.



(* Building relations a special kind of sets -- sets of pairs *)
Section Relations.

(* Two parameters -- types of elements *)
Variable T: Type.
Variable U: Type.

(* Relations -- sets of pairs *)
Definition Relation T U := MySet (T * U).

(* Defining relation domain and range *)
Definition dom (R : Relation T U) : MySet T := 
  fun x => exists y:U, In _ (x,y) R. 

Definition ran (R : Relation T U) : MySet U := 
  fun y => exists x:T, In _ (x,y) R. 

(* Defining inverse relation *)
Definition inverse (R : Relation T U) : Relation U T := 
  fun x => In _ (snd x,fst x) R.


(* Defining domain and range restrictions *)
Definition dom_rest (S : MySet T) (R : Relation T U) : Relation T U :=
  fun x => In _ x R /\ In _ (fst x) S. 

Definition ran_rest (R : Relation T U) (S : MySet U) : Relation T U :=
  fun x => In _ x R /\ In _ (snd x) S. 

(* Defining domain and range subtractions *)
Definition dom_subt (S : MySet T) (R : Relation T U) : Relation T U :=
  fun x => In _ x R /\ ~ In _ (fst x) S. 

Definition ran_subt (R : Relation T U) (S : MySet U) : Relation T U :=
  fun x => In _ x R /\ ~ In _ (snd x) S. 

(* Building relational product *)
Definition product (U V : Type) (A : MySet U) (B : MySet V) : MySet (U * V) :=
  fun x => In _ (fst x)A  /\ In _ (snd x) B.

(* Defining relational image *)
Definition rel_image (S : MySet T) (R : Relation T U) : MySet U :=
  fun y => exists x:T, In _ (x,y) R /\ In _ x S.  

(* Defining relational overriding *)
Definition over (R : Relation T U) (Q : Relation T U) := 
  Union _ Q (dom_subt (dom Q) R).

(* Defining relational composition *)
Definition comp (W : Type) (R : Relation T W) (Q : Relation W U) : Relation T U := 
  fun x => exists y, In _ (fst x,y) R /\ In _ (y,snd x) Q.

(* Property of being a total relation*)
Definition total (R : Relation T U) : Prop := 
  forall x : T, In _ x (Full_set T) -> In _ x (dom R).

(* Property of being a surjective relation *)
Definition surjective (R : Relation T U) : Prop := 
  forall x : U, In _ x (Full_set U) -> In _ x (ran R).


End Relations.


(* Building functions a special kind of relations *)
Section Functions.

Variable T: Type.
Variable U: Type.

(* Functions are relations with functionality property enforced as an axiom *)
Definition Function T U := Relation T U.

Axiom Functionality: forall (T U : Type) (F : Function T U) (x: T) (y z : U), 
  In _ (x,y) F ->  In _ (x,z) F -> y = z.

(* Property of being a injective relation *)
Definition injective (F : Function T U): Prop :=  forall (x y : T) (z : U),  
  In _ (x,z) F ->  In _ (y,z) F -> x = y.  

End Functions.


End EB_structs.