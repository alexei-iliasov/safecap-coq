From Coq Require Import Bool.Bool.
From Coq Require Import Setoids.Setoid.


(* Building finite sets as inductive type*)
Section FinSets.

(*Two parameters -- element type and equivalence (equality) function  for them *)

Variable U : Type.

Variable equiv : U -> U -> bool.

Axiom equiv_comm : forall (x:U) y, equiv x y = equiv y x.

Axiom equiv_trans :  forall (x:U) y z, equiv x y = true -> equiv y z = true -> equiv x z = true.

Axiom equiv_refl : forall (x:U), equiv x x = true.

Axiom equiv_extensionality: forall (x : U) y, equiv x y = true <-> x = y. 


(* Inductive definition -- a finite set either empty or is built by adding one element *)
Inductive FinSet : Type :=
  | Empty_set
  | Add (x : U) (A : FinSet).

(* a singleton set*)
Definition Singleton (x : U) : FinSet := Add x Empty_set.

(* recursively built union of two sets *)
Fixpoint Union (A : FinSet) (B : FinSet) := 
  match A with
  | Empty_set => B
  | Add y A0 => Add y (Union A0 B)
  end.

(* recursively built membership (returning bool) *)
Fixpoint mem (x : U) (A : FinSet) : bool :=
  match A with 
    | Empty_set => false
    | Add y B => (equiv x y) || mem x B
  end.

(* a maximal set as a property (proposition) *)
Definition Full_set (A : FinSet) : Prop :=
  forall (x : U), mem x A = true.

(* set subset *)
Definition Subset (A : FinSet) (B : FinSet) : Prop := 
  (forall x:U, mem x A = true -> mem x B = true).

(* two sets are the same if they are mutaul subsets *)
Definition Same_set (A : FinSet) (B : FinSet) : Prop := 
  Subset A B  /\ Subset B A.

(* sets are equal (substitutable in proofs) if they are the same *)
Axiom set_extensionality: forall (A : FinSet) B, Same_set A B <-> A = B. 

(* Counterpositive  is true in constructive logic *)
Lemma contrapos: forall (A:Prop) (B:Prop), (A -> B) -> ~ B -> ~ A.
Proof. 
  intros. unfold not. intros. apply H in H1. exfalso. unfold not in H0. apply H0. assumption.
Qed.


(* set membership as Coq proposition *)
Definition In (x : U) A : Prop := mem x A = true. 

(* membership excluded middle -- provable, not an axiom *)
Lemma In_excluded_middle: forall (x : U) A, In x A \/ ~ In x A.
Proof. 
  intros. unfold In. destruct (mem x A).
  - auto.
  - right. unfold not. intros. discriminate H. 
Qed.

(* no elements in an empty set *)
Lemma In_Empty: forall (x : U), ~ In x Empty_set.
Proof. 
  intros. unfold In. simpl. unfold not. intros. discriminate.
Qed.

(* only empty set can be a subset of empty set *)
Lemma Subset_empty: forall (A : FinSet), Subset A Empty_set -> A = Empty_set.
Proof.
  intros. induction A as [| x0 A0 HA].
  - reflexivity.
  - rewrite <- set_extensionality. unfold Same_set. split.
    + assumption.
    + unfold Subset. intros. simpl in H0. discriminate.
Qed.


(* an element is a member after addition *)
Lemma In_Add_same: forall (x:U) A, In x (Add x A).
Proof.
  intros. unfold In. simpl. rewrite orb_true_iff. left. rewrite equiv_extensionality. reflexivity.
Qed.

(* element membership for a general case *)
Lemma In_Add: forall (x:U) y A, In x (Add y A) <-> (x = y) \/ In x A.
Proof.
  intros. split. 
  - unfold In. intros.  unfold In in H. simpl in H. rewrite orb_true_iff in H. destruct H.
    + left. apply equiv_extensionality. assumption.
    + right. assumption.
  - intros. destruct H. 
    + rewrite H. apply In_Add_same.
    + unfold In. unfold In in H. simpl. rewrite orb_true_iff. right. assumption.
Qed.


(* two trivial properties for unions involving emprty sets *)
Lemma Union_Empty_left: forall (A : FinSet), Union Empty_set A = A.
Proof.
  intros. induction A as [| x0 A0 HA]; simpl; reflexivity.
Qed.

Lemma Union_Empty_right: forall (A : FinSet), Union A Empty_set = A.
Proof.
  intros. induction A as [| x0 A0 HA].
  - simpl. reflexivity.
  - simpl. rewrite HA. reflexivity.
Qed.


(* membership in Union *)
Lemma In_Union: forall (x:U) A B, In x A -> In x (Union A B).
Proof.
  intros. induction A as [| x0 A0 HA].
  - simpl. exfalso. apply (In_Empty x). assumption.
  - simpl. rewrite In_Add. unfold In in H. simpl in H. rewrite orb_true_iff in H. destruct H.
    + left. rewrite equiv_extensionality in H. assumption.
    + unfold In in HA. apply HA in H. right. unfold In. assumption.
Qed.

Lemma In_Union_either: 
  forall (x:U) A B, In x (Union A B) <-> In x A \/ In x B.
Proof.
  intros. split. 
  - induction A as [| x0 A0 HA].
    + simpl.  intros. right. assumption.
    + intros. unfold In in H. simpl in H. rewrite orb_true_iff in H. destruct H.
      ++ unfold In. simpl. rewrite orb_true_iff. left. left. assumption.
      ++ unfold In. simpl. rewrite orb_true_iff. unfold In in HA. apply HA in H. destruct H.
        ** left. right. assumption.
        ** right. assumption.
  - intros. destruct H.
    + apply In_Union. assumption.
    + induction A as [| x0 A0 HA].
      ++ unfold In. simpl. unfold In in H. assumption.
      ++ unfold In. simpl. rewrite orb_true_iff. unfold In in HA. right. assumption.
Qed.


(* Union commutativity *)
Lemma Union_comm: forall (A : FinSet) B, Union A B = Union B A.
Proof.
  intros. rewrite <- set_extensionality. unfold Same_set. split.
  - unfold Subset. intros. pose (HAB := In_Union_either x A B).  rewrite HAB in H.
    pose (HBA := In_Union_either x B A). rewrite HBA. destruct H.
    + right. assumption.
    + left. assumption.
  - unfold Subset. intros. pose (HAB := In_Union_either x A B). rewrite HAB.
    pose (HBA := In_Union_either x B A). rewrite HBA in H. destruct H.
    + right. assumption.
    + left. assumption.
Qed.


(* Union associativity *)
Lemma Union_assoc: forall (A : FinSet) B C, Union A (Union B C) = Union (Union A B) C.
Proof.
  intros.  rewrite <- set_extensionality. unfold Same_set. split.
  - unfold Subset. intros. pose (HA_BC := In_Union_either x A (Union B C)). 
    rewrite HA_BC in H. destruct H.
    + pose (HAB_C := In_Union_either x (Union A B) C). rewrite HAB_C. left. 
       apply In_Union_either. left. assumption.
    + apply In_Union_either in H. destruct H.
      ++  apply In_Union_either. left. apply In_Union_either. right. assumption. 
      ++ apply In_Union_either. right. assumption.
  - unfold Subset. intros. pose (HAB_C := In_Union_either x (Union A B) C).
    rewrite HAB_C in H. destruct H.
    + apply In_Union_either in H. destruct H.
      ++ apply In_Union_either. left. assumption.
      ++ apply In_Union_either. right. apply In_Union_either. left. assumption.
    + apply In_Union_either. right. apply In_Union_either. right. assumption.
Qed.  


(* moving Add out of Union (second argument) *)
Lemma Union_Add_right: forall (x:U) A B, Union A (Add x B) = Add x (Union A B).
Proof.
  intros. rewrite (Union_comm A (Add x B)). simpl. rewrite (Union_comm B A). reflexivity.
Qed.


(* excluded middle for equivalence *)
Lemma equiv_excluded_middle: forall (x : U) y, equiv x y = true \/ equiv x y = false.
Proof.
  intros. destruct (equiv x y). 
  - auto.
  - right. reflexivity. 
Qed.

(* set extensionality for the false case *)
Lemma equiv_extensionality_false: forall (x:U) y, equiv x y = false <-> ~ (x = y).
Proof.
  - intros. pose (Hequiv := equiv_excluded_middle x y). destruct Hequiv.
    + split.
      ++ intros. rewrite H in H0. discriminate.
      ++ rewrite equiv_extensionality in H. intros. exfalso. apply H0. assumption.
    + split. 
      ++ intros. unfold not. intros. rewrite H1 in H. rewrite equiv_refl in H. discriminate.
      ++ intros. assumption.
Qed.



(* equivalence and negation*)
Lemma equiv_false:  forall (x : U) y, equiv x y = false -> ~ (x = y). 
Proof. 
  intros. unfold not. intros. rewrite <- equiv_extensionality in H0. rewrite H in H0. discriminate.
Qed.


(* membership in singleton sets *)
Lemma In_Singleton: forall (x:U), In x (Singleton x).
Proof.
  intros. unfold Singleton. unfold In. simpl. rewrite equiv_refl. simpl. reflexivity.
Qed.

Lemma In_Singleton_only: forall (x:U) y, In x (Singleton y) -> x = y.
Proof.
  intros. unfold Singleton in H. unfold In in H. simpl in H. rewrite orb_false_r in H.
  rewrite equiv_extensionality in H. assumption.
Qed.

(* membership inside a (non-empty) set*)
Lemma In_inside: forall (x:U) x0 A, In x (Add x0 A) -> x <> x0 -> In x A.
Proof. 
  intros. apply In_Add in H. destruct H. 
  + rewrite H in H0. unfold not in H0. exfalso. apply H0. reflexivity.
  + assumption.
Qed.

(* The opposite by contrapositive *)
Lemma In_inside_not: forall (x:U) x0 A, x <> x0 -> ~ In x A -> ~In x (Add x0 A).
Proof. 
  intros x x0 A H. apply contrapos. intros. apply (In_inside x x0 A); assumption.
Qed.


(* subset properties *)
Lemma Add_subset: forall (x:U) A, Subset A (Add x A).
Proof.
  intros. unfold Subset. intros. simpl. rewrite H. rewrite orb_comm. simpl. reflexivity.
Qed.

Lemma In_Subset:  forall (x:U) A B, In x A -> Subset A B -> In x B.
Proof.
  intros. unfold Subset in H0. unfold In in H. unfold In. apply H0. assumption.
Qed.

Lemma Subset_refl: forall (A : FinSet), Subset A A.
Proof. 
  intros. unfold Subset. intros. assumption.
Qed.

Lemma Subset_trans: forall (A : FinSet) B C, Subset A B -> Subset B C -> Subset A C.
Proof. 
  intros. unfold Subset. intros. unfold Subset in H. unfold Subset in H0.
  apply H in H1. apply H0 in H1. assumption.
Qed.

(*Subset after adding*)
Lemma Subset_Add: forall (x:U) A B, Subset (Add x A) B -> Subset A B. 
Proof.
  intros x A B. unfold Subset. intros. simpl in H. pose (H1 := H x0). rewrite orb_true_iff in H1.
  apply H1. right. assumption.
Qed.

(* Subset and Union -- Union as max, Subset as an ordering*)
Lemma Subset_Union_left: forall (A : FinSet) B C, Subset (Union A B) C -> Subset A C.
Proof.
  intros A B C.  unfold Subset. induction A as [| x0 A0 HA].
  - intros. simpl in H0. discriminate.
  - intros. simpl in H0. rewrite orb_true_iff in H0. simpl in H. destruct H0.
    + pose (H1 := H x). rewrite orb_true_iff in H1. rewrite H0 in H1. apply H1. left. reflexivity.
    + pose (H1 := H x). rewrite orb_true_iff in H1. pose (HIn := In_Union x A0 B). 
       unfold In in HIn. apply HIn in H0. apply H1. right. assumption.
Qed.

Lemma Subset_Union_right: forall (A : FinSet) B C, Subset (Union A B) C -> Subset B C.
Proof.
  intros. rewrite Union_comm in H.  apply (Subset_Union_left B A C). assumption.
Qed.


(* Important -- Adding repeatedly the same element does not change a set *)
Lemma Add_same: forall (x : U) A, Add x (Add x A) = Add x A.
Proof. 
  intros. apply set_extensionality. unfold Same_set. split.
  - unfold Subset. intros. simpl. rewrite orb_true_iff. simpl in H. rewrite orb_true_iff in H.
    destruct H. 
    + left. assumption.
    + rewrite orb_true_iff in H. destruct H.
      ++ left. assumption.
      ++ right. assumption.
  - unfold Subset. intros. simpl. rewrite orb_true_iff. simpl in H. rewrite orb_true_iff in H.
    destruct H.
    + left. assumption.
    + rewrite orb_true_iff. right. right. assumption.
Qed.

(* Important -- Adding element in different order does not change a set *)
Lemma Add_twice: forall (x : U) y A, Add x (Add y A) = Add y (Add x A).
Proof. 
  intros. apply set_extensionality. unfold Same_set. split.
  - unfold Subset. intros. simpl. rewrite orb_true_iff. simpl in H. rewrite orb_true_iff in H.
    destruct H.
    + right. rewrite orb_true_iff. left. assumption.
    + rewrite orb_true_iff in H. destruct H.
      ++ left. assumption.
      ++ right. rewrite orb_true_iff. right. assumption.
  - unfold Subset. intros. simpl. rewrite orb_true_iff. simpl in H. rewrite orb_true_iff in H.
    destruct H.
    + right. rewrite orb_true_iff. left. assumption.
    + rewrite orb_true_iff in H. destruct H.
      ++ left. assumption.
      ++ right. rewrite orb_true_iff. right. assumption.
Qed.

(* Adding already existing element does not change a set *)
Lemma Add_existing: forall (x : U) A, In x A -> Add x A = A.
Proof.
  intros. apply set_extensionality. unfold Same_set. split; unfold Subset; intros.
  - simpl in H0. rewrite orb_true_iff in H0. destruct H0.
    + apply equiv_extensionality in H0. unfold In in H. rewrite H0. assumption.
    + assumption.
  - simpl. rewrite orb_true_iff. right. assumption.
Qed.


(* Some trivila useful lemmas about Add *)
Lemma trivial_Add: forall (x:U) A, Add x A = A -> In x A.
Proof.
  intros. induction A as [| x0 A0 HA] eqn:E.
  - simpl in H. inversion H.
  - inversion H. rewrite Add_same. apply In_Add. left. reflexivity.
Qed.

Lemma trivial_Add_contrapos: forall (x:U) A, ~ (In x A) -> ~ (Add x A = A).
Proof.
  intros x A. apply contrapos. apply trivial_Add.
Qed. 


(* Definition of removing a single element *)
Fixpoint Remove (x : U) (A : FinSet) : FinSet :=
  match A with 
    | Empty_set => Empty_set
    | Add y B => if equiv x y then B else Add y (Remove x B)  
  end.

(* Removing non-existing element does not change a set *)
Lemma Remove_noexist: forall (x : U) A, ~(In x A) -> (Remove x A) = A.
Proof.
  intros. induction A as [| x0 A0 HA].
  - simpl. reflexivity.
  - simpl. pose (Hequiv := equiv_excluded_middle x x0). destruct Hequiv.
    + rewrite H0. rewrite equiv_extensionality in H0. rewrite H0 in H. unfold not in H. 
       exfalso. apply H. apply In_Add_same.
    + rewrite H0. rewrite In_Add in H. pose (HIn := In_excluded_middle x A0). 
       destruct HIn.
      ++ unfold not in H. exfalso. apply H. right. assumption.
      ++ apply HA in H1. rewrite H1. reflexivity.
Qed.

(* Removing just added element does not change a set *)
Lemma Remove_Add: forall (x : U) A, Remove x (Add x A) = A.
Proof.
  intros. induction A as [| x0 A0 HA]. 
  - simpl. rewrite equiv_refl. reflexivity.
  - simpl. rewrite equiv_refl. reflexivity.
Qed.


(* Adding after removing is the same as just adding *)
Lemma Add_Remove: forall (x:U) A, Add x (Remove x A) = Add x A.
Proof. 
  intros. induction A as [| x0 A0 HA]. 
  - simpl. reflexivity.
  - simpl. pose (Hequiv := equiv_excluded_middle x x0). destruct Hequiv.
    + rewrite H. rewrite equiv_extensionality in H. rewrite H. rewrite Add_same. reflexivity.
    + rewrite H. rewrite Add_twice. rewrite HA. rewrite Add_twice. reflexivity.
Qed.

Lemma Remove_Add_different: 
  forall (x : U) y A, ~(x = y) -> Remove x (Add y A) = Add y (Remove x A).
Proof. 
  intros. induction A as [| x0 A0 HA].
  - simpl. pose (Hequiv := equiv_excluded_middle x y). destruct Hequiv.
    + rewrite equiv_extensionality in H0. unfold not in H. exfalso. apply H. assumption.
    + rewrite H0. reflexivity.
  - simpl. pose (Hequiv := equiv_excluded_middle x y). destruct Hequiv.
    + rewrite H0. pose (Hequiv := equiv_excluded_middle x x0). destruct Hequiv.
      ++ rewrite H1. rewrite equiv_comm in H1. apply (equiv_trans x0 x y) in H1.
        ** rewrite equiv_extensionality in H1. rewrite H1. reflexivity.
        ** assumption.
      ++ rewrite H1. rewrite equiv_extensionality in H0. unfold not in H. exfalso. apply H. assumption.
    + rewrite H0. reflexivity.
Qed. 


(* Order of removing elements does not matter *)
Lemma Remove_twice: forall (x:U) y A, Remove x (Remove y A) = Remove y (Remove x A).
Proof.
  intros. induction A as [| x0 A0 HA].
  - simpl. reflexivity.
  - simpl. pose (Hequiv := equiv_excluded_middle y x0). destruct Hequiv.
    + rewrite H. pose (Hequiv := equiv_excluded_middle x x0). destruct Hequiv.
      ++ rewrite H0. rewrite equiv_comm in H. pose (Hxy := equiv_trans x x0 y). 
           apply Hxy in H0.
        ** rewrite equiv_extensionality in H0. rewrite H0. reflexivity.
        ** assumption.
      ++ rewrite H0. rewrite equiv_extensionality in H. rewrite H. rewrite Remove_Add. reflexivity.
    + rewrite H. pose (Hequiv := equiv_excluded_middle x x0). destruct Hequiv.
      ++ rewrite H0. rewrite equiv_extensionality in H0. rewrite <- H0. rewrite Remove_Add.
           reflexivity.
      ++  rewrite H0. rewrite equiv_extensionality_false in H0. 
            apply (Remove_Add_different x x0 (Remove y A0)) in H0. rewrite H0.
            rewrite equiv_extensionality_false in H. 
            apply (Remove_Add_different y x0 (Remove x A0)) in H.
            rewrite H. rewrite HA. reflexivity.
Qed. 

(*Removing an element makes a subset*)
Lemma Remove_subset: forall (x : U) A, Subset (Remove x A) A.
Proof.
  intros. unfold Subset. intros. induction A as [| y A0 HA]. 
  - simpl in H. discriminate.
  - simpl. simpl in H. pose (Hequiv := equiv_excluded_middle x y). destruct Hequiv.
    + rewrite H0 in H. rewrite orb_true_iff. right. assumption.
    + rewrite H0 in H. rewrite orb_true_iff. simpl in H. rewrite orb_true_iff in H. destruct H.
      ++ left. assumption.
      ++ apply HA in H. right. assumption.
Qed.


(* A set with no repeated elements in its syntactic structure - inductive definition *)
Inductive TrueSet : FinSet -> Prop :=
  | TrueSet_empty: TrueSet Empty_set
  | TrueSet_add (x : U) (A : FinSet): TrueSet A -> ~ In x A -> TrueSet (Add x A).  

(* A set with no repeated elements in its syntactic structure - boolean definition*)
Fixpoint TrueSet_bool (A : FinSet) : bool :=
  match A with
    | Empty_set => true
    | Add x A0 => if mem x A0 then false else TrueSet_bool A0
  end.  

(* Connection between the two definitions *)
Lemma TrueSet_iff: forall A, TrueSet A <-> TrueSet_bool A = true.
Proof. 
  intros. split.
  - induction A as [| x0 A0 HA].
    + intros. simpl. reflexivity.
    + simpl. intros. pose (Hmem := In_excluded_middle x0 A0). destruct Hmem.
      ++ inversion H. unfold not in H4. exfalso. apply H4. assumption.
      ++ inversion H. unfold In in H4. apply not_true_is_false in H4. rewrite H4. apply HA. assumption.
  - induction A as [| x0 A0 HA].
    + intros. apply TrueSet_empty.
    + intros. apply TrueSet_add.
      ++ simpl in H. pose (Hmem := In_excluded_middle x0 A0). destruct Hmem.
        ** unfold In in H0. rewrite H0 in H. discriminate.
        ** unfold In in H0.  apply not_true_is_false in H0. rewrite H0 in H. apply HA. assumption.
      ++ simpl in H. pose (Hmem := In_excluded_middle x0 A0). destruct Hmem.
        ** unfold In in H0. rewrite H0 in H. discriminate.
        ** assumption.
Qed.

Lemma TrueSet_mono: forall (x : U) A, TrueSet (Add x A) -> TrueSet A. 
Proof. 
  intros. inversion H. assumption.
Qed.

(* For a true set, removing element means that it does not exist anymore in a set *)
Lemma Remove_In: forall (x : U) A, TrueSet A -> ~ In x (Remove x A).
Proof. 
  intros. induction A as [| x0 A0 HA].
  - simpl. unfold not. intros. pose (H1 := In_Empty x). apply H1. assumption.
  - simpl. pose (Hequiv := equiv_excluded_middle x x0). destruct Hequiv.
    + rewrite H0. inversion H. rewrite equiv_extensionality in H0. rewrite H0. assumption.
    + rewrite H0. inversion H. apply In_inside_not. 
      ++ rewrite equiv_extensionality_false in H0. assumption.
      ++ apply HA. assumption.
Qed.


(* For a true set, removing element repeatedly does not additionally affect a set *)
Lemma Remove_same: forall (x : U) A, TrueSet A -> Remove x (Remove x A) = Remove x A.
Proof.
  intros. induction A as [| x0 A0 HA].
  - simpl. reflexivity.
  - pose (Hequiv := equiv_excluded_middle x x0). destruct Hequiv.
    + rewrite equiv_extensionality in H0.  rewrite <- H0. apply (Remove_In x0 (Add x0 A0)) in H.
       rewrite <- H0 in H. apply Remove_noexist in H. assumption.
    + apply equiv_extensionality_false in H0. pose (H1 := Remove_Add_different x x0 A0). 
       pose (H2 := Remove_Add_different x x0 (Remove x A0)). rewrite H1.
      ++ inversion H. apply HA in H5. rewrite H5 in H2. apply H2. assumption.
      ++ assumption.
Qed.


(* Definition of a set diffefrence *)
Fixpoint Set_diff (A : FinSet) B : FinSet := 
  match B with
    | Empty_set => A
    | Add y B0 => Set_diff (Remove y A) B0
  end.

(* Connection between set difference and Remove*)
Lemma Remove_set_diff: forall (x : U) A, Remove x A = Set_diff A (Singleton x).
Proof.
  intros. unfold Singleton, Set_diff. reflexivity.
Qed.


(* two simple properties of set difference *)
Lemma Set_diff_empty: forall (A : FinSet), Set_diff A Empty_set = A. 
Proof. 
  intros. induction A as [| x0 A0 HA]; simpl; reflexivity.
Qed.

Lemma Set_diff_same: forall (A : FinSet), Set_diff A A = Empty_set. 
Proof. 
  intros. induction A as [| x0 A0 HA].
  - simpl. reflexivity.
  - simpl. rewrite equiv_refl. assumption.
Qed.

(* Monotonicity of membership *)
Lemma In_Add_exists: forall (x : U) x0 A, In x A -> In x (Add x0 A).
Proof.
 intros. unfold In. simpl. rewrite orb_true_iff. unfold In in H. right. assumption.
Qed.

(* Antimonotonicity of non-membership *)
Lemma In_Add_noexist: forall (x : U) x0 A, ~ In x (Add x0 A) -> ~ In x A.
Proof.
  intros x x0 A. apply contrapos. apply In_Add_exists.
Qed.


(* Set_diff and Remove can be swapped *)
Lemma Set_diff_Remove: 
  forall (x: U) A B, Set_diff (Remove x A) B = Remove x (Set_diff A B).
Proof.
  intros. rewrite <- set_extensionality. unfold Same_set. split.
  - generalize dependent A. induction B as [| y0 B0 HB].
    + simpl. intros. apply Subset_refl.
    + simpl. intros. pose (H := HB (Remove y0 A)). rewrite Remove_twice. assumption.
  - generalize dependent A. induction B as [| y0 B0 HB].
    + simpl. intros. apply Subset_refl.
    + simpl. intros. pose (H := HB (Remove y0 A)). rewrite (Remove_twice y0 x A). assumption.
Qed.


(* Add can be moved out of Set_diff *)
Lemma Set_diff_Add: forall (x : U) A B, ~ In x B -> Set_diff (Add x A) B = Add x (Set_diff A B).
Proof.
  intros. induction B as [| x0 B0 HB].
  - simpl. reflexivity.
  - simpl. pose (Hequiv := equiv_excluded_middle x0 x). destruct Hequiv.
    + rewrite H0. rewrite equiv_extensionality in H0. rewrite H0 in H. unfold not in H.
       exfalso. apply H. apply In_Add_same.
    + rewrite H0. rewrite equiv_extensionality_false in H0. pose (H1 := Remove_Add_different x0 x).
       pose (H2 := (H1 A) H0). rewrite <- H2. rewrite Set_diff_Remove. rewrite Set_diff_Remove.
       pose (H3 := H1 (Set_diff A B0) H0). rewrite <- H3.  apply In_Add_noexist in H. apply HB in H.
       rewrite H. reflexivity.
Qed.

(* Removing a different element does not affect membership *)
Lemma In_Remove: forall (x : U) y A, (x <> y) -> In x (Remove y A) -> In x A.
Proof.
  intros. induction A as [| x0 A0 HA].
  - simpl in H0. assumption.
  - pose (Hequiv := equiv_excluded_middle y x0). destruct Hequiv.
    + rewrite equiv_extensionality in H1. rewrite H1 in H0. rewrite Remove_Add in H0.
       apply In_Add. right. assumption.
    + apply In_Add. pose (Hequiv := equiv_excluded_middle x x0). destruct Hequiv.
      ++ rewrite equiv_extensionality in H2. left. assumption.
      ++ right. apply HA. rewrite equiv_extensionality_false in H1. 
           rewrite (Remove_Add_different _ _ _ H1) in H0. rewrite equiv_extensionality_false in H2.
           apply In_Add in H0. destruct H0.
        ** unfold not in H2. exfalso. apply H2. assumption.
        ** assumption.
Qed.


(* Subset and Add connection *)
Lemma Subset_Add_iff: forall (x:U) A B, Subset (Add x A) B <-> In x B /\ Subset A B.
Proof.
  intros. split.
  - intros. unfold Subset in H. simpl in H. split.
    + unfold In. apply H. rewrite orb_true_iff. left. apply equiv_refl.
    + unfold Subset. intros. apply H. rewrite orb_true_iff. right. assumption.
  - unfold Subset. intros. simpl in H0. rewrite orb_true_iff in H0. destruct H0.
    + destruct H. rewrite equiv_extensionality in H0. rewrite <- H0 in H. unfold In in H. assumption.
    + apply H. assumption.
Qed.


(*

Lemma TrueSet_Subset: forall (x : U) A B, TrueSet A -> Subset B A -> TrueSet B.
Proof.
  intros. induction B as [| y0 B0 HB].
  - apply TrueSet_empty.
  - rewrite Subset_Add_iff in H0. destruct H0. apply TrueSet_add.
    + apply HB. assumption.
    +

 induction A as [| x0 A0 HA] eqn:HE2.
    + unfold Subset in H0. simpl in H0. pose (H1 := H0 y0). rewrite orb_true_iff in H1. 
       exfalso. apply diff_false_true. apply H1. left. apply equiv_refl.
    + inversion H. apply TrueSet_add.
           


Lemma In_Set_diff: forall (x : U) A B, TrueSet A = true -> In x (Set_diff A B) -> In x A /\  ~ (In x B).
Proof. 
  intros. induction B as [| x0 B0 HB].
  - simpl in H. split.
    + assumption.
    + unfold In. simpl. unfold not. intros. discriminate.
  - simpl in H0. pose (Hequiv := equiv_excluded_middle x x0). destruct Hequiv.
    + rewrite equiv_extensionality in H1. rewrite <- H1 in H0. rewrite Set_diff_Remove in H0.
       Search (In ?x (Remove ?x ?A)). 


(*
Lemma TrueSet_Subset: forall (x : U) A B, TrueSet A = true -> Subset B A -> TrueSet B = true.
Proof.
  intros. induction B as [| y0 B0 HB].
  - simpl. reflexivity.
  - simpl. pose (HIn := In_excluded_middle y0 B0). unfold In in HIn. destruct HIn.
    + rewrite H1.

  - apply Subset_empty in H0. rewrite H0. simpl. reflexivity. 
  - apply HA.
    + apply (TrueSet_mono x0). assumption.
    + simpl in H. pose (HIn := In_excluded_middle x0 A0). unfold In in HIn. destruct HIn. 
      ++ rewrite H1 in H. discriminate.
      ++ apply not_true_is_false in H1. rewrite H1 in H. unfold Subset in H0. unfold Subset.
           intros. apply H0 in H2. simpl in H2. rewrite orb_true_iff in H2. destruct H2.
        ** rewrite equiv_extensionality in H2. rewrite H2. 

Lemma forall (x : U) A B, Subset (Set_diff A (Add x B)) (Set_diff A B).
*)




Lemma Subset_Remove: 
  forall (x : U) A B, TrueSet A = true -> TrueSet B = true -> Subset A B -> 
    Subset (Remove x A) (Remove x B).
Proof.
  intros.
  - unfold Subset. intros. induction A as [| x1 A1 HA].
    + simpl in H0. discriminate.
    + apply HA.
      ++  apply TrueSet_mono in H. assumption. 
      ++ apply Subset_Add in H1. assumption.
      ++  

Lemma Set_diff_mono_left:  
  forall (A : FinSet) A' B, Subset A A' -> Subset (Set_diff A B) (Set_diff A' B).
Proof. 
  intros. generalize dependent A. generalize dependent A'. induction B as [| x0 B0 HB].
  - intros. rewrite Set_diff_empty. rewrite Set_diff_empty. assumption.
  - intros. simpl. rewrite Set_diff_Remove.  rewrite Set_diff_Remove.


Lemma In_Set_diff: forall (x : U) A B, In x (Set_diff A B) -> In x A /\  ~ (In x B).
Proof. 
  intros. induction B as [| x0 B0 HB].
  - simpl in H. split.
    + assumption.
    + unfold In. simpl. unfold not. intros. discriminate.
  - simpl in H.

Lemma Set_diff_bigger:  forall (A : FinSet) B, Subset A B -> Set_diff A B = Empty_set.  
Proof. 
  intros. induction B as [| x0 B0 HB].
  - apply Subset_empty in H. rewrite H. rewrite Set_diff_empty. reflexivity.
  - simpl.
*)


(*
Lemma Set_diff_In: forall (x:U) A B, In x (Set_diff A B) -> In x A /\ ~ (In x B).
Proof.
  intros. induction B as [| x0 B0 HB].
  - simpl in H. split.
    + assumption.
    + unfold In. simpl. unfold not. intros. discriminate.
  - simpl in H.

Lemma Diff_Union_distr: 
  forall (A : FinSet) B C, Set_diff (Union A B) C = Union (Set_diff A C) (Set_diff B C).
Proof.
  intros. apply set_extensionality. unfold Same_set. split.
  - unfold Subset. induction A as [| x0 A0 HA].
    + simpl. intros.

*)


(* Set intersection as a Coq proposition *)
Definition Inter (A : FinSet) B  C: Prop := 
  forall (x : U), In x C -> In x A /\ In x B. 

(* Set comprehension? *)

End FinSets.


(* Defining finite relations*)
Section FinRelations.

(* Section parameters - two arbitrary types and equivalence functions for them *)
Variable T: Type.
Variable U: Type.

Definition Relation T U := FinSet (T * U).


Variable equivT : T -> T -> bool.

Axiom equivT_comm : forall (x:T) y, equivT x y = equivT y x.

Axiom equivT_trans :  forall (x:T) y z, equivT x y = true -> equivT y z = true -> equivT x z = true.

Axiom equivT_refl : forall (x:T), equivT x x = true.

Axiom equivT_extensionality: forall (x : T) y, equivT x y = true <-> x = y. 


Variable equivU : U -> U -> bool.

Axiom equivU_comm : forall (x:U) y, equivU x y = equivU y x.

Axiom equivU_trans :  forall (x:U) y z, equivU x y = true -> equivU y z = true -> equivU x z = true.

Axiom equivU_refl : forall (x:U), equivU x x = true.

Axiom equivU_extensionality: forall (x : U) y, equivU x y = true <-> x = y. 


(* Equivalence for product type defined via the corresponding given equivalences *)
Definition equivTU (x : T*U) (y : T*U) : bool := equivT (fst x) (fst y) &&  equivU (snd x) (snd y).


(* Recursively constructing domain, range, inverse for relations*)
Fixpoint dom (R : Relation T U) : FinSet T := 
  match R with
  | Empty_set _ => Empty_set _
  | Add _ (x,y) R0 => Add _ x (dom R0)
  end. 

Fixpoint ran (R : Relation T U) : FinSet U := 
  match R with
  | Empty_set _ => Empty_set _
  | Add _ (x,y) R0 => Add _ y (ran R0)
  end. 

Fixpoint inverse (R : Relation T U) : Relation U T := 
  match R with
  | Empty_set _ => Empty_set _
  | Add _ (x,y) R0 => Add _ (y,x) (inverse R0)
  end.


(* Recursively constructing domain/rangerestrictions and subtractions *)
Fixpoint dom_rest (S : FinSet T) (R : Relation T U) : Relation T U :=
  match R with
  | Empty_set _ => Empty_set _
  | Add _ (x,y) R0 => if mem _ equivT x S then Add _ (x,y) (dom_rest S R0) else dom_rest S R0
  end. 

Fixpoint ran_rest (S : FinSet U) (R : Relation T U) : Relation T U :=
  match R with
  | Empty_set _ => Empty_set _
  | Add _ (x,y) R0 => if mem _ equivU y S then Add _ (x,y) (ran_rest S R0) else ran_rest S R0
  end. 

Fixpoint dom_subt (S : FinSet T) (R : Relation T U) : Relation T U :=
  match R with
  | Empty_set _ => Empty_set _
  | Add _ (x,y) R0 => if mem _ equivT x S then dom_subt S R0 else Add _ (x,y) (dom_subt S R0)
  end. 

Fixpoint ran_subt (S : FinSet U) (R : Relation T U) : Relation T U :=
  match R with
  | Empty_set _ => Empty_set _
  | Add _ (x,y) R0 => if mem _ equivU y S then ran_subt S R0 else Add _ (x,y) (ran_subt S R0)
  end. 


(* Defining relational image *)
Definition rel_image (S : FinSet T) (R : Relation T U) : FinSet U :=
  ran (dom_rest S R).


(* Defining relational overriding *)
Definition over (R : Relation T U) (Q : Relation T U) := 
  Union _ Q (dom_subt (dom Q) R).


(* Defining a property of being total relation *)
Definition total (R : Relation T U) : Prop := 
  forall (x : T) A, Full_set _ equivT A -> In _ equivT x A -> In _ equivT x (dom R).


(* Defining a property of being surjective relation *)
Definition surjective (R : Relation T U) : Prop := 
  forall (x : U) A, Full_set _ equivU A -> In _ equivU x A -> In _ equivU x (ran R).


(* Defining a property of relational product *)
Definition product (A : FinSet T) (B : FinSet U) (C : Relation T U) : Prop :=
  forall (x : T) (y : U), In _ equivT x A  -> In _ equivU y B -> In _ equivTU (x,y) C.



(*
Definition comp (R : Relation T W) (Q : Relation W U) : Relation T U := 
  fun x => exists y, In _ (fst x,y) R /\ In _ (y,snd x) Q.
*)


End FinRelations
