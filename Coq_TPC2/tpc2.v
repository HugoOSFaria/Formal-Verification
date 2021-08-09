Set Implicit Arguments.
Require Import List.


Inductive In (A:Type) (y:A) : list A -> Prop :=
  | InHead : forall (xs:list A), In y (cons y xs)
  | InTail : forall (x:A) (xs:list A), In y xs -> In y (cons x xs).

Inductive Prefix (A:Type) : list A -> list A -> Prop :=
  | PreNil : forall (l:list A), Prefix nil l
  | PreCons : forall (x:A) (l1 l2:list A), Prefix l1 l2 -> Prefix (x::l1) (x::l2).

Inductive SubList (A:Type) : list A -> list A -> Prop :=
  | SLnil : forall (l:list A), SubList nil l
  | SLcons1 : forall (x:A) (l1 l2:list A), SubList l1 l2 -> SubList (x::l1) (x::l2)
  | SLcons2 : forall (x:A) (l1 l2:list A), SubList l1 l2 -> SubList l1 (x::l2).

Lemma ex1 : SubList (5::3::nil)  (5::7::3::4::nil).
Proof.
  constructor.
  constructor.
  constructor.
  constructor.
Qed.

Lemma ex1b : forall (A:Type) (l:list A), SubList l l.
Proof.
  intros.
  induction l.
  - constructor.
  - constructor.
    assumption.
Qed.

Lemma ex1c : forall (A B:Type) (f:A->B) (l1 l2:list A), SubList l1 l2 -> SubList (map f l1) (map f l2).
Proof.
  intros.
  induction H.
  - constructor.
  - simpl.
    constructor.
    assumption.
  - simpl.
    constructor.
    assumption.
Qed.

Lemma ex1d : forall (A:Type) (x:A) (l : list A), In x l -> exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction H.
  exists nil. exists xs. simpl. reflexivity.
  destruct IHIn as [I1 H1]. destruct H1 as [I2 H1]. exists (x0::I1). exists I2.  rewrite <-app_comm_cons.
  rewrite H1. reflexivity.
Qed.

Fixpoint drop (A:Type) (n:nat) (l : list A)  : list A :=  
  match n with
  | 0 => l (* Caso seja drop 0, o resultado é a lista *)
  | S n' => drop n' (tl l) (* Caso seja outro valor, retira-se 1 ao valor e faz-se sobre a cauda *)
  end.

Lemma ex2a : drop 2 (5::7::3::4::nil) = 3::4::nil.
Proof.
  constructor.
Qed.

Lemma ex2b : forall (A:Type) (n:nat) (l:list A), SubList (drop n l) l.
Proof.
  intros H n.
  induction n.
  - induction l.
    * constructor.
    * constructor.
      apply IHl.
  - induction l.
    * simpl.
      apply IHn.
    * constructor.
      simpl.
      apply IHn.
Qed.

Inductive Sorted : list nat -> Prop := 
  | sorted0 : Sorted nil  (* Caso vazio *)
  | sorted1 : forall a:nat, Sorted (a :: nil) (* Ultimo elemento da lista *) 
  | sorted2 : forall (a1 a2:nat) (l:list nat), a1 <= a2 -> Sorted (a2 :: l) -> Sorted (a1 :: a2 :: l). (* Caso geral *)

Lemma ex3a : forall (x y:nat) (l:list nat), x<=y -> (Sorted (y::l)) -> Sorted (x::l).
Proof.
  intros.
  induction l.
  - constructor.
  - constructor.
    + rewrite H. inversion H0. exact H3. 
    + inversion H0. exact H5.
    
Qed.

Lemma sorted2 : forall (x y:nat) (l:list nat), Sorted(x::y::l) -> x<=y. (* Auxiliar para o caso em que temos 2 valores da lista no Sorted*)
Proof.
  intros.
  inversion H.
  assumption.
Qed.

Lemma sortedAux: forall (x y:nat) (l:list nat), x<=y -> Sorted(x::y::l) -> Sorted(x::l). (* Mais uma auxiliar para o caso em que temos 2 valores da lista*)
Proof.
  intros.
  inversion H0.
  generalize H5.
  generalize H3.
  apply ex3a.
Qed.

Lemma ex3b : forall (x y:nat) (l:list nat), (In y l) /\ (Sorted (x::l)) -> x <= y.
Proof.
  intros.
  induction H.
  induction H.
  - generalize H0. apply sorted2.
  - inversion H0. 
    apply IHIn. 
    generalize H0. 
    apply sortedAux. 
    assumption. 
Qed.

Lemma ex4a : forall (A:Type) (l:list A), Prefix l l.
Proof.
  intros.
  induction l.
  - constructor.
  - constructor.
    assumption.
Qed.

Lemma concatenate_extra : forall (A:Type) (l1 l2:list A), Prefix l1 l2 -> exists l3:list A, l2 = l1 ++ l3. 
Proof.
  intros.
  induction H.
  - exists l. 
    rewrite app_nil_l.
    trivial.
  - destruct IHPrefix.
    exists x0. 
    rewrite H0. 
    apply app_comm_cons.
Qed.

Lemma concatenate_prefix : forall (A:Type) (l1 l2:list A), Prefix l1 (l1++l2).
Proof.
  intros.
  induction l1.
  - simpl. constructor.
  - simpl. constructor. exact IHl1.
Qed.

Lemma ex4_b : forall (A:Type) (l1 l2 l3:list A), Prefix l1 l2 /\ Prefix l2 l3 -> Prefix l1 l3.
Proof.
  intros.
  destruct H as [H1 H2].
  apply concatenate_extra in H1.
  destruct H1.
  apply concatenate_extra in H2.
  destruct H2.
  rewrite  H0.
  rewrite  H.
  assert(((l1++x)++x0)=(l1++(x++x0))). 
  - apply app_assoc_reverse. 
  - rewrite H1.
    apply concatenate_prefix.
Qed.

Lemma concatenate_aux : forall (A:Type) (x:A) (l1 l2:list A), l1 = l2 -> x::l1 = x::l2.
Proof.
  intros.
  rewrite H.
  trivial.
Qed.

Lemma ex4c : forall (A:Type) (l1 l2:list A), Prefix l1 l2 /\ Prefix l2 l1 -> l1 = l2.
Proof.
  intros.
  destruct H.
  induction H.
  - inversion H0. trivial.
  - apply concatenate_aux.
    apply IHPrefix.
    inversion H0.
    exact H2.
Qed.