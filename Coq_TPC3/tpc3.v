Require Import List.
Require Import ZArith.
Require Extraction. 
Set Implicit Arguments.
Extraction Language Haskell.

(*Ex 1 a*)

Inductive nList (A:Type) : nat -> A -> (list A) -> Prop :=
  | nIs0 : forall (a:A), nList 0 a nil
  | nIsNormal : forall (n:nat) (a:A) (l:list A), nList n a l -> nList (S n) a (a::l).

Lemma nList_correct : forall (A:Type) (n:nat) (a:A), { l:list A | nList n a l }.
Proof.
  intros.
  induction n.
  - exists nil. 
    constructor.
  - destruct IHn. 
    exists (a::x). 
    constructor. 
    exact n0.
Qed.

Recursive Extraction nList_correct.

(*Ex 1 b*)

Inductive somaPares: list (nat*nat) -> list nat -> Prop :=
  | somaNil : somaPares nil nil
  | somaNormal : forall (a: (nat*nat)) (b: list (nat*nat)) (l: list nat), somaPares b l -> somaPares (a::b) (((fst a)+(snd a))::l).

Theorem pairSum_correct : forall (b: list(nat*nat)), {l: list nat | somaPares b l}.
Proof.
  intros.
  induction b.
  - exists nil. 
    constructor.
  - destruct IHb.
    + intros. 
      exists ( ((fst a) + (snd a))::x ). 
      constructor. 
      exact s.
Qed.

Recursive Extraction pairSum_correct.

Open Scope Z_scope. 

(*Ex 2 a*)

Fixpoint count (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') => if (Z.eq_dec z z')
                  then S (count z l')
                  else count z l'
  end.

Lemma count_corr : forall (x:Z) (a:Z) (l:list Z), x <> a ->  count x (a :: l) = count x l.
Proof.
  intros.
  simpl.
  destruct (Z.eq_dec x a).
  - intros. 
    contradiction.
  - intros. 
    trivial.
Qed.

(*Ex 2 b*)

Inductive countRel : Z -> list Z -> nat -> Prop :=
  | cNil : forall z:Z, countRel z nil 0
  | cIf : forall (z:Z) (l: list Z) (n: nat), countRel z l n -> countRel z (z::l) (S n)
  | cElse : forall (z z':Z) (l: list Z) (n: nat), z <> z' -> countRel z l n -> countRel z (z'::l) n.

(*Ex 2 c*)

Lemma count_correct : forall (z:Z) (l:list Z), countRel z l (count z l).
Proof.
  intros.
  induction l.
  - simpl. 
    constructor.
  - simpl. 
    destruct (Z.eq_dec z a).
    + intros. 
      rewrite <- e. 
      constructor. 
      exact IHl.
    + intros. 
      destruct IHl. 
      * constructor.
        -- assumption.
        -- constructor.
      * constructor.
        -- assumption.
        -- constructor. 
           assumption.
      * constructor.
        -- exact n.
        -- constructor.
          ++ exact H.
          ++ exact IHl.
Qed.

Close Scope Z_scope.