Section TPC1.

Variables A B C D:Prop.
Lemma tpc1a : (A -> C) /\ (B -> C) -> (A /\ B) -> C.
Proof.
  intros.
  apply H.
  apply H0.
Qed.

Print tpc1a.

Lemma tpc1b : ~A \/ ~B -> ~(A /\ B).
Proof.
  intros.
  intro.
  destruct H as [H1 | H2].
  - apply H1.
    destruct H0 as [H3 H4].
    assumption.
  - apply H2.
    destruct H0 as [H3 H4].
    assumption.
Qed.

Print tpc1b.

Lemma tpc1c : (A -> (B \/ C)) /\ (B -> D) /\ (C -> D) -> (A -> D).
Proof.
  intros.
  destruct H as [H1 H2].
  - destruct H1 as [H3 | H4].
    + assumption.
    + destruct H2 as [H5 H6].
      * apply H5.
        assumption.
    + destruct H2 as [H5 H6].
      * apply H6.
        assumption.
Qed.

Print tpc1c.

Lemma tpc1d : (A /\ B) -> ~(~A \/ ~B).
Proof.
  intros.
  intro.
  destruct H0 as [H1 | H2].
  - destruct H as [H3 H4].
    apply H1.
    assumption.
  - destruct H as [H3 H4].
    apply H2.
    assumption.
Qed.

Print tpc1d.
End TPC1.

Section TPC2.

Variable X : Set.
Variables R P Q : X -> Prop.

Lemma tpc2a : (forall x,P x -> Q x) -> (forall y, ~(Q y)) -> (forall x, ~(P x)).
Proof.
  intros.
  intro.
  destruct (H0 x).
  apply H.
  apply H1.
Qed.

Lemma tpc2b : (forall x,P x \/ Q x) -> (exists y,(~Q y)) -> (forall x,R x -> ~(P x)) -> (exists x,~(R x)).
Proof.
  intros.
  destruct H0 as [y0 H2].
  exists y0.
  intro.
  apply H2.
  destruct (H y0) as [H3 | H4].
  - destruct (H1 y0).
    + assumption.
    + assumption.
  - assumption.
Qed.

End TPC2.

Section TPC3.
Axiom exclusive_middle : forall A: Prop, A \/ ~A.
Variables A B: Prop.
Variable X : Set.
Variables P : X -> Prop.

Lemma tpc3a : (~A -> B) -> (~B -> A).
Proof.
  intros.
  destruct exclusive_middle with A as [H1 | H2].
  - assumption.
  - destruct H0.
    apply H.
    apply H2.
Qed.

Lemma tpc3b : ~(exists x,~P x) -> (forall x: X,P x).  
Proof.
  intros.
  destruct exclusive_middle with (P x).
  - assumption.
  - destruct H.
    exists x.
    assumption.
Qed.


Lemma tpc3c : ~(forall x: X, ~(P x)) -> (exists x, P x).
Proof.
  intros.
  destruct exclusive_middle with (exists x, P x).
  - exact H0.
  - destruct H.
    intro x0.
    destruct exclusive_middle with (~P x0).
    + assumption.
    + unfold not.
      intro.
      destruct H0.
      exists x0.
      assumption.
Qed.
End TPC3. 