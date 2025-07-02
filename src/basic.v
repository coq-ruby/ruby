Require Export rel.

Definition series {A B C} 
  (R: rel A B) (S: rel B C):
  rel A C :=
  fun i j => exists2 k, R i k & S k j.

Notation " Q ; R " := (series Q R)
  (at level 40, left associativity).

Definition converse {A B}
  (R: rel A B):
  rel B A :=
  fun i j => R j i.

Notation " R ^~1 " := (converse R)
  (at level 39, left associativity).

Check _^~1.

Definition id 
  (A:Type): 
  rel A A :=
  fun i j => i=j.

Lemma id_left:
  forall A B (R:rel A B),
  id A; R = R.
Proof.
  intros.
  unfold series. unfold id.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply propositional_extensionality.
  split.
  - intros [c ? ?]. rewrite H. auto.
  - eauto.
Qed.

Lemma id_right:
  forall A B (R: rel A B),
  R; id B = R.
Proof.
  intros.
  unfold series. unfold id.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  apply propositional_extensionality.
  split. -
  intros [c ? ?]. rewrite <- H0. eauto.
  - eauto.
Qed.

Lemma id_conv:
  forall A,
  id A ^~1 = id A.
Proof.
  intros.
  unfold id. unfold converse.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  apply propositional_extensionality. split.
  - auto.
  - auto.
Qed.

Fixpoint pow {A} 
  (n:nat) (R: rel A A):
  rel A A :=
  match n with
    0 => id A
  | S p => pow p R ; R
  end.

Notation " R ^^ n " := (pow n R)
  (at level 39, left associativity).

Lemma series_assoc:
  forall A B C D (R:rel A B) (S:rel B C) (T:rel C D),
  R;(S;T) = (R;S);T.
Proof.
  intros.
  unfold series.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  apply propositional_extensionality. split.
  - intros [c ? [d ? ?]]. eauto.
  - intros [c [d ? ?] ?]. eauto.
Qed.

Lemma pow_left:
  forall A (n:nat) (R: rel A A),
  R; R^^n = R ^^ (S n).
Proof.
  intros.
  induction n.
  simpl. 
  rewrite id_left. rewrite id_right. auto.
  simpl. rewrite series_assoc.
  rewrite IHn.
  auto.
Qed.

Lemma pow_right:
  forall A (n:nat) (R: rel A A),
  R^^n; R = R^^(S n).
Proof. auto. Qed.

Lemma conv_conv:
  forall A B (R: rel A B),
  (R^~1)^~1 = R.
Proof.
  intros.
  unfold converse.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  apply propositional_extensionality. split.
  auto. auto.
Qed.

Lemma series_conv:
  forall A B C (R: rel A B) (S: rel B C),
  (R;S)^~1 = S^~1; R^~1.
Proof.
  intros.
  unfold series. unfold converse.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  apply propositional_extensionality. split.
  - intro. destruct H as [k H1 H2].
    exists k. auto. auto.
  - intro. destruct H as [k H1 H2].
    exists k. auto. auto.
Qed.

Lemma pow_conv:
  forall A (n:nat) (R: rel A A),
  (R^^n)^~1 = (R^~1)^^n.
Proof.
  intros.
  induction n.
  - simpl. apply id_conv.
  - simpl. rewrite series_conv.
    rewrite IHn.
    rewrite pow_left. rewrite pow_right. auto.
Qed.

Definition parallel {A B X Y}
  (R: rel A X) (S: rel B Y):
  rel (A*B) (X*Y) :=
  fun i j => R (fst i) (fst j) /\ S (snd i) (snd j).

Notation " [ Q , R ] " := (parallel Q R)
  (at level 38, left associativity).

Definition FST {A B C}
  (R: rel A B):
  rel (A*C) (B*C) :=
  [R, id C].

Definition SND {A B C}
  (R: rel A B):
  rel (C*A) (C*B) :=
  [id C, R].

Lemma para_conv:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S]^~1 = [R^~1, S^~1].
Proof.
  intros.
  unfold parallel. unfold converse.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  destruct x. destruct x0.
  apply propositional_extensionality. split.
  - intro. simpl in H. destruct H.
    simpl. auto.
  - intro. simpl in H. destruct H.
    simpl. auto.
Qed.

Lemma para_series:
  forall A B C D E F
  (R: rel A B) (S: rel D E) (T: rel B C) (U: rel E F),
  [R;T,S;U] = [R,S]; [T,U].
Proof.
  intros.
  unfold parallel. unfold series.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  apply propositional_extensionality. split.
  - intro. destruct H as [H1 H2].
    destruct H1 as [b H11 H12].
    destruct H2 as [e H21 H22].
    exists (b, e). simpl. auto.
    simpl. auto.
  - intro.
    destruct H as [be H1 H2].
    destruct H1 as [H11 H12].
    destruct H2 as [H21 H22].
    destruct be.
    split.
    + exists b. auto. auto.
    + exists e. auto. auto.
Qed.

Lemma fst_conv:
  forall A B C (R:rel A B),
  (FST (C:=C) R)^~1 = FST (R^~1).
Proof.
  intros.
  unfold FST. unfold converse. unfold parallel.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  apply propositional_extensionality. split.
  - intro. destruct H. split.
    + auto.
    + unfold id. auto.
  - intro. destruct H. split.
    + auto.
    + unfold id. auto.
Qed.

Lemma fst_series:
  forall A B C D (R: rel A B) (S: rel B C),
  (FST (C:=D) R); (FST S) = FST (R;S).
Proof.
  intros.
  unfold FST. unfold converse. unfold series. unfold parallel.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  apply propositional_extensionality. split.
  - intro. destruct H as [bd H1 H2]. destruct bd. 
    simpl in H1. simpl in H2.
    destruct H1 as [H11 H12]. destruct H2 as [H21 H22]. split.
    + exists b. auto. auto.
    + unfold id in H12. unfold id in H22. unfold id. rewrite H12. auto.
  - intro. destruct H. destruct H as [b H1 H2]. 
    destruct x. destruct x0.
    simpl in H0. simpl in H1. simpl in H2.
    exists (b, d). split.
    + auto.
    + simpl. unfold id. auto.
    + split.
      * simpl. auto.
      * simpl. unfold id. auto.
Qed.

Lemma snd_series:
  forall A B C D (R:rel A B) (S:rel B C),
  (SND (C:=D) R); SND S =  SND (R; S).
Proof.
  intros.
  unfold SND.
  rewrite <- para_series.
  rewrite id_right.
  auto.
Qed.

Lemma para_as_series:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S] = FST R; SND S.
Proof.
  intros.
  unfold FST. unfold SND.
  rewrite <- para_series.
  rewrite id_left. rewrite id_right. auto.
Qed.

Lemma para_as_series2:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S] = SND S; FST R.
Proof.
  intros.
  unfold FST. unfold SND.
  rewrite <- para_series.
  rewrite id_left. rewrite id_right. auto.
Qed.

Lemma para_snd:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel D E),
  [R, S]; SND T = [R, S; T].
Proof.
  intros.
  unfold SND.
  rewrite <- para_series.
  rewrite id_right. auto.
Qed.

Lemma para_fst:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel B E),
  [R, S]; FST T = [R; T, S].
Proof.
  intros.
  unfold FST.
  rewrite <- para_series.
  rewrite id_right. auto.
Qed.

Lemma snd_para:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel E C),
  SND T; [R, S] = [R, T; S].
Proof.
  intros.
  unfold SND.
  rewrite <- para_series.
  rewrite id_left. auto.
Qed.

Lemma fst_para:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel E A),
  FST T; [R, S] = [T; R, S].
Proof.
  intros.
  unfold FST.
  rewrite <- para_series.
  rewrite id_left. auto.
Qed.
