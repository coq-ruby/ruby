Require Export basic.

Definition loop {X Y S} 
  (R: rel (X*S) (S*Y)):
  rel X Y :=
  fun i j => exists s, R (i,s) (s, j).

Check loop.

Lemma loopinout1:
  forall A B C D E
  (P: rel A B) (Q: rel (B*E) (E*C)) (R:rel C D),
  P; loop Q; R = loop(FST P; Q; SND R).
Proof.
intros.
unfold loop.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply propositional_extensionality. split.

- intro.
  destruct H as [c H0].
  destruct H0 as [b H1].
  destruct H0 as [e H2].
  exists e.
  unfold FST. unfold SND. unfold series.
  exists (e, c). exists (b, e).
  unfold parallel; simpl; unfold id; auto. 
  auto.
  unfold parallel; simpl; unfold id; auto. 
  
- unfold FST. unfold SND. unfold series. unfold parallel. intros.
  destruct H as [e H0]. destruct H0 as [k H1]. destruct H1.
  destruct k. destruct x1.
  simpl in H0. simpl in H.
  destruct H0. unfold id in H2.
  destruct H. unfold id in H.
  exists c. exists b. auto.
  exists e. rewrite H2 at 1. rewrite <- H. auto.
  auto.
Qed.

Lemma loopid:
  forall A,
  loop ([(id A), (id A)]) = id A.
Proof.
intros.
unfold loop. unfold id.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
unfold parallel.
simpl.
apply propositional_extensionality. split.
- intro. 
  destruct H as [s H0].
  destruct H0 as [H1 H2]. 
  rewrite H1. auto.
- intro.
  exists x. auto.
Qed.

Lemma loopfstsnd:
  forall A B C
  (R: rel (A*C) (C*B)) (Q:rel C C),
  loop (SND Q; R) = loop (R; FST Q).
Proof.
intros.
unfold SND. unfold FST. 
unfold series. unfold parallel.
unfold loop.

apply functional_extensionality. simpl. intro a.
apply functional_extensionality. intro b.
apply propositional_extensionality. split.
- simpl. unfold id. intros. destruct H as [c0 H0].
  destruct H0 as [k H1 H2]. destruct k.
  destruct H1 as [H3 H4]. simpl in H3. simpl in H4.
  exists c. exists (c0, b). rewrite H3. auto.
  simpl. auto.
- unfold id. intros. destruct H as [c0 H0].
  destruct H0 as [k H1 H2]. destruct k.
  destruct H2 as [H3 H4]. simpl in H3. simpl in H4.
  exists c. exists (a, c0). simpl. auto.
  rewrite <- H4.
  auto.
Qed.