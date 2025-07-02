Require Export rec.

Lemma comcomp:
  forall A (n:nat) (Q: rel A A) (R: rel A A),
  Q;R=R;Q -> Q;(R^^n) = (R^^n);Q.
Proof.
  intros.
  induction n.
  simpl.
  rewrite id_right. rewrite id_left. auto.
  simpl.
  rewrite series_assoc.
  rewrite IHn.
  rewrite <- series_assoc.
  rewrite H.
  rewrite <- series_assoc.
  reflexivity.
Qed.

Lemma powdist:
  forall A (n:nat) (Q: rel A A) (R: rel A A),
  Q;R=R;Q -> Q^^n;R^^n = (Q;R)^^n.
Proof.
  intros.
  induction n. simpl.
  rewrite id_left. auto.
  simpl. rewrite series_assoc.
  rewrite <- (series_assoc _ _ _ _ _ (Q)).
  rewrite comcomp; auto.
  rewrite series_assoc.
  rewrite IHn.
  rewrite series_assoc at 1.
  auto.
Qed.

Lemma para_id:
  forall A B,
  [id A, id B] = id (A*B).
Proof.
intros.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply propositional_extensionality. split.
- unfold id. unfold parallel.
  destruct x. destruct x0. simpl. intro.
  destruct H. rewrite H. rewrite H0. auto.
- unfold id. unfold parallel.
  destruct x. destruct x0. intro.
  injection H. simpl. auto.
Qed.

Lemma para_id_left:
  forall A B (R:rel (A*B) B),
  ([id A, id B]; R) = R.
Proof.
intros.
rewrite para_id.
rewrite id_left.
auto.
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

Lemma preHorners:
  forall A B (n:nat) (P: rel A A) (Q:rel B B) (R:rel (A*B) B),
  [P, Q]; R = R; Q ->
  [ P ^^ n, Q ^^ n]; R = R; (Q ^^ n).
Proof.
  intros.
  induction n.
  simpl. rewrite para_id_left. 
  rewrite id_right. auto.
  repeat rewrite <- pow_right.
  rewrite para_series.
  rewrite <- series_assoc. rewrite H.
  rewrite series_assoc. rewrite IHn. 
  rewrite series_assoc. auto.
Qed.

Lemma empty_is_nil' : forall A n (v: t A n),
match n return t A n -> Prop with
| O => fun v => v = nil A
| _ => fun _ => True
end v.
Proof.
destruct v; auto.
Qed.

Lemma empty_is_nil:
  forall A {a: t A 0},
  a = nil A.
Proof. 
intros; apply (empty_is_nil' _ _ a).
Qed.

Lemma mapn_rdr_id_zero:
  forall A B,
  [mapn_zero(A:=A) (B:=A), id B]; rdr_zero = rdr_zero.
Proof.
intros. unfold mapn_zero. unfold id. unfold rdr_zero.
unfold parallel. unfold series.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply propositional_extensionality. split.
+ intro. destruct H. destruct H. destruct H.
 rewrite H1. auto.
+ intro. exists (nil A, x0). split. split.
  destruct x. simpl in H.
  simpl. apply empty_is_nil.
  simpl. auto.
  simpl. auto.
  simpl. auto. 
Qed.

Lemma Horners:
  forall A B (n:nat) (P:rel A A) (Q:rel B B) (R:rel (A*B) B),
  [P,Q]; R = R; Q ->
  [tri n P, pow n Q]; (rdr n R) = rdr n (SND Q; R).
Proof.
  intros.
  induction n. simpl.
  apply mapn_rdr_id_zero.
  simpl.

  repeat rewrite (series_assoc _).
  rewrite para_fst.

  repeat rewrite <- series_assoc.
  rewrite apr_apr1. rewrite id_right.
  rewrite <- fst_para.
  repeat rewrite series_assoc.
  (*
  replace (FST (apr n ^~1); [[tri n P, P ^^ n], Q ^^ n; Q]; lsh)
  with (FST (apr n ^~1); ([[tri n P, P ^^ n], Q ^^ n; Q]; lsh))
  by now rewrite <- series_assoc.
  *)
  rewrite <- (series_assoc _ _ _ _ _([[tri n P, P ^^ n], Q ^^ n; Q])).
  rewrite para_lsh.

  repeat rewrite series_assoc.
  rewrite <- (series_assoc _ _ _ _ _([tri n P, [P ^^ n, Q ^^ n; Q]])).
  rewrite para_snd.

  rewrite pow_right. rewrite <- pow_left.
  rewrite <- (snd_para _ _ _ _ _ (P ^^ n)).

  repeat rewrite <- series_assoc.
  rewrite preHorners.

  repeat rewrite series_assoc. rewrite <- snd_para.

  repeat rewrite <- series_assoc.
  rewrite IHn.
  auto. auto.
Qed.


