Require Export wire.

Definition mapn_zero_f {A B} (x:t A 0) : t B 0 := nil B.

Definition mapn_zero_rf {A B}:
  rel (t A 0) (t B 0) :=
  fun i j => j = mapn_zero_f i.
(* i = nil A /\ j = nil B *)

Definition mapn_zero {A B}:
  rel (t A 0) (t B 0) :=
  fun i j => i = nil A /\ j = nil B.

Fixpoint mapn {A B} (n:nat) (R: rel A B): 
  rel (t A n) (t B n) :=
  match n with
    0 => mapn_zero
  | S p => (apr p)^~1 ; [(mapn p R), R] ; apr p
  end.

Fixpoint mapnl {A B} (n:nat) (R: rel A B): 
  rel (t A n) (t B n) :=
  match n with
    0 => mapn_zero
  | S p => (apl p)^~1 ; [R, (mapnl p R)] ; apl p
  end.

(*
Lemma mapn_dual:
  forall A B (n:nat) (R: rel A B),
  mapn n R = mapnl n R.
*)

Lemma mapn_zero_series:
  forall A B C,
  mapn_zero (A:=A) (B:=C) = mapn_zero (A:=A) (B:=B); mapn_zero (A:=B) (B:=C).
Proof. intros.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply propositional_extensionality. split.
+ unfold series. unfold mapn_zero. intro.
  destruct H.
  exists (nil B). auto. auto.
+ unfold series. unfold mapn_zero. intro.
  destruct H. destruct H. destruct H0.
  split. auto. auto.
Qed.


Lemma mapn_series:
  forall A B C (n:nat) (R: rel A B) (S: rel B C),
  mapn n (R; S) = mapn n R; mapn n S.
Proof.
intros.
induction n.
- simpl. apply mapn_zero_series.
- simpl.
  repeat rewrite series_assoc.
  rewrite <- (series_assoc _ _ _ _ _ (apr n)).
  rewrite apr_apr1.
  rewrite id_right.
  rewrite <- (series_assoc _ _ _ _ _ ([mapn n R, R])).
  rewrite <- para_series.
  rewrite IHn.
  auto.
Qed.

Definition rdr_zero {A B}: 
  rel ((t A 0)*B) B :=
  fun i j => snd i = j.

Fixpoint rdr {A B} (n:nat) (R: rel (A*B) B):
  rel (t A n * B) B :=
  match n with
    0 => rdr_zero
  | S p => FST ((apr p)^~1) ; lsh ; SND R ; rdr p R
  end.

Definition rdl_zero {A B}:
  rel (A * t B 0) A :=
  fun i j => fst i = j.

Fixpoint rdl {A B} (n:nat) (Q: rel (A*B) A):
  rel (A * t B n) A :=
  match n with
    0 => (rdl_zero)
  | S p => SND (apl p)^~1 ; rsh ; FST Q; rdl p Q
  end.

Fixpoint tri {A} (n:nat) (R: rel A A):
  rel (t A n) (t A n) :=
  match n with 
    0 => mapn_zero
  | S p => (apr p)^~1; [tri p R, R^^p]; apr p
end.

(*
Ltac regroup block := 
  repeat rewrite series_assoc;
  rewrite <- (series_assoc _ _ _ _ _ block).
*)

Lemma tri_mapn:
  forall A (n:nat) (R: rel A A),
  mapn n R; tri n R = tri n R; mapn n R.
Proof.
  intros.
  induction n.
  - simpl. auto.
  - simpl.
    repeat rewrite series_assoc.
    rewrite <- (series_assoc _ _ _ _ _ (apr n)).
    rewrite apr_apr1.
    rewrite id_right.
    rewrite <- (series_assoc _ _ _ _ _ ([mapn n R, R])).
    rewrite <- para_series.
    rewrite IHn.
    rewrite pow_left. rewrite <- pow_right.
    rewrite <- (series_assoc _ _ _ _ _ (apr n)).
    rewrite apr_apr1.
    rewrite id_right.
    rewrite <- (series_assoc _ _ _ _ _ ([tri n R, R ^^ n])).
    rewrite para_series. auto.
Qed.







