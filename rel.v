Require Export axioms.

Definition rel (A B: Type) := A -> B -> Prop.

Definition rel_dot {n m p} (x: rel n m) (y: rel m p): 
  rel n p :=
  fun i j => exists2 k, x i k & y k j.

Definition rel_prod {n m p q} (x: rel n m) (y: rel p q): 
  rel (n*p) (m*q) :=
  fun i j => x (fst i) (fst j) /\ y (snd i) (snd j).

Lemma dot_assoc:
  forall m n p q (x: rel m n) (y: rel n p) (z: rel p q),
  rel_dot (rel_dot x y) z = rel_dot x (rel_dot y z).
Proof.
  intros.
  apply functional_extensionality. intros a.
  apply functional_extensionality. intros b.
  apply propositional_extensionality.
  unfold rel_dot; split.
  - intros [c [d ? ?] ?]. eauto.
  - intros [c ? [d ? ?]]. eauto.
Qed.