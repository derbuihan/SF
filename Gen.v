Require Export Poly.


Theorem double_injective' : forall n m,
    double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  simpl. intros m eq. destruct m as [| m'].
    reflexivity.
    inversion eq.
  intros m eq. destruct m as [| m'].
    inversion eq. assert (n' = m') as H. apply IHn'.
    inversion eq. reflexivity. rewrite H. reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
    double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
    simpl.  intros n eq. destruct n as [| n'].
      reflexivity.
      inversion eq.
    simpl. intros n eq. destruct n as [| n'].
      inversion eq.
      assert (n' = m') as H.
        apply IHm'. inversion eq. reflexivity.
      rewrite H. reflexivity.
Qed.


Theorem plus_n_n_injective_take2 : forall n m,
    n + n = m + m -> n = m.
Proof.
  intros n. induction n as [| n'].
    intros m eq. destruct m as [| m'].
      reflexivity.
      inversion eq.
    intros m eq. destruct m as [| m'].
      inversion eq.
      inversion eq. rewrite (plus_comm n' (S n')) in H0. rewrite (plus_comm m' (S m')) in H0. inversion H0. specialize (IHn' m' H1). rewrite IHn'. reflexivity.
Qed.


Theorem index_after_last: forall (n : nat) (X:Type) (l : list X),
    length l = n -> index (S n) l = None.
Proof.
  intros n X.
  induction n as [| n'].
  intros. destruct l as [| l'].
    reflexivity.
    inversion H.
  intros. destruct l as [| l'].
    reflexivity.
    inversion H. simpl. rewrite H1. apply IHn'. trivial.
Qed.

Theorem length_snoc''' : forall (n : nat) (X : Type) (v : X) (l : list X),
     length l = n -> length (snoc l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  induction l as [| v' l'].
    intros. simpl. inversion H. reflexivity.
    intros. simpl. destruct n as [| n'].
      inversion H.
      assert (length (snoc l' v) = S n').
        apply IHl'. simpl in H. inversion H. trivial.
      rewrite H0. trivial.
Qed.


Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
    length (l1 ++ (x :: l2)) = n -> S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x.
  induction l1 as [|v1' l1'].
    simpl. intros. trivial.
    destruct n as [| n'].
      simpl. intros. inversion H.
      simpl. intros. inversion H. rewrite H1. rewrite (IHl1' n' H1). trivial.
Qed.


Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n -> length (l ++ l) = n + n.
Proof.
  intros X n l. generalize dependent n.
  induction l as [| v' l'].
    simpl. intros. rewrite <- H. reflexivity.
    simpl.
    intros n. destruct n as [| n'].
      intros. inversion H.
      simpl. intros.
      rewrite <- plus_n_Sm.
      assert (forall (X:Type) (xs ys:list X) (y:X),  length (xs ++ y :: ys) = S (length xs + length ys)). 
        intros. induction xs as [| x' xs']. reflexivity. simpl. rewrite <- IHxs'. reflexivity.
      rewrite (H0 X l' l' v'). inversion H. rewrite H2. trivial.
Qed.

