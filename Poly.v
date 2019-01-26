Require Export Lists.

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.


Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.


Check (nil nat).
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil _ => O
  | cons _ x xs => S (length X xs)
  end.

Eval simpl in (length nat (nil nat)).

Example test_length1:
  length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof.
  reflexivity.
Qed.

Example test_length2:
  length bool (cons bool true (nil bool)) = 1.
Proof.
  reflexivity.
Qed.


Fixpoint app (X:Type) (l1 l2:list X) : (list X) :=
  match l1 with
  | nil _ => l2
  | cons _ x xs => cons X x (app X xs l2)
  end.

Eval simpl in
    (app nat (cons nat 1 (cons nat 2 (nil nat))) (cons nat 3 (nil nat))).

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil _ => cons X v (nil X)
  | cons _ x xs => cons X x (snoc X xs v)
  end.

Fixpoint rev (X:Type) (l:list X) : (list X) :=
  match l with
  | nil _ => nil X
  | cons _ x xs => snoc X (rev X xs) x
  end.

Eval simpl in
    (rev nat (cons nat 1 (cons nat 2 (nil nat)))).


Example test_rev1 :
  rev nat (cons nat 1 (cons nat 2 (nil nat))) = (cons nat 2 (cons nat 1 (nil nat))).
Proof.
  reflexivity.
Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof.
  reflexivity.
Qed.

Arguments nil [X].
Arguments cons [X].
Arguments length [X].
Arguments app [X].
Arguments rev [X].
Arguments snoc [X].

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil => O
  | cons x xs => S (length'' xs)
  end.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123 := [1,2,3].

Fixpoint repeat (X:Type) (x:X) (count:nat): list X :=
  match count with
  | O => nil
  | S n => cons x (repeat X x n)
  end.

Example test_repeat1:
  repeat bool true 2 = cons true (cons true nil).
Proof.
  reflexivity.
Qed.


Example test_repeat2:
  repeat bool true 2 = cons true (cons true nil).
Proof.
  reflexivity.
Qed.

Theorem nil_app: forall X : Type, forall l : list X,
      app [] l = l.
Proof.
  reflexivity.
Qed.

Theorem rev_snoc: forall X : Type, forall v : X, forall s : list X,
        rev (snoc s v) = v :: (rev s).
Proof.
  intros.
  induction s.
    reflexivity.
    simpl. rewrite IHs. reflexivity.
Qed.

Theorem snoc_with_append:
  forall X : Type, forall l1 l2 : list X, forall v : X,
        snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros.
  induction l1.
    reflexivity.
    simpl. rewrite IHl1. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair [X] [Y].

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.


Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
    (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
    (x, y) => y
  end.

Fixpoint combine {X Y:Type} (lx:list X) (ly:list Y):list (X * Y) :=
  match (lx, ly) with
        | (nil, _) => nil
        | (_, nil) => nil
        | (x::tx, y::ty) => (x, y) :: (combine tx ty)
  end.

Eval simpl in (combine [1,2] [false, false, true, true]).

Fixpoint split {X Y:Type} (pl:list (X * Y)) : list X * list Y :=
  match pl with
  | nil => (nil, nil)
  | (x, y) :: xs => (x :: fst (split xs), y :: snd (split xs))
  end.


Example test_split:
  split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof.
  reflexivity.
Qed.

Inductive option (X:Type): Type :=
| Some : X -> option X
| None : option X.

Arguments Some [X].
Arguments None [X].

Fixpoint index {X:Type} (n:nat) (l:list X) : option X :=
  match l with
  | nil => None
  | x :: xs => if beq_nat 0 n then
                Some x
              else
                index (pred n) xs
  end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof.
  reflexivity.
Qed.

Example test_index2 : index 1 [[1],[2]] = Some [2].
Proof.
  reflexivity.
Qed.

Example test_index3 : index 2 [true] = None.
Proof.
  reflexivity.
Qed.

Definition head_opt {X:Type} (l:list X) : option X :=
  match l with
  | nil => None
  | x::_ => Some x
  end.

Example test_hd_opt1 : head_opt [1,2] = Some 1.
Proof.
  reflexivity.
Qed.

Example test_hd_opt2 : head_opt [[1],[2]] = Some [1].
Proof.
  reflexivity.
Qed.

Definition doit3times {X:Type} (f:X -> X) (n:X): X :=
  f (f (f (n))).

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type}
           (f : X * Y -> Z) (x:X) (y:Y) :Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
           (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) x y,
    prod_uncurry (prod_curry f) (x, y) = f (x, y).
Proof.
  reflexivity.
Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l: list X): (list X) :=
  match l with
  | nil => nil
  | x :: xs => if (test x) then
                x :: (filter test xs)
              else
                filter test xs
  end.

Example test_filter1 : filter evenb [1, 2, 3, 4] = [2, 4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => ble_nat 7 n) (filter evenb l).

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof.
  reflexivity.
Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof.
  reflexivity.
Qed.

Definition partition {X:Type} (test:X -> bool) (l:list X):list X * list X :=
  (filter test l, filter (fun x => negb(test x)) l).


Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y:Type} (f:X -> Y) (l:list X) : (list Y) :=
  match l with
  | nil => nil
  | x :: xs => (f x) :: map f xs
  end.

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.


Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n,oddb n]) [2,1,2,5]
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity. Qed.


Theorem map_snoc : forall (X Y:Type) (f:X -> Y) l x,
    snoc (map f l) (f x) = map f (snoc l x).
Proof.
  intros.
  induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.
  
Theorem map_rev : forall (X Y:Type) (f:X -> Y) (l:list X),
    map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l.
    reflexivity.
    simpl. rewrite <- IHl. rewrite map_snoc. reflexivity.
Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) : list Y :=
  match l with
  | nil => nil
  | x :: xs => (f x) ++ (flat_map f xs)
  end.

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4] = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Eval simpl in (option_map (fun x => x + 1) (Some 2)).

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | x :: xs => f x (fold f xs b)
  end.

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).


Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true,false,true,true] true = false.
Proof. reflexivity. Qed.

Definition constfun {X : Type} (x:X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
         
Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X:Type} (f:nat -> X) (k:nat) (x:X): nat -> X :=
  fun (k' : nat) => if beq_nat k k' then
                   x
                 else
                   f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof. reflexivity. Qed.

Theorem unfold_example : forall m n,
    3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite H.
  reflexivity.
Qed.

Theorem override_eq: forall {X:Type} x k (f:nat -> X),
    (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H0 H1.
  unfold override.
  rewrite H1.
  trivial.
Qed.

Theorem eq_add_S : forall (n m : nat),
    S n = S m -> n = m.
Proof.
  intros n m eq.
  inversion eq.
  trivial.
Qed.

Theorem silly4 : forall (n m : nat),
    [n] = [m] -> n = m.
Proof.
  intros n m H.
  inversion H.
  trivial.
Qed.

Theorem silly5 : forall (n m o : nat),
    [n, m] = [o, o] -> [n] = [m].
Proof.
  intros  n m o H.
  inversion H.
  trivial.
Qed.

Example sillyex1: forall (X:Type) (x y z:X) (xs ys:list X),
    x :: y :: xs = z :: ys -> y :: xs = x :: ys -> x = y.
Proof.
  intros X x y z xs ys H0 H1.
  inversion H0.
  inversion H1.
  rewrite H2.
  trivial.
Qed.

Theorem silly6 : forall (n : nat),
    S n = 0 -> 2 + 2 = 5.
Proof.
  intros n H.
  inversion H.
Qed.

Theorem silly7: forall (n m : nat),
    false = true -> [n] = [m].
Proof.
  intros n m H.
  inversion H.
Qed.

Lemma eq_remove_S : forall n m,
    n = m -> S n = S m.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

Theorem beq_nat_eq: forall n m,
    true = beq_nat n m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
    intros m.
    destruct m as [| m'].
      reflexivity.
      simpl. intros H. inversion H.
    intros m.
    destruct m as [| m'].
      simpl. intros H. inversion H.
      simpl. intros H. apply eq_remove_S. apply IHn'. apply H.
Qed.

Theorem beq_nat_eq' : forall m n,
  beq_nat n m = true -> n = m.
Proof.
  intros m.
  induction m as [| m'].
    intros n. destruct n as [| n'].
      reflexivity.
      intros H. inversion H.
    intros n. destruct n as [| n'].
      intros H. inversion H.
      intros H. apply eq_remove_S. apply IHm'. apply H.
Qed.

Theorem length_snoc': forall (X:Type) (v:X) (l:list X) (n:nat),
    length l = n -> length (snoc l v) = S n.
Proof.
  intros X v l.
  induction l as [| l'].
    intros n H. simpl. inversion H. reflexivity.
    intros n H. destruct n as [| n'].
      inversion H.
      apply eq_remove_S. apply IHl. inversion H. reflexivity.
Qed.

Theorem beq_nat_0_l: forall n,
    true = beq_nat 0 n -> 0 = n.
Proof.
  intros n H.
  destruct n.
    reflexivity.
    inversion H.
Qed.

Theorem beq_nat_0_r: forall n,
    true = beq_nat n 0 -> 0 = n.
Proof.
  intros n H.
  destruct n.
    reflexivity.
    inversion H.
Qed.

Theorem double_injective : forall n m,
     double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
    intros m. destruct m.
      reflexivity.
      intros H. inversion H.
    intros m. destruct m.
      intros H. inversion H.
      intros H. apply eq_remove_S. apply IHn'. inversion H. reflexivity.
Qed.

Theorem S_inj: forall (n m : nat) (b : bool),
    beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H. trivial.
Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n H0 H1.
  symmetry in H0. apply H0. symmetry in H1. trivial.
Qed.

Theorem plus_n_m_injective : forall n m,
    n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
    intros m. destruct m as [| m'].
      reflexivity.
      simpl. intros H. inversion H.
    intros m. destruct m as [| m'].
      simpl. intros H. inversion H.
      simpl. intros H. inversion H.
        rewrite <- (plus_n_Sm n' n') in H1.
        rewrite <- (plus_n_Sm m' m') in H1.
        inversion H1. apply eq_remove_S. apply IHn'. trivial.
Qed.


Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then
    false
  else
    if beq_nat n 5 then
      false
    else
      false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    trivial.
    destruct (beq_nat n 5).
      trivial.
      trivial.
Qed.


