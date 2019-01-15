
Inductive day: Type :=
  | monday: day
  | tuesday: day
  | wednesday: day
  | thursday: day
  | friday: day
  | saturday: day
  | sunday: day.

Definition next_weekday (d: day): day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday friday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.

Inductive bool: Type :=
  | true: bool
  | false: bool.

Definition negb (b: bool): bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1: bool) (b2: bool): bool :=
  match b1 with
  | true => b2
  | false => false
  end.


Definition orb (b1: bool) (b2: bool): bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb2: (orb false false) = false.
Proof.
  simpl.
  reflexivity.
Qed.


Example test_orb3: (orb false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb4: (orb true true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Definition admit {T: Type} : T. Admitted.

Definition nandb (b1: bool) (b2: bool) :bool :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
 andb (andb b1 b2) b3.

Example test_andb31: (andb3 true true true) = true.
Proof.
  reflexivity.
Qed.

Example test_andb32: (andb3 false true true) = false.
Proof.
  reflexivity.
Qed.

Example test_andb33: (andb3 true false true) = false.
Proof.

  reflexivity.
Qed.

Example test_andb34: (andb3 true true false) = false.
Proof.
  reflexivity.
Qed.

Check (negb).

Module Playground1.

  Inductive nat: Type :=
  | O: nat
  | S: nat -> nat.

  Definition pred (n: nat): nat :=
    match n with
    | O => O
    | S n' => n'
    end.
  
End Playground1.

Definition minustwo (n: nat): nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S O))).
Eval simpl in (minustwo 4).

Check S.
Check prod.
Check minustwo.

Fixpoint evenb (n: nat): bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Example test_evenb: (evenb 100) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Fixpoint oddb (n: nat) : bool :=
  match n with
  | O => false
  | S O => true
  | S (S n') => oddb n'
  end.

Example test_oddb1: (oddb (S O)) = true.
Proof.
  reflexivity.
Qed.

Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof.
  simpl. reflexivity.
Qed.

Module Playground2.

  Fixpoint plus (n: nat) (m: nat): nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Eval simpl in (plus 5 4).

  Fixpoint mult (n m: nat): nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Eval simpl in (mult 3 4).

  Fixpoint minus (n m: nat): nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

  Eval simpl in (minus 11 5).

End Playground2.

Fixpoint exp (n m: nat): nat :=
  match m with
  | O => 1
  | S m' => mult n (exp n m')
  end.

Eval simpl in (exp 3 4).

Fixpoint factorial (n: nat): nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Eval simpl in (factorial 3).

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).


Fixpoint beq_nat (n m: nat): bool :=
  match n with
  | O => match m with
         | O => true
         | S _ => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.


Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.



Definition blt_nat (n m : nat) : bool := andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n: forall n: nat, 0 + n = n.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem plus_0_n': forall n: nat, 0 + n = n.
Proof.
  reflexivity.
Qed.

Theorem plus_0_n'': forall n: nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_1_l: forall n: nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_l: forall n: nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_id_example: forall n m: nat,
    n = m -> n + n = m + m.
Proof.
  intros n m H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + (n * m).
Proof.
  intros.
  rewrite -> plus_1_l.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [ | n']. (* as以下は必要ではない *)
  reflexivity.
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n: nat, beq_nat 0 (n+1) =false.
Proof.
  intros.
  destruct n.
  reflexivity.
  reflexivity.
Qed.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    rewrite <- H.
    reflexivity.
  Case "b = fasle".
    destruct c.
    SCase "c = true".
      reflexivity.
    SCase "c = false".
      rewrite <- H. reflexivity.
Qed.      

Theorem plus_0_r : forall n: nat,
  n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = Sn'". simpl. rewrite -> IHn'. reflexivity.  
Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. trivial.
Qed.


Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. trivial.
Qed.  

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite <- IHn'. reflexivity.
Qed.
  
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = 0".
    induction m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl. rewrite <- IHm'. reflexivity.
  Case "n = S n'".
    induction m as [| m'].
    SCase "m = 0". simpl. rewrite -> IHn'. reflexivity.
    SCase "m = S m'". simpl. rewrite -> IHn'. simpl. rewrite plus_n_Sm. reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma plus_assoc : forall n m p: nat,
    (n + m) + p = n + (m + p).
Proof.
  intros n m p.
  induction n as [| n'].
    reflexivity.
    simpl. rewrite IHn'. reflexivity.
Qed.    

Theorem beq_nat_refl: forall n : nat,
    true = beq_nat n n.
Proof.
  intros n.
  induction n as [| n'].
    reflexivity.
    simpl. trivial.
Qed.    

Theorem mult_0_plus': forall n m: nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite H. reflexivity.
Qed.


Theorem plus_rearrange: forall n m p q: nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite plus_comm. reflexivity.
  rewrite H. reflexivity.
Qed.

Theorem plus_swap: forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H0: n + (m + p) = (n + m) + p).
    rewrite <- plus_assoc. reflexivity.
  assert (H1: m + (n + p) = (m + n) + p).
    rewrite <- plus_assoc. reflexivity.
  rewrite H0. rewrite H1.
  assert (H2: n + m = m + n).
    rewrite plus_comm. reflexivity.
  rewrite H2. reflexivity.
Qed.

Theorem  mult_plus_distr_l: forall n m l: nat,
    m * l + m * n = m * (n + l).
Proof.
  intros n m l.
  induction m as [| m'].
    Case "m = 0". reflexivity.
    Case "m = S m'".
      simpl.
      rewrite <- IHm'.
      rewrite <- plus_swap.
      rewrite <- plus_assoc.
      rewrite <- plus_assoc.
      rewrite <- plus_assoc.
      reflexivity.
Qed.

Theorem mult_1_r: forall n: nat,
    n * 1 = n.
Proof.
  intros n.
  induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.
  
Theorem mult_comm: forall m n: nat,
    m * n = n * m.
Proof.  
  induction n as [| n'].
    Case "n = 0". rewrite -> mult_0_r. reflexivity.
    Case "n = S n'".
      assert (H0: S n' = 1 + n'). reflexivity.
      simpl.
      rewrite H0.
      rewrite <- mult_plus_distr_l.
      rewrite plus_comm. 
      rewrite -> mult_1_r.
      rewrite IHn'.
      reflexivity.
Qed.

Theorem ble_nat_refl : forall n: nat,
  true = ble_nat n n.
Proof.
  intros n.
  induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'". simpl. trivial.
Qed.


Theorem zero_nbeq_S : forall n: nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
    Case "b = true". reflexivity.
    Case "b = false". reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p H.
  induction p as [| p'].
    Case "p = 0". simpl. trivial.
    Case "p = S p'". simpl. trivial.
Qed.

Theorem S_nbeq_0 : forall n: nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_1_l : forall n: nat, 1 * n = n.
Proof.
  intros n. rewrite <- plus_0_r. reflexivity.
Qed.  

Theorem all3_spec : forall b c : bool,
    orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros b c.
  destruct b. destruct c.
  reflexivity. reflexivity. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'". simpl. rewrite IHn'. rewrite plus_assoc. reflexivity.
Qed.
  
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'". simpl. rewrite mult_plus_distr_r. rewrite IHn'. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite <- plus_assoc. rewrite <- plus_assoc.
  replace (n + m) with (m + n). reflexivity.
  rewrite plus_comm. reflexivity.
Qed.


Inductive bin : Type :=
| o : bin
| s : bin -> bin
| t : bin -> bin.

Fixpoint inc (b : bin) : bin :=
  match b with
  | o => t o
  | s b' => t b'
  | t b' => s (inc b')
  end.

Eval simpl in (inc (inc (inc (inc (inc o))))).

Fixpoint bin_nat (b : bin) : nat :=
  match b with
  | o => 0
  | s b' => bin_nat b' + bin_nat b'
  | t b' => S (bin_nat b' + bin_nat b')
  end.

Eval simpl in (bin_nat (s (t (s (t o))))).

Theorem inc_comm: forall b : bin,
    bin_nat (inc b) = S (bin_nat b).
Proof.
  intros b.
  induction b.
    reflexivity.
    reflexivity.
    simpl. rewrite -> IHb. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.

Fixpoint nat_bin (n : nat) : bin :=
  match n with
  | O => o
  | S n' => inc (nat_bin n')
  end.

Eval simpl in nat_bin 1.
Eval simpl in nat_bin 2.
Eval simpl in nat_bin 3.
Eval simpl in nat_bin 4.
Eval simpl in nat_bin 5.
Eval simpl in nat_bin 6.
Eval simpl in nat_bin 10.


  









  