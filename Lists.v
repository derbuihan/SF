From mathcomp
     Require Import ssreflect.
Require Import Basics.

Module NatList.

  Inductive natprod : Type :=
    pair : nat -> nat -> natprod.

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Notation "( x , y )" := (pair x y).

  Eval simpl in (fst (3, 4)).

  Definition fst' (p : natprod) : nat :=
    match p with
    | (x ,y) => x
    end.

  Definition snd' (p : natprod) : nat :=
    match p with
    | (x ,y) => y
    end.
  
  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x, y) => (y, x)
    end.

  Theorem surjecive_pairing': forall (n m: nat),
      (n, m) = (fst (n, m), snd (n, m)).
  Proof.
    move => //.
  Qed.

  Theorem surjective_pairing : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    move => p.
    case p => //.
  Qed.
    
  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

  Eval simpl in ([1,3,3,4,4,2]).

  Definition l_123' := 1 :: (2 :: (3 :: nil)).
  Definition l_123'' := 1 :: 2 :: 3 :: nil.
  Definition l_123''' := [1,2,3].

  Fixpoint repeat (n count : nat): natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l : natlist): nat :=
    match l with
    | nil => O
    | x :: xs  => S (length xs)
    end.

  Eval simpl in (length [1, 2, 3, 4]).

  Fixpoint app (l1 l2 : natlist): natlist :=
    match l1 with
    | nil => l2
    | x :: xs => x :: (app xs l2)
    end.

  Eval simpl in (app [1,2] [3,4,5]).

  Notation "x ++ y" := (app x y) (right associativity, at level 60).

  Eval simpl in ([1,2] ++ [3,4,5]).
  
  Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
  Proof.
    move => //.
  Qed.
  
  Example test_app2: nil ++ [4,5] = [4,5].
  Proof.
    move => //.
  Qed.
  
  Example test_app3: [1,2,3] ++ nil = [1,2,3].
  Proof.
    move => //.
  Qed.

  Definition head (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | x :: xs => x
    end.

  Eval simpl in (head 0 [1,2]).

  Definition tail (l : natlist) : natlist :=
    match l with
    | nil => nil
    | x :: xs => xs
    end.

  Example test_head1: head 0 [1,2,3] = 1.
  Proof.
    move => //.
  Qed.
  
  Example test_head2: head 0 [] = 0.
  Proof.
    move => //.
  Qed.
  
  Example test_tail: tail [1,2,3] = [2,3].
  Proof.
    move => //.
  Qed.


  Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | nil => nil
    | x :: xs => match x with
                | O => nonzeros xs
                | S n => x :: nonzeros xs
                end
    end.

  Example test_nonzeros: nonzeros [0,1,0,2,3,0, 0] = [1, 2, 3].
  Proof.
    move => //.
  Qed.

  Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | nil => nil
    | x :: xs => match (oddb x) with
               | true  => x :: oddmembers xs
               | false => oddmembers xs
               end
    end.

  Eval simpl in (oddmembers [1,2,3]).

  Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
  Proof.
    move => //.
  Qed.
  
  Fixpoint countoddmembers (l : natlist): nat := length (oddmembers l).

  Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
  Proof.
    move => //.
  Qed.
    
  Example test_countoddmembers2: countoddmembers [0,2,4] = 0.
  Proof.
    move => //.
  Qed.
    
  Example test_countoddmembers3: countoddmembers nil = 0.
  Proof.
    move => //.
  Qed.

  Fixpoint alternate (l1 l2 : natlist): natlist :=
    match l1 with
    | nil => l2
    | x :: xs => x :: match l2 with
                | nil => xs
                | y :: ys => y :: alternate xs ys
                end
    end.

  Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
  Proof.
    move => //.
  Qed.
  
  Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
  Proof.
    move => //.
  Qed.
  
  Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
  Proof.
    move => //.
  Qed.

  Example test_alternate4: alternate [] [20,30] = [20,30].
  Proof.
    move => //.
  Qed.

  Definition bag := natlist.

  Fixpoint count (v : nat) (s : bag): nat :=
    match s with
    | nil => 0
    | x :: xs => match (beq_nat v x) with
                | true => 1 + count v xs
                | false => count v xs
                end
    end.

  Example test_count1: count 1 [1,2,3,1,4,1] = 3.
  Proof.
    move => //.
  Qed.

  Example test_count2: count 6 [1,2,3,1,4,1] = 0.
  Proof.
    move => //.
  Qed.

  Definition sum : bag -> bag -> bag := app.

  Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
  Proof.
    move => //.
  Qed.

  Definition add (v:nat) (s:bag) : bag := v :: s.

  Example test_add1: count 1 (add 1 [1,4,1]) = 3.
  Proof.
    move => //.
  Qed.

  Example test_add2: count 5 (add 1 [1,4,1]) = 0.
  Proof.
    move => //.
  Qed.


  Definition member (v:nat) (s:bag) : bool :=
    match (count v s) with
    | 0 => false
    | S _ => true
    end.

  Example test_member1: member 1 [1,4,1] = true.
  Proof.
    move => //.
  Qed.

  Example test_member2: member 2 [1,4,1] = false.
  Proof.
    move => //.
  Qed.

  Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | x :: xs => match (beq_nat x v) with
                | true => xs
                | false => x :: (remove_one v xs)
                end
    end.

  Eval simpl in (remove_one 5 [1,5,3,5]).

  Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
  Proof.
    move => //.
  Qed.

  Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
  Proof.
    move => //.
  Qed.

  Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
  Proof.
    move => //.
  Qed.

  Example test_remove_one4:
    count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
  Proof.
    move => //.
  Qed.

  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | x :: xs => match (beq_nat x v) with
               | true => remove_all v xs
               | false => x :: remove_all v xs
               end
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
  Proof.
    move => //.
  Qed.

  Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
  Proof.
    move => //.
  Qed.

  Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
  Proof.
    move => //.
  Qed.

  Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
  Proof.
    move => //.
  Qed.

  Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
    match s2 with
    | nil => beq_nat 0 (length s1)
    | y :: ys => subset (remove_one y s1) ys
    end.

  Example test_subset1: subset [1,2] [2,1,4,1] = true.
  Proof.
    move => //.
  Qed.

  Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
  Proof.
    move => //.
  Qed.

  (* bag_theorem *)
  
  Definition eq_bag (s1 : bag) (s2 : bag) :=
    andb (subset s1 s2) (subset s2 s1).

  Fixpoint filter (f : nat -> bool) (s : bag) : bag :=
    match s with
    | nil => nil
    | x :: xs => match (f x) with
                | true => x :: filter f xs
                | false => filter f xs
                end
    end.  

  Theorem nil_app : forall l : natlist,
      [] ++ l = l.
  Proof.
    move => //.
  Qed.

  Theorem tl_length_pred : forall l : natlist,
      pred (length l) = length (tail l).
  Proof.
    move => l.
    case l => [//| n l' //].
  Qed.

  Theorem app_ass : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    move => l1 l2 l3.
    elim l1 => [//| n l' IHl' /=].
    rewrite <- IHl' => //.
  Qed.

  Theorem app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    move => l1 l2.
    elim l1 => [//| n l' IHl' /=].
    rewrite IHl' => //.
  Qed.

  Fixpoint snoc (l : natlist) (v : nat) : natlist :=
    match l with
    | nil => [v]
    | x :: xs => x :: (snoc xs v)
    end.

  Fixpoint rev (l : natlist) : natlist :=
    match l with
    | nil => nil
    | x :: xs => snoc (rev xs) x
    end.

  Example test_rev1 : rev [1, 2, 3] = [3, 2, 1].
  Proof.
    move => //.
  Qed.

  Example test_rev2 : rev nil = nil.
  Proof.
    move => //.
  Qed.

  Theorem length_snoc : forall n : nat, forall l : natlist,
        length (snoc l n) = S (length l).
  Proof.
    move => n l.
    elim l => [//| n' l' IHl' /=].
    rewrite IHl' => //.
  Qed.
    
  Theorem rev_length : forall l : natlist,
      length (rev l) = length l.
  Proof.
    move => l.
    elim l => [//| n l' IHl' /=].
    rewrite length_snoc IHl' => //.
  Qed.

  Theorem app_nil_end : forall l : natlist,
      l ++ [] = l.
  Proof.
    move => l.
    elim l => [//| n l' IHl' /=].
    rewrite IHl' => //.
  Qed.
  
  Theorem rev_app : forall n : nat, forall l : natlist,
        rev (snoc l n) = n :: (rev l).
  Proof.
    move => n l.
    elim l => [//| n' l' IHl' /=].
    rewrite IHl' => //.
  Qed.

  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    move => l.
    elim l => [//| n l' IHl' /=].
    rewrite rev_app IHl' => //.
  Qed.

  Theorem snoc_app : forall l1 l2 : natlist, forall n : nat,
        snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
  Proof.
    move => l1 l2 n.
    elim l1 => [//|n' l' IHl' /=].
    rewrite IHl' => //.
  Qed.

  Theorem distr_rev : forall l1 l2 : natlist,
      rev (l1 ++ l2) = (rev l2) ++ (rev l1).
  Proof.
    move => l1 l2.
    elim l1 => [/=|n' l' IHl' /=].
      rewrite app_nil_end => //.
      rewrite IHl' snoc_app => //.
  Qed.

  Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    move => l1 l2 l3 l4.
    rewrite 2!app_ass => //.
  Qed.

  Theorem snoc_append : forall (l : natlist) (n : nat),
      snoc l n = l ++ [n].
  Proof.
    move => l n.
    elim l => [//| n' l' IHl' /=].
    rewrite IHl' => //.
  Qed.


  (* list_design *)


  Theorem count_member_nonzero : forall (s : bag),
      ble_nat 1 (count 1 (1 :: s)) = true.
  Proof.
    move => s.
    elim s => [//| n s' IHs' //].
  Qed.

  Theorem ble_n_Sn : forall n,
      ble_nat n (S n) = true.
  Proof.
    move => n.
    elim n => [//|n' IHn' //].
  Qed.

  Theorem remove_decreases_count: forall (s : bag),
      ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    move => s.
    elim s => [//| n s' IHs' //].
    elim n => [/=| n' IHn' //=].
    rewrite ble_n_Sn => //.
  Qed.

  Theorem rev_injective : forall l1 l2 : natlist,
      rev l1 = rev l2 -> l1 = l2.
  Proof.
    move => l1 l2 H.
    rewrite <- rev_involutive.
    rewrite <- H.
    rewrite rev_involutive => //.
  Qed.

  


    