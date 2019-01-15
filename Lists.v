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
    reflexivity.
  Qed.

  Theorem surjective_pairing : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    intros p.
    destruct p as (n,m).
    simpl.
    reflexivity.
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
    reflexivity.
  Qed.
  
  Example test_app2: nil ++ [4,5] = [4,5].
  Proof.
    reflexivity.
  Qed.
  
  Example test_app3: [1,2,3] ++ nil = [1,2,3].
  Proof.
    reflexivity.
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
    reflexivity.
  Qed.
  
  Example test_head2: head 0 [] = 0.
  Proof.
    reflexivity.
  Qed.
  
  Example test_tail: tail [1,2,3] = [2,3].
  Proof.
    reflexivity.
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
    reflexivity.
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
    reflexivity.
  Qed.
  
  Fixpoint countoddmembers (l : natlist): nat := length (oddmembers l).

  Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
  Proof.
    reflexivity.
  Qed.
    
  Example test_countoddmembers2: countoddmembers [0,2,4] = 0.
  Proof.
    reflexivity.
  Qed.
    
  Example test_countoddmembers3: countoddmembers nil = 0.
  Proof.
    reflexivity.
  Qed.


  





  

  

  
  

