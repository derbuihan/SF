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




  

