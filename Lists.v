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
    intros.
    induction p as (n, m).
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
    reflexivity.
  Qed.
  
  Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
  Proof.
    reflexivity.
  Qed.
  
  Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate4: alternate [] [20,30] = [20,30].
  Proof.
    reflexivity.
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
    reflexivity.
  Qed.

  Example test_count2: count 6 [1,2,3,1,4,1] = 0.
  Proof.
    reflexivity.
  Qed.

  Definition sum : bag -> bag -> bag := app.

  Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
  Proof.
    reflexivity.
  Qed.

  Definition add (v:nat) (s:bag) : bag := v :: s.

  Example test_add1: count 1 (add 1 [1,4,1]) = 3.
  Proof.
    reflexivity.
  Qed.

  Example test_add2: count 5 (add 1 [1,4,1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Definition member (v:nat) (s:bag) : bool :=
    match (count v s) with
    | 0 => false
    | S _ => true
    end.

  Example test_member1: member 1 [1,4,1] = true.
  Proof.
    reflexivity.
  Qed.

  Example test_member2: member 2 [1,4,1] = false.
  Proof.
    reflexivity.
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
    reflexivity.
  Qed.

  Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one4:
    count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
  Proof.
    reflexivity.
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
    reflexivity.
  Qed.

  Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
  Proof.
    reflexivity.
  Qed.

  Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
    match s2 with
    | nil => beq_nat 0 (length s1)
    | y :: ys => subset (remove_one y s1) ys
    end.

  Example test_subset1: subset [1,2] [2,1,4,1] = true.
  Proof.
    reflexivity.
  Qed.

  Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
  Proof.
    reflexivity.
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
    reflexivity.
  Qed.

  Theorem tl_length_pred : forall l : natlist,
      pred (length l) = length (tail l).
  Proof.
    intros l.
    destruct l.
      reflexivity.
      reflexivity.
  Qed.

  Theorem app_ass : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3.
    induction l1.
      reflexivity.
      simpl. rewrite IHl1. reflexivity.
  Qed.

  Theorem app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2.
    induction l1.
      reflexivity.
      simpl. rewrite IHl1. reflexivity.
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
    reflexivity.
  Qed.

  Example test_rev2 : rev nil = nil.
  Proof.
    reflexivity.
  Qed.

  Theorem length_snoc : forall n : nat, forall l : natlist,
        length (snoc l n) = S (length l).
  Proof.
    intros n l.
    induction l.
      reflexivity.
      simpl. rewrite IHl. reflexivity.
  Qed.
    
  Theorem rev_length : forall l : natlist,
      length (rev l) = length l.
  Proof.
    intros l.
    induction l.
      reflexivity.
      simpl. rewrite length_snoc. rewrite IHl. reflexivity.
  Qed.

  Theorem app_nil_end : forall l : natlist,
      l ++ [] = l.
  Proof.
    intros l.
    induction l.
      reflexivity.
      simpl. rewrite IHl. reflexivity.
  Qed.
  
  Theorem rev_app : forall n : nat, forall l : natlist,
        rev (snoc l n) = n :: (rev l).
  Proof.
    intros n l.
    induction l.
      reflexivity.
      simpl. rewrite IHl. reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    intros l.
    induction l.
      reflexivity.
      simpl. rewrite rev_app. rewrite IHl. reflexivity.
  Qed.

  Theorem snoc_app : forall l1 l2 : natlist, forall n : nat,
        snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
  Proof.
    intros l1 l2 n.
    induction l1.
      reflexivity.
      simpl. rewrite IHl1. reflexivity.
  Qed.

  Theorem distr_rev : forall l1 l2 : natlist,
      rev (l1 ++ l2) = (rev l2) ++ (rev l1).
  Proof.
    intros l1 l2.
    induction l1.
      simpl. rewrite app_nil_end. reflexivity.
      simpl. rewrite IHl1. rewrite snoc_app. reflexivity.
  Qed.

  Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite app_ass. rewrite app_ass. reflexivity.
  Qed.

  Theorem snoc_append : forall (l : natlist) (n : nat),
      snoc l n = l ++ [n].
  Proof.
    intros l n.
    induction l.
      reflexivity.
      simpl. rewrite IHl. reflexivity.
  Qed.

  (* list_design *)

  Theorem count_member_nonzero : forall (s : bag),
      ble_nat 1 (count 1 (1 :: s)) = true.
  Proof.
    intros s.
    induction s.
      reflexivity.
      reflexivity.
  Qed.

  Theorem ble_n_Sn : forall n,
      ble_nat n (S n) = true.
  Proof.
    intros n.
    induction n.
      reflexivity.
      simpl. trivial.
  Qed.

  Theorem remove_decreases_count: forall (s : bag),
      ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    intros s.
    induction s.
      reflexivity.
      induction n.
        simpl. rewrite ble_n_Sn. trivial.
        simpl. trivial.
  Qed.

  Theorem rev_injective : forall l1 l2 : natlist,
      rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2 H.
    rewrite <- rev_involutive.
    rewrite <- H.
    rewrite rev_involutive.
    trivial.
  Qed.

  Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

  Fixpoint index_bad (n : nat) (l : natlist) : nat :=
    match l with
    | nil => 42
    | a :: l' => match beq_nat n 0 with
                | true => a
                | false => index_bad (pred n) l'
                end
    end.

  Fixpoint index (n : nat ) (l : natlist) : natoption :=
    match l with
    | nil =>  None
    | a :: l' => match beq_nat n 0 with
                | true => Some a
                | fasle => index (pred n) l'
                end
    end.

  Example test_index1 : index 0 [4,5,6,7] = Some 4.
  Proof.
    reflexivity.
  Qed.

  Example test_index2 : index 3 [4,5,6,7] = Some 7.
  Proof.
    reflexivity.
  Qed.

  Example test_index3 : index 10 [4,5,6,7] = None.
  Proof.
    reflexivity.
  Qed.

  
  Fixpoint index' (n : nat ) (l : natlist) : natoption :=
    match l with
    | nil =>  None
    | a :: l' => if beq_nat n 0 then
                  Some a
                else
                  index' (pred n) l'
    end.

  Definition option_elim (o : natoption) (d : nat) : nat :=
    match o with
    | Some n' => n'
    | None => d
    end.

  Definition hd_opt (l : natlist) : natoption :=
    match l with
    | nil => None
    | x :: xs => Some x
    end.
  
  Example test_hd_opt1 : hd_opt [] = None.
  Proof.
    reflexivity.
  Qed.

  Example test_hd_opt2 : hd_opt [1] = Some 1.
  Proof.
    reflexivity.
  Qed.

  Example test_hd_opt3 : hd_opt [5,6] = Some 5.
  Proof.
    reflexivity.
  Qed.
  
  Theorem option_elim_hd : forall (l: natlist) (default: nat),
      head default l = option_elim (hd_opt l) default.
  Proof.
    intros l d.
    induction l.
      reflexivity.
      reflexivity.
  Qed.

  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | nil, nil => true
    | (x :: _), nil => false
    | nil, (y :: _) => false
    | (x :: xs), (y :: ys) => match (beq_nat x y) with
                           | true => beq_natlist xs ys
                           | false => false
                           end
    end.

  Example test_beq_natlist1 : (beq_natlist nil nil = true).
  Proof.
    reflexivity.
  Qed.
  
  Example test_beq_natlist2 : beq_natlist [1,2,3] [1,2,3] = true.
  Proof.
    reflexivity.
  Qed.
  
  Example test_beq_natlist3 : beq_natlist [1,2,3] [1,2,4] = false.
  Proof.
    reflexivity.
  Qed.
  
  Theorem beq_natlist_refl : forall l:natlist,
      true = beq_natlist l l.
  Proof.
    intros l.
    induction l.
      reflexivity.
      simpl. rewrite <- IHl.
      induction n.
        reflexivity.
        simpl. trivial.
  Qed.

  Theorem silly1: forall (n m o p : nat),
      n = m ->
      [n, o] = [n, p] ->     
      [n, o] = [m, p].
  Proof.
    intros n m o p H1 H2.
    rewrite <- H1.
    apply H2.
  Qed.

  Theorem silly2: forall (n m o p : nat),
      n = m ->      
      (forall (q r : nat), q = r -> [q, o] = [r, p]) ->
      [n, o] = [m, p].
  Proof.
    intros n m o p H1 H2.
    apply H2.
    apply H1.
  Qed.

  
  Theorem silly2a : forall (n m : nat),
      (n,n) = (m,m) ->
      (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
      [n] = [m].
  Proof.
    intros n m H1 H2.
    apply H2. trivial.
  Qed.

  Theorem silly_ex :
    (forall n, evenb n = true -> oddb (S n) = true) ->
    evenb 3 = true ->
    oddb 4 = true.
  Proof.
    intros H1 H2.
    apply H1. trivial.
  Qed.

  Theorem silly3 : forall (n : nat),
      true = beq_nat n 5 ->
      beq_nat (S (S n)) 7 = true.
  Proof.
    intros n H.
    symmetry.
    simpl. trivial.
  Qed.

  Theorem rev_exercise1 : forall (l l' : natlist),
      l = rev l' -> l' = rev l.
  Proof.
    intros l l' H.
    rewrite H.
    rewrite rev_involutive.
    reflexivity.
  Qed.
  
  Theorem app_ass' : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1.
    induction l1 as [| n l'].
      reflexivity.
      intros l2 l3. simpl.
      rewrite (IHl' l2 l3). trivial.
  Qed.

  Theorem beq_nat_sym : forall (n m : nat),
      beq_nat n m = beq_nat m n.
  Proof.
    intros n. induction n as [| n'].
      intros m. induction m. reflexivity. reflexivity.
      intros m. induction m. reflexivity. simpl. apply IHn'.
  Qed.

End NatList.

Module Dictionary.

  Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

  Definition insert (key value : nat) (d : dictionary) : dictionary :=
    (record key value d).
  
  Fixpoint find (key : nat) (d : dictionary) : option nat :=
    match d with
    | empty => None
    | record k v d' => if (beq_nat key k) then
                         Some v
                       else
                         find key d'
    end.

  Theorem dictionary_invariant1 : forall (d : dictionary) (k v : nat),
      (find k (insert k v d)) = Some v.
  Proof.
    intros d k v.
    induction d.
      simpl. rewrite <- beq_nat_refl. reflexivity.
      simpl. rewrite <- beq_nat_refl. reflexivity.
  Qed.

  Theorem dictionary_invariant2 : forall (d : dictionary) (m n o : nat),
      (beq_nat m n) = false -> (find m d) = (find m (insert n o d)).
  Proof.
    intros d m n o H.
    induction d.
      simpl.  rewrite H.
      reflexivity.
      simpl. rewrite H. reflexivity.
  Qed.

End Dictionary.

Definition beq_nat_sym := NatList.beq_nat_sym.
      