(*Largest Common Substring List of Numbers*)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
Locate "+".


Print Datatypes.length.

Print last.
Print removelast.

Definition lstA := [ 1; 5; 10; 3; 6; 4].
Definition lstB := [ 9; 2; 6; 4; 5; 10; 3].



Fixpoint all_prefixs  (l : list nat) : list (list nat) := 
  match l with 
    | nil => nil
 (*   | [h] => [[h]] *)
    | h :: t => [[h]] ++ (map (fun lst => (cons h lst)) (all_prefixs t))
  end.
  

Compute (all_prefixs lstA).



Fixpoint all_subseqs (ns : list nat) : list (list nat) :=
  match ns with 
     | nil => [ns]
     | h::t => ( all_prefixs ns ) ++ (all_subseqs t) 
      
  end.


Compute all_subseqs lstA.


Compute (all_subseqs lstA).

Definition common_subseq: 
            list (list nat) -> list (list nat) -> list (list nat). 

Admitted.

Definition longest_subseq: list (list nat ) -> list nat.
Admitted.




Definition lcs (A B : list nat) : list nat :=
longest_subseq
  (common_subseq (all_subseqs A) (all_subseqs B)).



