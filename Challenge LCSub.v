(*Largest Common Substring List of Numbers*)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
Locate "+".


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

Print hd.

Compute (lstA = lstB).
Print forallb.
Print Nat.eqb.



Fixpoint same_list (l1 l2 : list nat) : bool :=
        match l1, l2 with 
        | nil , nil =>  true
        | nil, _ => false 
        | _ , nil => false
        | h0 :: t0 , h1 :: t1 =>  if ( Nat.eqb h0 h1)
                                        then same_list t0 t1 
                                         else false
      end.


Compute (same_list lstA lstB). 
Compute (same_list lstA lstA).


Fixpoint contains_list (l1: list nat )(l2: list (list nat)) : bool :=
          match l2 with 
        | nil => false
        | [h] => if(same_list h l1) 
                      then true
                      else false
        | h::t => if (same_list h l1) 
                            then true 
                            else contains_list l1 t
      end.



Fixpoint common_subseq (l1 l2: list (list nat)) : list (list nat) :=
           match l1, l2 with 
        | _ , nil => nil
        |  nil, _ => nil 
        |  h :: t, _ =>  if (contains_list  h l2)
                            then h :: common_subseq  t l2
                            else common_subseq t l2 
      end. 

Compute (common_subseq (all_subseqs lstA)(all_subseqs lstB)).




Fixpoint longest_subseq (l: list (list nat )) : list nat :=
 match l with
 | [] => []
 | [a] => a
 | h :: t => let C := (longest_subseq t) in
             if Datatypes.length C <=?
                Datatypes.length h
             then h
             else C
 end.

Compute longest_subseq (all_subseqs lstA).



Definition lcs (A B : list nat) : list nat :=
longest_subseq
  (common_subseq (all_subseqs A) (all_subseqs B)).


Compute (lcs lstA lstB).




Inductive Prefix : list nat -> list nat -> Prop :=
  | pref_nil : forall p, Prefix [] p
  | pref_cons : forall x p q, Prefix p q -> Prefix (x::p) (x::q).

Inductive Subseq : list nat -> list nat -> Prop := 
  | ss_pref : forall p q, Prefix p q -> Subseq p q
  | ss_cons : forall x p q, Subseq p q -> Subseq p (x::q).


Lemma all_subs_refl : forall ns ss, 
               In ss (all_subseqs ns) -> Subseq ss ns.
Proof.
  intros ns.
  induction ns as [ | n ns' IHns].
  - simpl. intros ss [H | H].
    -- rewrite <- H. constructor. constructor.
    -- inversion H.
  - intros ss Hin.
    -- unfold all_subseqs in Hin. fold all_subseqs in Hin.
        
Search (In _ (_ ++ _)).
       destruct (in_app_or _ _ _ Hin).
  2: {     apply ss_cons.
    apply IHns. auto.
     }
 1: { apply ss_pref.
      apply all_prefs_refl. 
}
Qed.

   


