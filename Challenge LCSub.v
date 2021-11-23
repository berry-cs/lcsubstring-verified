(*Largest Common Substring List of Numbers*)

From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
Locate "+".
From Coq Require Import Nat.

Definition lstA := [ 1; 5; 10; 3; 6; 4].
Definition lstB := [ 9; 2; 6; 4; 5; 10; 3].


(* Note: this produces all *** non-empty *** prefixes,
         which is slightly different than the concept defined by the Prefix property below *)
Fixpoint all_prefixs  (l : list nat) : list (list nat) := 
  match l with 
    | nil => nil
 (*   | [h] => [[h]] ---  Don't include this case -- it makes for more cases in proofs *)
    | h :: t => [[h]] ++ (map (fun lst => (cons h lst)) (all_prefixs t))
  end.
  
Compute (all_prefixs lstA).


Fixpoint all_subseqs (ns : list nat) : list (list nat) :=
  match ns with 
     | nil => [ns]
     | h::t => ( all_prefixs ns ) ++ (all_subseqs t) 
      
  end.

Compute all_subseqs lstA.


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
(*        | [h] => if(same_list h l1)    ---  Don't include this-- it makes for more cases in proofs
                      then true
                      else false*)
        | h::t => if (same_list h l1) 
                            then true 
                            else contains_list l1 t
      end.


Fixpoint common_subseq (l1 l2: list (list nat)) : list (list nat) :=
           match l1, l2 with 
       (* | _ , nil => nil  ---  Don't include this-- it makes for more cases in proofs *)
        |  nil, _ => nil 
        |  h :: t, _ =>  if (contains_list  h l2)
                            then h :: common_subseq  t l2
                            else common_subseq t l2 
      end. 

Compute (common_subseq (all_subseqs lstA)(all_subseqs lstB)).



Fixpoint longest_subseq (l: list (list nat )) : list nat :=
 match l with
 | [] => []
(* | [a] => a   ---  Don't include this -- it makes for more cases in proofs *) 
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


(* *********** Proving correctness of lcs ************ *)

(* Prefix A B means "A is a prefix of B", A could be nil. *)
Inductive Prefix : list nat -> list nat -> Prop :=
  | pref_nil : forall p, Prefix [] p
  | pref_cons : forall x p q, Prefix p q -> Prefix (x::p) (x::q).

(* Subseq A B means "A is a consecutive subsequence of B", A could be nil *)
Inductive Subseq : list nat -> list nat -> Prop := 
  | ss_pref : forall p q, Prefix p q -> Subseq p q
  | ss_cons : forall x p q, Subseq p q -> Subseq p (x::q).




(* Hints:
   - use Nat.eqb_refl
*)
Lemma same_list_refl : forall lA, same_list lA lA = true.
Proof.
  intros. induction lA.
  - reflexivity.
  - simpl. rewrite Nat.eqb_refl.
    apply IHlA.
Qed.


(* Hints:
   - Start with  `split`, then prove both directions
*)
Lemma same_list_eq : forall lA lB, same_list lA lB = true <-> lA = lB.
Proof.
split.
- generalize dependent lB. induction lA.
  * intros. simpl in H. destruct lB. auto. discriminate.
  * intros. destruct lB. simpl in H. discriminate. simpl in H. destruct (a =? n) eqn:Han.
    + Search (_ =? _ = true). rewrite Nat.eqb_eq in Han. rewrite Han. replace lA with lB.
      auto. symmetry. apply IHlA. auto.
    + discriminate.
- generalize dependent lB. induction lA.
  * intros. destruct lB. auto. discriminate.
  * intros. destruct lB. discriminate. rewrite H. apply same_list_refl.
Qed.



(* Hints:
   - Uses same_list_eq and same_list_refl.
*)
Lemma contains_list_In : forall lst lstlsts, contains_list lst lstlsts = true <-> In lst lstlsts.
Proof.
  intros. split.
  - induction lstlsts. 
    -- intros. discriminate.
    -- intros. simpl in *. destruct (same_list a lst) eqn:Heq. 
      + left. rewrite <- same_list_eq. apply Heq. 
      + right. rewrite H in IHlstlsts. apply IHlstlsts. reflexivity.
  - induction lstlsts.
    -- intros. inversion H.
    -- intros. simpl in *. destruct (same_list a lst) eqn:Heq ; auto.
       apply IHlstlsts.
       destruct H.
       --- rewrite <- same_list_eq in H.
           rewrite H in Heq.
           discriminate.
       --- auto.
Qed.


(* Hints:
   - split and use induction on l1. 
   - uses contains_list_In  (rewrite contains_list_In)
   - when you have terms that get stuck on simplifying of the form
       (if (blah) then ... else ...)
     then  destruct (blah) eqn:Heq.
*)
Lemma common_subseq_correct :
      forall l1 l2 lst,  In lst (common_subseq l1 l2) <-> In lst l1 /\ In lst l2.
Proof.
(*on my other computer*)
Admitted.


(* Hints:
   - Nat.leb_gt and Nat.leb_le may be useful
*)
Lemma longest_subseq_correct :
  forall lstlsts lst, In lst lstlsts -> length lst <= length (longest_subseq lstlsts).
Proof.
  intros.

  generalize dependent lst.
  induction lstlsts as [ | h lstlsts' ].
    - simpl. intros. simpl in H. inversion H.
    - simpl. intros.
      destruct H as [H1 | H1].
      -- rewrite H1. 
         destruct (length(longest_subseq lstlsts') <=? length lst) eqn:Heq; auto.
         rewrite Nat.leb_nle in Heq.
        lia.
      -- destruct ( length (longest_subseq lstlsts') <=? length h) eqn:Heq; auto.
         rewrite Nat.leb_le in Heq.
         Search (_ <= _ -> _ <= _ -> _ <= _).
         apply Nat.le_trans with (m := length (longest_subseq lstlsts')).
         apply IHlstlsts'; auto.
         auto.
Qed.


Lemma longest_subseq_In :
  forall lstlsts, lstlsts <> nil -> In (longest_subseq lstlsts) lstlsts.
Proof.
  induction lstlsts as [ | h t].
      - simpl. auto.
      - simpl. intros. destruct (length (longest_subseq t) <=? length h ) eqn: Heq.
        -- left. auto.
        -- right. apply IHt. 
           rewrite Nat.leb_nle in Heq.
           assert ( length h < length (longest_subseq t)  ).
           lia.
           destruct t; auto.
           simpl in H0. inversion H0.
           intros Habs. 
           inversion Habs.
Qed.

(* Hints:
   - use  in_map_iff   (rewrite in_map_iff in ...)
*)
Lemma not_nil_in_all_prefixs : forall l, ~In [] (all_prefixs l).
Proof.
induction l as [ | h t ].
- simpl. unfold not. auto.
- simpl. unfold not. intros. 
Admitted.


(* Hints:
   - Use in_or_app.
   - this one is really short
*)
Lemma nil_in_all_subseqs : forall l, In [] (all_subseqs l).
Proof.
Admitted.


(* Lots of subcases on this one!
   in_map_iff   is helpful. *)
Lemma all_prefs_correct : forall ns ss,
    In ss (all_prefixs ns) <-> exists h, exists t, ss = h::t /\ Prefix ss ns.
Proof.
Admitted.



(* I'll give you this one -- proved in both directions. *)
Lemma all_subs_correct : forall ns ss, 
               In ss (all_subseqs ns) <-> Subseq ss ns.
Proof.
  split.
  {
    generalize dependent ss.
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
              rewrite all_prefs_correct in H.
              destruct H as (h, (t, (H1, H2))); auto.
         }
  }
  {
    generalize dependent ss.
    induction ns as [ | n ns' IHns].
    - simpl. intros ss Hss.
      inversion Hss.
      inversion H; auto.
    - intros ss Hss.
      inversion_clear Hss.
      -- destruct ss as [ | h t ].
         --- apply nil_in_all_subseqs; auto.
         --- replace h with n in *; try clear h.
             2: { inversion H; auto. }
             inversion_clear H.
             assert (Subseq t ns'). { constructor; auto. }
             apply IHns in H.
             simpl.
             destruct t as [ | n' t'].
             + left; auto.
             + right.
               apply in_or_app.
               left.
               apply in_map.
               apply all_prefs_correct; eauto.
     -- simpl.
        right.
        apply in_or_app.
        auto.
        }
Qed.

(* Hints:
   - not very long, use common_subseq_correct and nil_in_all_subseqs.
*)
Lemma common_subseq_all_subseqs_not_nil :
  forall lA lB, common_subseq (all_subseqs lA) (all_subseqs lB) <> [].  
Proof.
Admitted.


(* Put it all together! *)
Theorem lcs_correct :
  forall lA lB lC,
    lC = (lcs lA lB) -> Subseq lC lA /\ (* lC is a subsequence of each list ... *)
                        Subseq lC lB /\ (* ... and is at least as long as any other
                                               common subsequence, lst *)
                        (forall lst, Subseq lst lA /\ Subseq lst lB -> length lst <= length lC).
Proof.
  intros lA lB lC Hlcs.
  unfold lcs in Hlcs.
  assert (In lC (common_subseq (all_subseqs lA) (all_subseqs lB))).
  {
    rewrite Hlcs; apply longest_subseq_In.
    apply common_subseq_all_subseqs_not_nil.
  }
  rewrite common_subseq_correct in H.
  destruct H as [H1 H2].
  split.
  - apply all_subs_correct; auto.  (* Subseq lC lA *)
  - split.
    -- apply all_subs_correct; auto. (* Subseq lC lB *)
    -- intros lst (HA, HB).
       rewrite Hlcs.
       apply longest_subseq_correct.
       rewrite common_subseq_correct.
       split; rewrite all_subs_correct; auto.
Qed.
