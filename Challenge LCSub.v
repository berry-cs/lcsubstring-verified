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


(*The purpose of this fixpoint is to take a list of lists and return the longest list
element. In this case, we will pass this a list of subsequences and it will return
the longest subsequence. *)

Fixpoint longest_subseq (l: list (list nat )) : list nat :=

 match l with
 | [] => [] (* if the list of subsequences is (l) is empty then return empty*)
(* | [a] => a   ---  Don't include this -- it makes for more cases in proofs *)
 
 | h :: t => let C := (longest_subseq t) in
             if Datatypes.length C <=?
                Datatypes.length h
             then h
             else C

 (* if there is a subsequence list that is longer than the initial head subsequence then
  override the variable C with the longer sequence.  Continue to compare until you hit
   the end of the list *)

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




Ltac silly_in :=
  match goal with
   | x : In _ [] |- _ => inversion x
   | x : In _ (common_subseq [] _) |- _ => inversion x
  end.


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
intros. 
split.

induction l1 as [ | h t IHL].
  - intros Heq. silly_in. (*simpl in *. inversion Heq. *)
  - intros Heq. split. simpl. simpl in Heq. destruct (contains_list h l2) eqn: Heq2.
  simpl in Heq. destruct Heq. left. auto. apply IHL in H. destruct H. right. apply H.
  apply IHL in Heq. destruct Heq. right. apply H. 
  simpl in Heq. destruct (contains_list h l2) eqn:Heq2. simpl in Heq. destruct Heq. 
  rewrite contains_list_In in Heq2. rewrite H in Heq2. apply Heq2.
  apply IHL in H. destruct H. apply H0.
  apply IHL in Heq. destruct Heq; auto.

  - induction l1;
    intros (H1, H2).
    silly_in.
    simpl in *. destruct (contains_list a l2) eqn:Heq2. 
    -- simpl. destruct H1.
              --- left.
                  apply H.
              --- right. apply IHl1. split. auto. auto.

    -- apply IHl1.
      split; auto.
      destruct H1; auto.
      rewrite H in Heq2.
      rewrite <- contains_list_In in H2.
      rewrite H2 in Heq2. inversion Heq2.
Qed.


(* Hints:
   - Nat.leb_gt and Nat.leb_le may be useful
*)
Lemma longest_subseq_correct :
  forall lstlsts lst, In lst lstlsts -> length lst <= length (longest_subseq lstlsts).
(* If a subsequence (lst) is in the list of subquences (lstlsts),
  the length of the subsequence (lst) is lesser than or equal to the length of the longest 
  list element in the list of subsequences (lstlsts)*)
Proof.
  intros. 
  induction lstlsts as [ | h lstlsts' ]. 
  (*two cases *)

  (* first case *)
    - simpl. intros. simpl in H. inversion H.
    (* This case is where the list of lists is empty and H is contradictory.
          By definition there can never be a subsequence in an empty list*)

  (*second case*)
  (*this is the case where the list of subsequences is not empty *)
    - simpl. intros. (* this simpl unfolds In into two cases where the subsequence is either in the 
                          head or the tail*)

      destruct H as [H1 | H1].  (*destruct the hypothesis H into two cases where the subsequence is either
                                  in the head or somewhere in the rest of the list *)
     (* destruct H case 1*)
     (* This case is where the subsequence (lst) is the head *)
      -- rewrite H1. (*replaces the h in the goal with lst using H1 as the proof *)
         (* assuming that lst is equal to h, we then need to anaylze whether the head is
            greater than or equal to the rest of the list *)
         destruct (length(longest_subseq lstlsts') <=? length lst) eqn:Heq; auto.
         (* the first case where lst, the head, is the longest subsequence is 
            self explanatory to prove as the length of lst is less than or equal to itself *)
         rewrite Nat.leb_nle in Heq.
         (* In the second case the longest subsequence is found in the tail and is
            proved as the goal and our Heq hypothesis are effectievly the same as 
            if length lst is less than or equal to length of the largest subsequence
            of the tail then length lst is not greater than length of the largest
            subsequence of the tail *)
        lia.
      (* This case is where the subsequence (lst) is in the tail of the list of lists *)
      (* We first have to destruct to see whether the longest element in the list of
         subsequences is the *)
      -- destruct ( length (longest_subseq lstlsts') <=? length h) eqn:Heq; auto.
         rewrite Nat.leb_le in Heq. (* turns the boolean to computational *)
         Search (_ <= _ -> _ <= _ -> _ <= _).
         (* In the inductive hypothesis, we have that the length of lst is less than
            or equal to the length of the longest subsequence of the tail. In Heq,
            we have that the length of the longest subsequence of the tail is less
            than or equal to the length of h. Therefore by the transitive property, 
            we have that the length of lst is less than the length of h. *)
         apply Nat.le_trans with (m := length (longest_subseq lstlsts')).
         (* Now we can apply the inductive hypothesis and then 
            auto applies H1 and Heq *)
         apply IHlstlsts'. auto.
         auto.
Qed.


Lemma longest_subseq_In :
  forall lstlsts, lstlsts <> nil -> In (longest_subseq lstlsts) lstlsts.
  (* As long as a list of sbusequences is not equal to nil, then the longest subsequence
     of a list of subsequences must be in the original list of subsequences *)
Proof.
  induction lstlsts as [ | h t].
  (* two cases *)
        (* in the first case where the list of subsequences is empty, this contradicts the
           initial premise and therefore is nonsensical*)
      - simpl. auto.
        (* in the second case where the list of subsequences is not empty we have to break
           this down into further cases where we first unfold In into the head and tail.
           we then have to destruct the conditional if where the head is either the longest
           subsequence or the longest subsequence is in the tail *)
      - simpl. intros. destruct (length (longest_subseq t) <=? length h ) eqn: Heq.
           (* the case where h is the longest subsequence, we choose the left case where h
              = to h is reflexivly true *)
        -- left. auto.
           (* in the second case, where h is not the longest subsequence, we work with
              the right case, where the longest subsequence of the tail is in the tail
              which is equal to our inductive hypothesis *)
        -- right. apply IHt. 
           (* applying our inductive hypotehsis we must further prove that t is not 
              equal to empty which is true by our premise *)
           rewrite Nat.leb_nle in Heq.
           (* since we know the head is not the longest, the head must be shorter than
              everything else in the list which means the longest subsequence in the tail
              can not be empty *)
           assert ( length h < length (longest_subseq t)  ).
           lia.
           (* doing case analysis on t *)
           destruct t; auto.
           (* the first case where t is empty is nonsensical because H0 simplified is
           saying that the length of h is less than 0 *)
           simpl in H0. inversion H0. 
           
           intros Habs. (*l::t cannot be equal to empty, by the definition of cons. *)
           inversion Habs.
Qed.

(* Hints:
   - use  in_map_iff   (rewrite in_map_iff in ...)
*)
Lemma not_nil_in_all_prefixs : forall l, ~In [] (all_prefixs l).
Proof.
induction l as [ | h t ].
- simpl. unfold not. auto.
- simpl. unfold not. intros. rewrite in_map_iff in H. inversion H. inversion H0. simpl in *. 
  inversion H0. destruct H1.
    -- inversion H1.
 Qed.


(* Hints:
   - Use in_or_app.
   - this one is really short
*)
Lemma nil_in_all_subseqs : forall l, In [] (all_subseqs l).
Proof.
  induction l; simpl; auto.
  right; auto. 
  Search (In _ (_ ++ _)).
  apply in_or_app; auto.
Qed.

(* Lots of subcases on this one!
   in_map_iff   is helpful. *)
Lemma all_prefs_correct : forall ns ss,
    In ss (all_prefixs ns) <-> exists h, exists t, ss = h::t /\ Prefix ss ns.
Proof.
  split.
  {
    generalize dependent ss.
    induction ns.
    - intros ss H; simpl in H; inversion H.
(*      rewrite <- H0; constructor.
      inversion H0.*)
    - intros ss [H | H]; simpl in H.
      -- exists a; exists nil; split; auto.
         rewrite <- H. apply pref_cons. apply pref_nil.
      -- destruct ss as [ | p' ss'] eqn:Heq.
         --- rewrite in_map_iff in H.
             destruct H as (x, (H1, H2)); inversion H1.
         --- exists p'; exists ss'; split; auto.
             assert (H' := H).
             rewrite in_map_iff in H'.
             destruct H' as (x, (H1, H2)).
             inversion H1; replace p' with a; auto.
             constructor.
             destruct (IHns _ H2) as (_, (_, (_, IHnss))).
             replace ss' with x; auto.
  }
  {
    generalize dependent ss.
    induction ns as [ | n ns' ].
    - intros ss (h, (t, (He, Hp))); inversion Hp; simpl; auto.
      rewrite He in H; discriminate.
    - intros ss (h, (t, (He, Hp))).
      rewrite He in *; clear ss He.
      replace h with n in *; try clear h.
      2: { inversion Hp; auto. }
      inversion Hp.
      simpl.
      destruct t as [ | n' t']; auto.
      right.
      apply in_map.
      apply IHns'.
      eauto.
  }
Qed. 



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
  intros.
  assert (In [] (common_subseq (all_subseqs lA) (all_subseqs lB))).
  apply common_subseq_correct. split; apply nil_in_all_subseqs.
  intros H1. rewrite H1 in H. inversion H.
  Qed.


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





