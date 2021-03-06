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
(* Splits the list into a head and a tail and then works backwards 
   generating all prefixes of the tail before mapping the head on to 
   each of them. *)
Fixpoint all_prefixs  (l : list nat) : list (list nat) := 
  match l with 
    | nil => nil
 (*   | [h] => [[h]] ---  Don't include this case -- it makes for more cases in proofs *)
    | h :: t => [[h]] ++ (map (fun lst => (cons h lst)) (all_prefixs t))
  end.
  
Compute (all_prefixs lstA).


(* This iterates through a list of natural numbers appending the list of all prefixes
   from each possible starting point into a larger list of all possible subsequences including
   empty *)
Fixpoint all_subseqs (ns : list nat) : list (list nat) :=
  match ns with 
     | nil => [ns]
     | h::t => (all_prefixs ns) ++ (all_subseqs t) 
  end.

Compute all_subseqs lstA.

(* checks if the two given lists are the same *)
Fixpoint same_list (l1 l2 : list nat) : bool :=
        match l1, l2 with 
        | nil , nil =>  true (* if they are both nil return true*) 
        | nil, _ => false (* if the first is nil and the second is not return false *)
        | _ , nil => false (* if the second is nil and the first is not return false *)

        (* in the case that they are both non empty lists the function will recursively check the
           head of the list to make sure that they are equal *) 
        | h0 :: t0 , h1 :: t1 =>  if ( Nat.eqb h0 h1)
                                        then same_list t0 t1 
                                         else false 
      end.
Compute (same_list lstA lstB). 
Compute (same_list lstA lstA).


(* This recursively checks if l1 is equal to any of the elements
   of l2. If theres a match it returns true, otherwise false. 
   This is effectively a computational version of In *)
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

(*For all lists lA, lA is the same_list as lA *)
Lemma same_list_refl : forall lA, same_list lA lA = true.
Proof.
  intros. induction lA.
    (* induction on lA to break it into its two cases*)
    (* The first case is where lA is empty*)
  - reflexivity. (* This is trivial by the definition of same_list *)

    (*The second case where lA is a list and has a head and a tail*)
  - simpl.
    (* this simpl unfolds same_list *)
     rewrite Nat.eqb_refl. (* we use Nat.eqb_refl to rewrite the conditional that
                               compares the head of the list. This shows that the 
                                conditional will always return true*)

    apply IHlA. (* From here we can apply the inductive hypothesis *)
Qed.


(* Hints:
   - Start with  `split`, then prove both directions
*)

(*forall lists lA and lB, lA equals lB if and only if same_list lA lB equals true   *)
Lemma same_list_eq : forall lA lB, same_list lA lB = true <-> lA = lB.
Proof.
split. (* split in the two directions of the if and only if *)

-  generalize dependent lB. (* generalize lB so that it applies to any arbitrary list 
                                and not a specific list *)
   induction lA. (* induction on lA to split it into its two cases*)
      (* In the first case lA is an empty list, then we simpl in H to show that for same_list
         to be true lB also must be empty.  *)
      * intros. simpl in H. destruct lB. (*destruct lB into its two cases *)
          -- auto. (* the first case is trivial based on the definition of same_list*)
          -- discriminate. (* the second case is nonsensical  based on the definition of same_list*)

      (* This is the second case where lA is a head cons onto a tail*)
      (**)
      * intros. 
           destruct lB. (* destruct lB into its two cases *)

               (* first case where lB is empty *)
              -- simpl in H. discriminate. (*simpl H so that it shows the contradiction
                                             between the definition of same_list and the 
                                             current hypothesis *) 

              -- simpl in H. destruct (a =? n) eqn:Han. (* simpl H to unfold same_list and 
                                                            destruct the conditional into
                                                            its two cases*)
                  (* The first case is where the heads of the lists are the same
                      then we use Nat.eqb_eq to rewrite the boolean to the equality in Han  *)
                    + Search (_ =? _ = true). rewrite Nat.eqb_eq in Han. 
                      (* Then we can rewrite Han in our goal. Then we can replace lA with lB since 
                          H tells us they are equal. We use auto to take care of the goal that is 
                          reflexively true. *)  
                      rewrite Han. replace lA with lB. auto. 
                      (*The we use symmetry to flip the goal so that it matches our inductive hypothesis
                        We then apply the inductive hypothesis and then apply H using auto. *)
                      symmetry. apply IHlA. auto.

                     (* The second case where the heads of the lists are different, this means 
                        same_list is automatically false which makes H nonsensical*)
                    + discriminate.
(*second direction *) 

- generalize dependent lB. (* generalize lB so that it applies to any arbitrary list 
                                and not a specific list *)
induction lA.  (* induction on lA to split it into its two cases*)

  (* The first case where lA is empty*)
  * intros. 
        destruct lB. (*destruct lB into its two cases*)
            (*first case where lA and lB are both empty*)
          -- auto. (* this is reflexive by the definition of same_list and thus handled by auto.*)
          -- discriminate. (*this case is nonsensical based on the definition of same_list *)
    (*This is the second case where lA is a heads cons onto a tail *)
  * intros. destruct lB. (*destruct lB into its two cases *) 
      (* first case where lB is empty *)
      -- discriminate. (* this is nonsensical based on the definition of same_list *)

      (* rewrite H into the goal to show that the lists are the same*) 
      -- rewrite H. apply same_list_refl. (* use the previously proven same_list_refl to show that a list
                                             is always the same as itself *)
Qed.



(* Hints:
   - Uses same_list_eq and same_list_refl.
*)
(* For any given list and list of lists, the list of lists
   contains the list if, and only if, the list is In the list of lists *)
Lemma contains_list_In : forall lst lstlsts, 
      contains_list lst lstlsts = true <-> In lst lstlsts.
Proof.
  intros.
  (* Split into the two directions *)
  split.
  (* Case analysis on the list of lists giving us two cases *)
  - induction lstlsts. 
    (* in the first case where lstlsts is empty, it's impyling that 
       lst is contained within an empty list which is nonsensical by 
       our defintion of contains_list *)
    -- intros. discriminate.
    (* in the second case where the list of lists is not empty, we introduce 
       the premise, and then simplify both the premise and the goal into the cases where lst
       is in the head or lst is in the tail. *)
    -- intros. simpl in *.
       (* we then destruct the conditional in H into its two cases *)
       destruct (same_list a lst) eqn:Heq. 
       (* in the fist case where lst matches the head of lstlsts, 
          we utilize the left case, using our previous lemma same_list_eq
          which takes the computational equality in our goal and turns it
          into a boolean comparison aligning with our premise. 
          Thus allowing us to apply Heq *)
       + left. rewrite <- same_list_eq. apply Heq. 
       (* in the second case where lst is in the tail, we utilize the right 
          case allowing us to rewrite H in our inductive hypothesis. The 
          inductive hypothesis then matches our goal and can be applied 
          leaving a conclusion that is refleively true *)
       + right. rewrite H in IHlstlsts. apply IHlstlsts. reflexivity.
       (* This concludes the proof in the first direction *)
  (* we must now prove the second direction *)
  - induction lstlsts.
  (* Case analysis on the list of lists giving us two cases *)
  (* in the first case where lstlsts is empty, it's impyling that 
       lst is In an empty list which is nonsensical by 
       the definition of In *)
    -- intros. inversion H.
    (* in the second case where the list of lists is not empty, we introduce 
       the premise, and then simplify both the premise and the goal into the cases where lst
       is in the head or lst is in the tail. *)
    -- intros. simpl in *. 
       (* we then destruct the conditional in the goal into its two cases and use auto
          to take care of the trivial case where lst is equal to the head *)
       destruct (same_list a lst) eqn:Heq; auto.
       (* Now in the case where samelist is false
          we then apply the inductive hypothesis *)
       apply IHlstlsts.
       (* we now split H into its two cases *)
       destruct H.
       (* in the first case we use our previous lemma same_list_eq
          which takes the computational equality in H and turns it
          into a boolean comparison contradicting Heq. *)
       --- rewrite <- same_list_eq in H.
           (* we can now rewrite H into Heq to prove to coq 
              that this case is nonsensical. This is because same_list 
              being false by the false case of our previous destruct
              of (same_list a lst) contradicts our premise that the head
              is equal to lst. therefore by same_list_eq the head being
              the same list as lst is true *)
           rewrite H in Heq.
           discriminate.
       (* in the second case the goal is the same as the premise
          in H and therefore is trivial. *)
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
(* Given a list l, all prefixes of list l will not contain empty *)
Proof.
induction l as [ | h t ].
(* two cases *)
  (* we do case analysis on the list l, in the first case where l is empty, by the Coq
     definition of In, an empty list of lists simplifies to false, and not false aka false
     implies false is true *)
- simpl. unfold not. auto.
  (* in the second case where the list of prefixes is not empty we have to break
     this down into further cases where we first unfold In into the head and tail. *)
- simpl. unfold not. intros. rewrite in_map_iff in H. inversion H.
    (* In the left case, a list of h is not equal to empty so this is nonsensical. *)
  * inversion H0. 
    (* In this case, in H0 its made the assumption that there is some list x such that
       h consed onto empty which is nonsensical by definition *)
  * inversion H0. destruct H1. inversion H1.
 Qed.


(* Hints:
   - Use in_or_app.
   - this one is really short
*)
Lemma nil_in_all_subseqs : forall l, In [] (all_subseqs l).
(* for a given list l of natural numbers, all subesequenes of l will contain a list of empty *)
Proof.
  (* two cases. in the first case, the list of natural numbers is assumed to be empty.
     this case is trivial as it simplifies to empty equals empty which is true *)
  induction l. simpl. auto.
  (* in the second case, we assume the list is not empty, so either the first item of the l
     is empty or emty is further down in the tail of the list. going right... *)
  simpl. right.
  Search (In _ (_ ++ _)).
  (* using the preexisting in_or_app coq theorem that states that if something is in a list
     appended to another list, then that thing is either in the first list or the second
     list, we prove this case by our inductive hypothesis. *)
  apply in_or_app. auto.
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
(* given two lists of natural numbers, first computing their individual subsequences before
   finding which subsequences they have in common, the list of said common subsequences will
   not be equal to empty *)
Proof.
  intros.
  (* based on our definitions of all_subseqs and common_subseq, an empty list will always be a
     an element of the computed list of lists of common_subseq which means the list computed
     from common_subseq can not itself be equal to empty  *)
  assert (In [] (common_subseq (all_subseqs lA) (all_subseqs lB))).
  (* relying on our previous lemma common_subseq_correct which proved that if in element is
     part of a computed list of common_subseq from list A and list B then the given elment must
     be in list A or list B, furthering splitting the proof for the assertion and applying
     the lemma that the empty list will always be in all subsequences of a list, we can
     prove the assertion *)
  apply common_subseq_correct. split; apply nil_in_all_subseqs.
  (* rewriting the premise in H, we derive a nonsensical assumption that empty is In empty
     which is false by the definition of In *)
  intros H1. rewrite H1 in H. inversion H.
  Qed.


(* Put it all together! *)
(* given lists lA, lB and lC, if lC is the longest common subsequence of lA and lB
   then lC is a subsequence of both lA and lB and is at least as long as any other 
   common subsequece of lA and lB. This can be proven utilizing all of the 
   previously proven lemmas *)
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



