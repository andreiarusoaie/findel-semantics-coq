Load findel.

(* Zero coupon bond *)
Definition zcb_desc
           (NOW : nat)
           (PERIOD : nat) :=
  (And
     (Give (Scale 10 (One USD)))
     (At (NOW + PERIOD) (Scale 11 (One USD)))
  ).

Definition executed
           (ctr : FinContract)
           (s s' : State)
           (at_ : Time) :=
    step s s' /\
    In ctr (m_contracts s) /\
    In (Executed ctr) (m_events s') /\
    at_ = m_global_time s.

Definition deleted
           (ctr : FinContract)
           (s s' : State)
           (at_ : Time) :=
    step s s' /\
    In ctr (m_contracts s) /\
    In (Deleted ctr) (m_events s') /\
    at_ = m_global_time s.

Definition joins
           (O : Address)
           (ctr : FinContract)
           (s1 s2 : State)
           (at_ : Time) :=
   exists s s', (s1 ~~> s) /\ (s' ~~> s2) /\ (executed ctr s s' at_ \/ deleted ctr s s' at_).

Ltac destruct_executed H :=
  let S := fresh "St" in
  let M := fresh "M" in
  let Ev := fresh "Ev" in
  let T := fresh "T" in
  destruct H as [S [M [Ev T]]].

Ltac destruct_deleted := destruct_executed.

Ltac destruct_join H :=
  let s := fresh "s" in
  let s' := fresh "s'" in
  let Ss1 := fresh "Ss" in
  let Ss2 := fresh "Ss" in
  let E := fresh "E" in
  let D := fresh "D" in
  destruct H as [s [s' [Ss1 [Ss2 [E | D]]]]]; try destruct_executed E; try destruct_deleted D.

Definition consistent' (s : State) :=
    (forall ctr, In ctr (m_contracts s) -> ~ In (Executed ctr) (m_events s)) /\
    (forall ctr, In ctr (m_contracts s) -> ~ In (Deleted ctr) (m_events s)) /\
    (forall ctr, In (Executed ctr) (m_events s) -> ~ In (Deleted ctr) (m_events s)) /\
    (forall ctr, In (Deleted ctr) (m_events s) -> ~ In (Executed ctr) (m_events s)) /\
    next_id_is_fresh s.
Print State.

Lemma new_contract_is_fresh :
  forall ctr s,
    ctr_id ctr = m_fresh_id s ->
    next_id_is_fresh s ->
    ~ In ctr (m_contracts s).
Proof.
  intros ctr s H [H1 [H2 [H3 H4]]].
  unfold not. intros C.
  apply H1 in C.
  contradiction.
Qed.

Lemma new_contracts_are_not_executed :
  forall ctr s,
    ctr_id ctr = m_fresh_id s ->
    next_id_is_fresh s ->
    ~ In (Executed ctr) (m_events s).
Proof.
  intros ctr s H [H1 [H2 [H3 H4]]].
  unfold not. intros C.
  apply H2 in C.
  contradiction.
Qed.
    
Lemma new_contracts_are_not_deleted :
  forall ctr s,
    ctr_id ctr = m_fresh_id s ->
    next_id_is_fresh s ->
    ~ In (Deleted ctr) (m_events s).
Proof.
  intros ctr s H [H1 [H2 [H3 H4]]].
  unfold not. intros C.
  apply H3 in C.
  contradiction.
Qed.

Ltac unfold_append :=
  unfold not; intros CL;
  unfold append_new_ctr_to_state in *; simpl in *;
  destruct CL as [CL | CL].
Ltac resolve_append :=
  unfold_append; try inversion CL.  

Lemma rm_in:
  forall cs c, In c (rm c cs) -> False.
Proof.
  induction cs; intros; simpl in *; try contradiction.
  case_eq (FinContract_eq_dec c a); intros H0 H'; rewrite H' in H.
  + eapply IHcs. eauto.
  + simpl in H. destruct H as [H | H]. subst. contradiction.
    eapply IHcs. eauto.
Qed.

Lemma incl_rm : forall S x y, x <> y -> In x (rm y S) -> In x S.
Proof.
  induction S.
  - simpl. intros. trivial.
  - intros.
    simpl in H0.
    case_eq (FinContract_eq_dec y a); intros He H'; rewrite H' in H0. subst.
    + simpl. right. eapply IHS; eauto.
    + simpl in H0. destruct H0 as [H0 | H0]; subst.
      * simpl. left. reflexivity.
      * simpl. right. eapply IHS; eauto.
Qed.

Lemma new_contracts_are_fresh :
  forall ctr s owner bal' ctrs' next' ledger',
    consistent' s ->
    next_id_is_fresh s ->
    exec_ctr_in_state_with_owner ctr s owner = Some (result bal' ctrs' next' ledger') ->
    ~ In ctr ctrs'.
Proof.
  intros ctr.
  destruct ctr.
  induction ctr_primitive0; intros s owner bal' ctrs' next' ledger' C F E; unfold exec_ctr_in_state_with_owner in E; simpl in E.
  - try inversion E; clear E. subst. auto.
  - try inversion E; clear E. subst. auto.
  -     
    
  unfold not. intros CTR.
  destruct ctr.
  unfold exec_ctr_in_state_with_owner in E.
  induction ctr_primitive0; simpl in E.
  - try inversion E; clear E; try subst ctrs'; trivial.
  - try inversion E; clear E; try subst ctrs'; trivial.
  - simpl in *.apply IHctr_primitive0.
  - simpl in *. apply IHctr_primitive0 in CTR. ; eauto.
  - 
  

Lemma consistent_step_1 : forall  (s s' : State),
  step s s' ->
  consistent' s ->
  (forall ctr, In ctr (m_contracts s') -> ~ In (Executed ctr) (m_events s')).
Proof.
  intros s s' H (C1 & _).
  destruct H; subst s'.
  - unfold not. intros. simpl in H4, H5.
    destruct H5 as [H5 | H5]; try inversion H5.
    + destruct H4 as [H4 | H4].
      * subst ctr.
        apply new_contracts_are_not_executed with (ctr := new_contract) in H5; try contradiction; subst; trivial.
      * apply C1 in H4. contradiction.
  - unfold not. intros. simpl in *.
    rewrite in_app_iff in H6. 
    destruct H6 as [H6 | H6].
    case_eq (FinContract_eq_dec ctr ctr0); intros.
    + subst ctr0.
      destruct H7 as [H7 | H7]; try eapply rm_in; eauto.
    + destruct H7 as [H7 | H7]. 
      * inversion H7. try contradiction.
      * apply incl_rm in H6; auto. apply C1 in H6. contradiction.
    + destruct H7 as [H7 | H7].
      * inversion H7. subst.



        
        apply 
      
      * inversion H7. clear H7. subst ctr0.
        eapply rm_in; eauto.
      * unfold not in C1. apply C1 with (ctr := ctr0).
        case_eq (FinContract_eq_dec ctr ctr0); intros.

          

          

      try inversion H6.
    + destruct H4 as [H4 | H4].
      * subst ctr.
        apply new_contracts_are_not_executed with (ctr := new_contract) in H5; try contradiction; subst; trivial.
      * apply C1 in H4. contradiction.
  -
    
    intros FG.
  - simpl in H', FG.
    destruct H' as [H' | H'].
    + subst ctr'.
      apply new_contracts_are_not_executed with (ctr := new_contract) in H3.
      contradiction. subst. trivial.
    + resolve_append.
      
    unfold_append.
    

  apply C1; trivial.
Qed.    

Lemma consistent_step_2 : forall  (s s' : State),
  step s s' ->
  consistent' s ->
  (forall ctr, In ctr (m_contracts s) -> ~ In (Deleted ctr) (m_events s)).
Proof.
  intros s s' H (_ & C2 & _).
  destruct H; subst s'; intros ctr' H'; apply C2; trivial.
Qed.

Lemma consistent_step_3 : forall  (s s' : State),
  step s s' ->
  consistent' s ->
  (forall ctr, In (Executed ctr) (m_events s) -> ~ In (Deleted ctr) (m_events s)).
Proof.
  intros s s' H (C1 & C2 & C3 & C4 & F).
  destruct H; subst s'; intros ctr' H'; apply C3; trivial.
Qed.

Lemma consistent_step_4 : forall  (s s' : State),
  step s s' ->
  consistent' s ->
  (forall ctr, In (Deleted ctr) (m_events s) -> ~ In (Executed ctr) (m_events s)).
Proof.
  intros s s' H (C1 & C2 & C3 & C4 & F).
  destruct H; subst s'; intros ctr' H'; apply C4; trivial.
Qed.

Lemma consistent_step_5 : forall  (s s' : State),
  step s s' ->
  consistent' s ->
  next_id_is_fresh s'.
  

    simpl in H'. destruct H' as [H' | H'].
      * unfold_append. subst ctr. inversion CL.
        apply new_contracts_are_not_executed with (ctr := ctr) in F.
        contradiction. subst; auto.
      * resolve_append. apply C1 in H'. contradiction.
    + intros ctr H'. simpl in H'. destruct H' as [H' | H'].
      * unfold_append. subst ctr. inversion CL.
        apply new_contracts_are_not_deleted with (ctr := ctr) in F.
        contradiction. subst; auto.
      * resolve_append. apply C2 in H'. contradiction.
    + intros ctr H'. simpl in H'. destruct H' as [H' | H'].
      * inversion H'.
      * unfold_append. inversion CL.
        apply C3 in H'. contradiction.
    + intros ctr H'. simpl in H'. destruct H' as [H' | H'].
      * inversion H'.
      * unfold_append. inversion CL.
        apply C4 in H'. contradiction.
  
  
Lemma consistent_step : forall  (s s' : State),
  step s s' ->
  consistent' s ->
  consistent' s'.
Proof.
  intros s s' H (C1 & C2 & C3 & C4 & F).
  destruct H; subst s'.
  - repeat split.
    + intros ctr H'. simpl in H'. destruct H' as [H' | H'].
      * unfold_append. subst ctr. inversion CL.
        apply new_contracts_are_not_executed with (ctr := ctr) in F.
        contradiction. subst; auto.
      * resolve_append. apply C1 in H'. contradiction.
    + intros ctr H'. simpl in H'. destruct H' as [H' | H'].
      * unfold_append. subst ctr. inversion CL.
        apply new_contracts_are_not_deleted with (ctr := ctr) in F.
        contradiction. subst; auto.
      * resolve_append. apply C2 in H'. contradiction.
    + intros ctr H'. simpl in H'. destruct H' as [H' | H'].
      * inversion H'.
      * unfold_append. inversion CL.
        apply C3 in H'. contradiction.
    + intros ctr H'. simpl in H'. destruct H' as [H' | H'].
      * inversion H'.
      * unfold_append. inversion CL.
        apply C4 in H'. contradiction.
    + 
        unfold_append. subst ctr. inversion CL.
        apply new_contracts_are_not_deleted with (ctr := ctr) in F.
        contradiction. subst; auto.
      * resolve_append. apply C2 in H'. contradiction.

    +    
Admitted.

Lemma consistent_steps : forall  (s s' : State),
  steps s s' ->
  consistent' s ->
  consistent' s'.
Admitted.

Ltac insert_consistent' s H :=
  let H' := fresh "H" in
  match goal with
  | H : steps _ s |- _ => 
    assert (H' : consistent' s);
    try eapply consistent_steps; eauto
  | H : step _ s |- _ =>
    assert (H' : consistent' s);
    try eapply consistent_step;eauto
  end.

(* The issuer's rights *)
Proposition zcb_O_to_I:
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    consistent' s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    joins O ctr s1 s2 now ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 10.
Proof.
  intros.
  destruct_join H1;
  insert_consistent' s Ss;
  insert_consistent' s' St;
  insert_consistent' s2 St.
  - induction St; subst s'; simpl in Ev.
    + destruct Ev as [Ev | Ev].
      inversion Ev.
      unfold consistent' in H1.
      destruct H1 as (C & _ & _ & _ & _ & _).
      apply C in M. contradiction.
    + destruct Ev as [Ev | Ev].
      * admit.
      * destruct H1 as (C & _ & _ & _ & _ & _).
        apply C in M. contradiction.
    + destruct Ev as [Ev | Ev].
      * admit.
      * destruct H1 as (C & _ & _ & _ & _ & _).
        apply C in M. contradiction.
    + destruct Ev as [Ev | Ev].
      * admit.
      * destruct H1 as (C & _ & _ & _ & _ & _).
        apply C in M. contradiction.
    + destruct Ev as [Ev | Ev].
      * admit.
      * destruct H1 as (C & _ & _ & _ & _ & _).
        apply C in M. contradiction.
    + destruct H1 as (C & _ & _ & _ & _ & _).
      apply C in M. contradiction.
  - induction St; subst s'; simpl in Ev.
    + destruct Ev as [Ev | Ev]. inversion Ev.
      destruct H1 as (_ & C & _ & _ & _ & _).
      apply C in M. contradiction.
    + destruct Ev as [Ev | Ev].
      * inversion Ev.
      * destruct H1 as (_ & C & _ & _ & _ & _).
        apply C in M. contradiction.
    + destruct Ev as [Ev | Ev].
      * inversion Ev.
      * destruct H1 as (_ & C & _ & _ & _ & _).
        apply C in M. contradiction.
    + destruct Ev as [Ev | Ev].
      * inversion Ev.
      * destruct H1 as (_ & C & _ & _ & _ & _).
        apply C in M. contradiction.
    + destruct Ev as [Ev | Ev].
      * inversion Ev. admit.
      * destruct H1 as (_ & C & _ & _ & _ & _).
        apply C in M. contradiction.
    + destruct H1 as (_ & C & _ & _ & _ & _).
      apply C in M. contradiction.
Qed.
        
    
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H9.
      case_analysis H9.
      case_analysis H12.
      * eexists. split.
        ** eapply steps_does_not_remove_transactions; eauto.
           simpl. subst ledger'. right. left. eauto.
        ** repeat split; trivial. resolve_owner H4.
      * eexists. split.
        ** eapply steps_does_not_remove_transactions; eauto.
           simpl. subst ledger'. left. eauto.
        ** repeat split; trivial. resolve_owner H4.
    + not_or ctr ctr0 H6.
    + not_or ctr ctr0 H6.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + ctr_case_analysis ctr ctr0.
      inversion_event Ev. find_contradiction_del M.
    + not_or ctr ctr0 H6.
    + not_or ctr ctr0 H6.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H7.
      case_analysis H7; simpl in *; rewrite <- T in *.
      * eapply ltb_sound_true in H0. contradict H0. omega.
      * case_analysis H10.
    + find_contradiction_del M.
Qed.

Print zcb_O_to_I.


(* The owner's rights - see Proposition after this lemma *)

(* helper lemma for the inner contract *) 
Lemma inner_ctr_proof:
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (At (now + period) (Scale 11 (One USD))) I O O sc ->
    joins O ctr s1 s2 (now + period) ->
    O <> 0 ->
    period > Δ ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.
  intros.
  destruct_join H1.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H10.
      case_if H10.
      case_if H14.
      * eexists. split.
        ** eapply steps_does_not_remove_transactions; eauto.
           subst ledger'. simpl. left. eauto.
      ** repeat split; trivial. resolve_owner H5.
      * eapply leb_sound_false in H10. contradict H10. rewrite <- T. unfold Δ. omega.
    + not_or ctr ctr0 H7.
    + not_or ctr ctr0 H7.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + ctr_case_analysis ctr ctr0.
       inversion_event Ev. find_contradiction_del M.
    + not_or ctr ctr0 H7.
    + not_or ctr ctr0 H7.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H8.
      case_if H8; simpl in *.
      * rewrite <- T in H0. apply ltb_sound_true in H0. contradict H0. omega.
      * case_if H11.
    + find_contradiction_del M.
Qed.

Proposition zcb_I_to_O:
  forall s1 s2 ctr_id gen_ctr dsc_id now period I O sc ctr,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    joins_generated O ctr gen_ctr s1 s2 now (now + period) ->
    O <> 0 ->
    period > Δ ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.
  intros.
  destruct_join_gen H1.
  - insert_consistent s Ss.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0.
      simpl in Ev. inversion_event Ev.
      execute_own ctr H11.
      case_analysis H11.
      case_analysis H15.
      * eexists. split.
        eapply steps_does_not_remove_transactions. exact Ss0.
        subst ledger'. simpl. left. eauto.
        repeat split; trivial.
        simpl. resolve_owner H6.
      * destruct_join J.
        ** simpl in Exec.
           rewrite H0, H11 in Exec.
           inversion Exec. clear Exec. subst res.
           simpl in M0. destruct M0 as [M0 | M0]; try contradiction.
           eapply inner_ctr_proof; eauto.
           unfold joins. exists s0, s'. unfold At.
           repeat split; simpl in *; auto.
           left. unfold executed. repeat split; trivial;
           simpl; subst gen_ctr; try exact M1; simpl; auto.
        ** simpl in Exec.
           rewrite H0, H11 in Exec.
           inversion Exec. clear Exec. subst res.
           simpl in M0. destruct M0 as [M0 | M0]; try contradiction.
           eapply inner_ctr_proof; eauto.
           unfold joins. exists s0, s'. unfold At.
           repeat split; simpl in *; auto.
           right. unfold executed. repeat split; trivial;
           simpl; subst gen_ctr; try exact M1; simpl; auto.
    + not_or ctr ctr0 H8.
    + not_or ctr ctr0 H8.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - destruct_deleted D.
    insert_consistent s Ss.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M0.
    + inversion_event Ev. find_contradiction_del M0.
    + not_or ctr ctr0 H8.
    + not_or ctr ctr0 H8.
    + ctr_case_analysis ctr ctr0.
      inversion_event Ev.
      * execute_own ctr H9.
        case_analysis H9.
        ** simpl in *. rewrite H0 in Exec. inversion Exec.
        ** case_analysis H12.
      * find_contradiction_del M0.
    + find_contradiction_del M0.
Qed.

Print zcb_I_to_O.


(* Fact: if the owner does not join the contract in time, the contract is deleted *)
(* Lemma: joining an expired contract triggers Delete *)
Lemma O_joins_generated_too_late_inner:
  forall s1 s2 c_id dsc_id now period I O sc ctr T,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (At (now + period) (Scale 11 (One USD))) I O O sc ->
    joins O ctr s1 s2 T ->
    T > now + period + Δ ->
    period > Δ ->
    O <> 0 ->
    In (Deleted (ctr_id ctr)) (m_events s2).
Proof.
  intros.
  destruct_join H1.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H11.
      simpl in *.
      case_if H11.
      case_if H14; rewrite T0 in *; apply ltb_sound_false in H0; contradict H0; omega.
    + not_or ctr ctr0 H8.
    + not_or ctr ctr0 H8.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - eapply steps_does_not_remove_events; eauto.
Qed.


Proposition O_joins_generated_too_late:
  forall s1 s2 c_id gen_ctr dsc_id now period I O sc ctr T,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (zcb_desc now period) I O O sc ->
    joins_generated O ctr gen_ctr s1 s2 now T ->
    T > now + period + Δ ->
    period > Δ ->
    O <> 0 ->
    In (Deleted (ctr_id gen_ctr)) (m_events s2).
Proof.
  intros.
  destruct_join_gen H1.
  - insert_consistent s Ss.
    insert_consistent s' Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H12.
      case_analysis H12.
      case_analysis H15.
      * rewrite <- T0 in *.
        apply leb_sound_true in H12.
        apply ltb_sound_false in H0.
        contradict H0. unfold Δ. omega.
      * simpl in *. 
        rewrite H0, H12 in Exec.
        inversion Exec. subst res.
        simpl in M0, J. destruct M0 as [M0 | M0]; try contradiction.
        eapply O_joins_generated_too_late_inner; eauto.
    + not_or ctr ctr0 H9.
    + not_or ctr ctr0 H9.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - destruct_deleted D.
    insert_consistent s Ss.
    insert_consistent s' Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + not_or ctr ctr0 H9.
    + not_or ctr ctr0 H9.
    + ctr_case_analysis ctr ctr0.
      inversion_event Ev.
      * execute_own ctr H10.
        case_analysis H10.
        ** simpl in *. rewrite H0 in Exec. inversion Exec.
        ** case_analysis H13.
      * find_contradiction_del M0.
    + find_contradiction_del M0.
Qed.

Print O_joins_generated_too_late.
