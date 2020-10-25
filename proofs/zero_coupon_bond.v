Load metaproperties.

(* Zero coupon bond *)
Definition zcb_desc
           (NOW : nat)
           (PERIOD : nat) :=
  (And
     (Give (Scale 10 (One USD)))
     (At (NOW + PERIOD) (Scale 11 (One USD)))
  ).


(* The issuer's rights *)
Proposition zcb_O_to_I:
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    consistent_state s1 ->
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
  destruct_join H1.
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
