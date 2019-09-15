Load metaproperties.

(* ERCE : External rate currency exchange *)
Definition erce_desc (addr : Address) :=
  (And
     (Give (One EUR))
     (ScaleObs addr (One USD))
  ).

(* The owner's rights *)
Lemma erce_step_I_to_O:
  forall s1 s2 ctr_id dsc_id addr I O ctr sc,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (erce_desc addr) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists obs tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * obs /\
      tr_currency tr = USD).
Proof.
  intros.
  induction H.
  - subst s2.
    simpl in H3. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H0.
  - ctr_case_analysis ctr ctr0.
    unfold exec_ctr_in_state_with_owner in H10.
    subst ctr. simpl in H10.
    case_match H10. destruct r. inversion H14. clear H14. subst.
    case_eq (query (m_gateway s1) addr (m_global_time s1)); intros;
      rewrite H10 in H1; inversion H1.
    inversion H1. clear H1. simpl.
    eexists. eexists.
    split. left. eauto.
    simpl. repeat split; eauto.
    resolve_owner H5.
  - ctr_case_analysis ctr ctr0. rewrite H1 in H7.
    unfold erce_desc in H7. simpl in H7. inversion H7.
  - ctr_case_analysis ctr ctr0. rewrite H1 in H7.
    unfold erce_desc in H7. simpl in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 s2. simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H0.
  - subst s2. simpl in *. find_contradiction H0.
Qed.

(* If the owner joins, then the owner receives obs * sc USD from the owner *)
Theorem erce_steps_I_to_O:
  forall s1 s2 ctr_id dsc_id addr sc I O ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (erce_desc addr) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists obs tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * obs /\
      tr_currency tr = USD).
Proof.
  intros.
  induction H.
  - subst. find_contradiction H0.
  - assert (H' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H | [H | H]]; trivial.
    + eapply erce_step_I_to_O; eauto.
    + subst ctr. simpl in *. eapply IHsteps in H.
      destruct H as [obs [tr [H H'']]].
      exists obs, tr. split; trivial.
      eapply step_does_not_remove_transactions; eauto.
    + eapply step_preserves_consistent_state in H'; eauto.
      destruct H' as [_ [_ [_ [_ H']]]].
      exfalso. eapply H'. subst ctr. simpl in *.
      split; eauto.
      eapply step_does_not_remove_events; eauto.
Qed.

Print erce_steps_I_to_O.


(* The issuer's rights *)
Lemma erce_step_O_to_I:
  forall s1 s2 ctr_id dsc_id addr sc I O ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (erce_desc addr) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc /\
      tr_currency tr = EUR).
Proof.
  intros.
  induction H.
  - subst s2. simpl in H3. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H0.
  - ctr_case_analysis ctr ctr0.
    unfold exec_ctr_in_state_with_owner in H10.
    subst ctr. simpl in H10.
    case_match H10. destruct r. inversion H14. clear H14. subst.
    case_eq (query (m_gateway s1) addr (m_global_time s1)); intros;
      rewrite H10 in H1; inversion H1.
    inversion H1. clear H1. simpl.
    eexists. split. right. left. trivial.
    simpl. repeat split; eauto.
    resolve_owner H5.
  - ctr_case_analysis ctr ctr0. rewrite H1 in H7.
    unfold erce_desc in H7. simpl in H7. inversion H7.
  - ctr_case_analysis ctr ctr0. rewrite H1 in H7.
    unfold erce_desc in H7. simpl in H7. inversion H7.
  - ctr_case_analysis ctr ctr0.
    subst s2. simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H0.
  - subst s2. simpl in *. find_contradiction H0.
Qed.


Theorem erce_steps_O_to_I:
  forall s1 s2 ctr_id dsc_id addr sc I O ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (erce_desc addr) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc /\
      tr_currency tr = EUR).
Proof.
  intros.
  induction H.
  - subst. find_contradiction H0.
  - assert (H' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H | [H | H]]; trivial.
    + eapply erce_step_O_to_I; eauto.
    + subst ctr. simpl in *. eapply IHsteps in H.
      destruct H as [tr [H H'']].
      exists tr. split; trivial.
      eapply step_does_not_remove_transactions; eauto.
    + eapply step_preserves_consistent_state in H'; eauto.
      destruct H' as [_ [_ [_ [_ H']]]].
      exfalso. eapply H'. subst ctr. simpl in *.
      split; eauto.
      eapply step_does_not_remove_events; eauto.
Qed.

Print erce_steps_O_to_I.


(* Invalid gateway! *)

(* Invalid gateway implies no changes in the ledger! *)
Theorem erce_invalid_gateway:
  forall s1 s2 ctr_id dsc_id addr sc I O ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (erce_desc addr) I O O sc ->
    In ctr (m_contracts s1) ->
    O <> 0 ->
    query (m_gateway s1) addr (m_global_time s1) = None ->
    (m_ledger s1) = (m_ledger s2).
Proof.
  intros.
  induction H; try subst s2; trivial; simpl in *.
  - ctr_case_analysis ctr ctr0.
    unfold exec_ctr_in_state_with_owner, erce_desc in H10.
    rewrite H1 in H10. simpl in H10.
    case_match H10. destruct r.
    case_match H12. rewrite H4 in H10. inversion H10.
  - ctr_case_analysis ctr ctr0. rewrite H1 in H7.
    unfold erce_desc in H7. simpl in H7. inversion H7.
  - ctr_case_analysis ctr ctr0. rewrite H1 in H7.
    unfold erce_desc in H7. simpl in H7. inversion H7.
Qed.

Print erce_invalid_gateway.

(* If contract gets deleted, then the ledger remains the same. *)
Lemma erce_invalid_gtw_step:
  forall s1 s2 ctr_id dsc_id addr sc I O ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (erce_desc addr) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Deleted ctr_id) (m_events s2) ->
    O <> 0 ->
    (m_ledger s1) = (m_ledger s2).
Proof.
  intros.
  induction H.
  - subst s2. simpl in H3. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H0.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 s2. simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    destruct H0 as [_ [_ [_ [H0 _]]]].
    apply H0 in H2. destruct H2 as [_ H2].
    subst ctr. simpl in *. try contradiction.
  - ctr_case_analysis ctr ctr0. rewrite H1 in H7.
    unfold erce_desc in H7. simpl in H7. inversion H7.
  - ctr_case_analysis ctr ctr0. rewrite H1 in H7.
    unfold erce_desc in H7. simpl in H7. inversion H7.
  - ctr_case_analysis ctr ctr0. subst s2. simpl. trivial.
  - subst s2. simpl in *. find_contradiction H0.
Qed.
