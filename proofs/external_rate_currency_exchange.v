Load metaproperties.

(* ECX : External currency exchange *)
Definition ecx_desc (addr : Address) (sc : nat) :=
  (And
     (Give (Scale sc (One EUR)))
     (ScaleObs addr (Scale sc (One USD)))
  ).

(* The issuer pays the owner *)
Lemma ecx_step_I_to_O:
  forall s1 s2 ctr_id dsc_id addr sc amount I O ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (ecx_desc addr amount) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists obs tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * obs * amount).
Proof.
  intros.
  induction H.
  - subst s2. simpl in H3. destruct H3 as [H3 | H3]; try inversion H3.
    apply consistent_impl_exec with (ctr := ctr) in H0; auto.
    subst ctr. contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    unfold exec_ctr_in_state_with_owner in H10.
    subst ctr0 ctr. simpl in H10.
    case_match H10. destruct r. inversion H14. clear H14. subst.
    case_eq (query (m_gateway s1) addr (m_global_time s1)); intros;
      rewrite H10 in H1; inversion H1.
    inversion H1. clear H1. simpl.
    eexists. eexists. split. left. trivial.
    simpl. repeat split; eauto.
    destruct H5 as [H5 | H5]; simpl; subst; simpl; trivial. contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0. rewrite H1 in H7. unfold ecx_desc in H7.
    simpl in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0. rewrite H1 in H7. unfold ecx_desc in H7.
    simpl in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 s2. simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    apply consistent_impl_exec with (ctr := ctr) in H0; auto.
    subst ctr. contradiction.
  - subst s2. simpl in *.
    apply consistent_impl_exec with (ctr := ctr) in H0; auto.
    subst ctr. contradiction.
Qed.


Lemma ecx_steps_I_to_O:
  forall s1 s2 ctr_id dsc_id addr sc amount I O ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (ecx_desc addr amount) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists obs tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * obs * amount).
Proof.
  intros.
  induction H.
  - subst. eapply consistent_impl_exec in H0; eauto.
    simpl in *. contradiction.
  - assert (H' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H | [H | H]]; trivial.
    + eapply ecx_step_I_to_O; eauto.
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



(* The owner pays the issuer *)
Lemma ecx_step_O_to_I:
  forall s1 s2 ctr_id dsc_id addr sc amount I O ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (ecx_desc addr amount) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * amount).
Proof.
  intros.
  induction H.
  - subst s2. simpl in H3. destruct H3 as [H3 | H3]; try inversion H3.
    apply consistent_impl_exec with (ctr := ctr) in H0; auto.
    subst ctr. contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    unfold exec_ctr_in_state_with_owner in H10.
    subst ctr0 ctr. simpl in H10.
    case_match H10. destruct r. inversion H14. clear H14. subst.
    case_eq (query (m_gateway s1) addr (m_global_time s1)); intros;
      rewrite H10 in H1; inversion H1.
    inversion H1. clear H1. simpl.
    eexists. split. right. left. trivial.
    simpl. repeat split; eauto.
    destruct H5 as [H5 | H5]; simpl; subst; simpl; trivial. contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0. rewrite H1 in H7. unfold ecx_desc in H7.
    simpl in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0. rewrite H1 in H7. unfold ecx_desc in H7.
    simpl in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 s2. simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    apply consistent_impl_exec with (ctr := ctr) in H0; auto.
    subst ctr. contradiction.
  - subst s2. simpl in *.
    apply consistent_impl_exec with (ctr := ctr) in H0; auto.
    subst ctr. contradiction.
Qed.


Lemma ecx_steps_O_to_I:
  forall s1 s2 ctr_id dsc_id addr sc amount I O ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (ecx_desc addr amount) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * amount).
Proof.
  intros.
  induction H.
  - subst. eapply consistent_impl_exec in H0; eauto.
    simpl in *. contradiction.
  - assert (H' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H | [H | H]]; trivial.
    + eapply ecx_step_O_to_I; eauto.
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