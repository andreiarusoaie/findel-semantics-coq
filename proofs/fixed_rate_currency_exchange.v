Load metaproperties.

(* Fixed rate currency exchange *)
Definition frce_desc :=
  (And
     (Give (Scale 11 (One USD)))
     (Scale 10 (One EUR))
  ).


Print Transaction.
Print execute.
Lemma frce_execute_I_to_O :
  forall sc I O bal time gtw ctr_id dsc_id next_id ledger result,
    execute frce_desc sc I O bal time gtw ctr_id dsc_id next_id ledger =
    Some result ->
    exists tr,
      In tr (res_ledger result) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 10 /\
      tr_timestamp tr = time.
Proof.
  intros.
  unfold frce_desc in H. simpl in H.
  inversion H. clear H.
  eexists. simpl.
  split.
  - left. trivial.
  - repeat split; simpl; trivial.
Qed.


Lemma frce_execute_O_to_I :
  forall sc I O bal time gtw ctr_id dsc_id next_id ledger result,
    execute frce_desc sc I O bal time gtw ctr_id dsc_id next_id ledger =
    Some result ->
    exists tr,
      In tr (res_ledger result) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 11 /\
      tr_timestamp tr = time.
Proof.
  intros.
  unfold frce_desc in H. simpl in H.
  inversion H. clear H.
  eexists. simpl.
  split.
  - right. left. trivial.
  - repeat split; simpl; trivial.
Qed.

Lemma frce_step_I_to_O:
  forall s1 s2 ctr ctr_id dsc_id I O sc,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id frce_desc I O O sc ->
    In ctr (m_contracts s1) ->
    ~ In (Executed ctr_id) (m_events s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 10 /\
      tr_timestamp tr = (m_global_time s1).
Proof.
  intros *.
  intros H.
  assert (H' := H).
  induction H; intros.
  - subst s2; simpl in *. destruct H9 as [H9 | H9]; try inversion H9; try contradiction.
  - apply step_executes_only_one_contract with
        (ctr := ctr) (ctr' := ctr0) in H'; auto.
    + subst s2. simpl.
      unfold can_join in H0.
      destruct H0 as [H0 | H0]; try contradiction.
      * subst owner ctr0.
        rewrite H8 in H5.
        unfold exec_ctr_in_state_with_owner in H5.
        simpl in H5.
        inversion H5.
        eexists. simpl.
        split.
        ** left. trivial.
        ** repeat split; trivial.
      * subst ctr0 ctr. simpl in H0. rewrite H0 in H12. contradiction.
    + subst ctr. simpl. trivial.
    + subst s2. simpl. left. trivial.
  - apply step_executes_only_one_contract with
        (ctr := ctr) (ctr' := ctr0) in H'; auto.
    + subst ctr ctr0. unfold frce_desc in H2. simpl in H2. inversion H2.
    + subst ctr. simpl. trivial.
    + subst s2. simpl. left. trivial.
  - apply step_executes_only_one_contract with
        (ctr := ctr) (ctr' := ctr0) in H'; auto.
    + subst ctr ctr0. unfold frce_desc in H2. simpl in H2. inversion H2.
    + subst ctr. simpl. trivial.
    + subst s2. simpl. left. trivial.
  - subst s2. simpl in *.
    destruct H9 as [H9 | H9]; try contradiction; try inversion H9.
  - subst s2. simpl in *. contradiction.
Qed.


Lemma frce_step_O_to_I:
  forall s1 s2 ctr ctr_id dsc_id I O sc,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id frce_desc I O O sc ->
    In ctr (m_contracts s1) ->
    ~ In (Executed ctr_id) (m_events s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 11 /\
      tr_timestamp tr = (m_global_time s1).
Proof.
  intros *.
  intros H.
  assert (H' := H).
  induction H; intros.
  - subst s2; simpl in *. destruct H9 as [H9 | H9]; try inversion H9; try contradiction.
  - apply step_executes_only_one_contract with
        (ctr := ctr) (ctr' := ctr0) in H'; auto.
    + subst s2. simpl.
      unfold can_join in H0.
      destruct H0 as [H0 | H0]; try contradiction.
      * subst owner ctr0.
        rewrite H8 in H5.
        unfold exec_ctr_in_state_with_owner in H5.
        simpl in H5.
        inversion H5.
        eexists. simpl.
        split.
        ** right. left. trivial.
        ** repeat split; trivial.
      * subst ctr0 ctr. simpl in H0. rewrite H0 in H12. contradiction.
    + subst ctr. simpl. trivial.
    + subst s2. simpl. left. trivial.
  - apply step_executes_only_one_contract with
        (ctr := ctr) (ctr' := ctr0) in H'; auto.
    + subst ctr ctr0. unfold frce_desc in H2. simpl in H2. inversion H2.
    + subst ctr. simpl. trivial.
    + subst s2. simpl. left. trivial.
  - apply step_executes_only_one_contract with
        (ctr := ctr) (ctr' := ctr0) in H'; auto.
    + subst ctr ctr0. unfold frce_desc in H2. simpl in H2. inversion H2.
    + subst ctr. simpl. trivial.
    + subst s2. simpl. left. trivial.
  - subst s2. simpl in *.
    destruct H9 as [H9 | H9]; try contradiction; try inversion H9.
  - subst s2. simpl in *. contradiction.
Qed.


Lemma frce_steps_I_to_O:
  forall s1 s2 ctr ctr_id dsc_id I O sc,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id frce_desc I O O sc ->
    In ctr (m_contracts s1) ->
    ~ In (Executed ctr_id) (m_events s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    exists time tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 10 /\
      tr_timestamp tr = time.
Proof.
  intros.
  induction H; intros.
  - subst. contradiction.
  - assert (H' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eexists.
      eapply frce_step_I_to_O; eauto.
      destruct H' as [H' [T P]].
      apply T in H.
      destruct H as [H _].
      subst ctr.
      simpl in *.
      trivial.
    + subst ctr.
      simpl in *.
      apply IHsteps in H.
      destruct H as [time [tr [S2 H]]].
      exists time, tr.
      split; trivial.
      eapply step_does_not_remove_transactions; eauto.
    + eapply step_does_not_remove_events in H; eauto.
      eapply step_preserves_consistent_state in H'; eauto.
      destruct H' as [H' [T P]].
      subst ctr. simpl in *.
      contradiction P with (e := ctr_id0).
      split; trivial.
Qed.


Lemma frce_steps_O_to_I:
  forall s1 s2 ctr ctr_id dsc_id O I sc,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id frce_desc I O O sc ->
    In ctr (m_contracts s1) ->
    ~ In (Executed ctr_id) (m_events s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    exists time tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 11 /\
      tr_timestamp tr = time.
Proof.
  intros.
  induction H; intros.
  - subst. contradiction.
  - assert (H' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eexists.
      eapply frce_step_O_to_I; eauto.
      destruct H' as [H' [T P]].
      apply T in H.
      destruct H as [H _].
      subst ctr.
      simpl in *.
      trivial.
    + subst ctr.
      simpl in *.
      apply IHsteps in H.
      destruct H as [time [tr [S2 H]]].
      exists time, tr.
      split; trivial.
      eapply step_does_not_remove_transactions; eauto.
    + eapply step_does_not_remove_events in H; eauto.
      eapply step_preserves_consistent_state in H'; eauto.
      destruct H' as [H' [T P]].
      subst ctr. simpl in *.
      contradiction P with (e := ctr_id0).
      split; trivial.
Qed.
