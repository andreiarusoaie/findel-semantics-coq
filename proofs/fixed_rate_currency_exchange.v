Load metaproperties.

(* fixed rate currency exchange *)
Definition frce_desc :=
  (And
     (Give (Scale 11 (One USD)))
     (Scale 10 (One EUR))
  ).


(* The owner's rights *)
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
      tr_currency tr = EUR.
Proof.
  intros. unfold frce_desc in H. simp_inv_clear H.
  eexists. simpl.
  split.
  - left. trivial.
  - repeat split; simpl; trivial.
Qed.


Lemma frce_step_I_to_O:
  forall s1 s2 ctr ctr_id dsc_id I O sc,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id frce_desc I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 10 /\
      tr_currency tr = EUR.
Proof.
  intros.
  induction H.
  - subst s2; simpl in *. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - ctr_case_analysis ctr ctr0.
    subst ctr s2. simpl in *.
    destruct H3 as [H3 | H3]; try contradiction.
    unfold exec_ctr_in_state_with_owner in H10.
    simpl in H10. inversion H10. subst.
    eexists. split.
    + simpl. left. trivial.
    + repeat split; trivial.
      resolve_owner H5.
  - ctr_case_analysis ctr ctr0.
    subst ctr. unfold frce_desc in H7. simp_inv_clear H7. 
  - ctr_case_analysis ctr ctr0.
    subst ctr. unfold frce_desc in H7. simp_inv_clear H7. 
  - ctr_case_analysis ctr ctr0.
    subst ctr s2. simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - subst s2. simpl in *. find_contradiction H2.
Qed.

(* If the owner joins, then the owner receives sc * n * 10 EUR from the issuer *)
Proposition frce_steps_I_to_O:
  forall s1 s2 ctr ctr_id dsc_id I O sc,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id frce_desc I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 10 /\
      tr_currency tr = EUR.
Proof.
  intros.
  induction H.
  - subst. find_contradiction H2.
  - assert (H' := H). assert (H'' := H).
    eapply steps_preserves_consistent_state in H'; eauto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eapply frce_step_I_to_O; eauto.
    + subst ctr. simpl in *.
      apply IHsteps in H.
      destruct H as [tr [S2 H]].
      exists tr. split; trivial.
      eapply step_does_not_remove_transactions; eauto.
    + eapply step_does_not_remove_events in H; eauto.
      eapply step_preserves_consistent_state in H'; eauto.
      destruct H' as [_ [_ [H' [T P]]]].
      subst ctr. simpl in *.
      contradiction P with (e := ctr_id0).
      split; trivial.
Qed.

Print frce_steps_I_to_O.


(* The issuer's rights *)
(* The owner's rights *)
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
      tr_currency tr = USD.
Proof.
  intros. unfold frce_desc in H. simp_inv_clear H.
  eexists. simpl.
  split.
  - right. left. trivial.
  - repeat split; simpl; trivial.
Qed.


Lemma frce_step_O_to_I:
  forall s1 s2 ctr ctr_id dsc_id I O sc,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id frce_desc I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 11 /\
      tr_currency tr = USD.
Proof.
  intros.
  induction H.
  - subst s2; simpl in *. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - ctr_case_analysis ctr ctr0.
    subst ctr s2. simpl in *.
    destruct H3 as [H3 | H3]; try contradiction.
    unfold exec_ctr_in_state_with_owner in H10.
    simpl in H10. inversion H10. subst.
    eexists. split.
    + simpl. right. left. trivial.
    + repeat split; trivial.
      resolve_owner H5.
  - ctr_case_analysis ctr ctr0.
    subst ctr. unfold frce_desc in H7. simp_inv_clear H7.
  - ctr_case_analysis ctr ctr0.
    subst ctr. unfold frce_desc in H7. simp_inv_clear H7.
  - ctr_case_analysis ctr ctr0.
    subst ctr s2. simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - subst s2. simpl in *. find_contradiction H2.
Qed.

(* If the owner joins, then the issuer receives sc * n * 11 USD from the owner *)
Proposition frce_steps_O_to_I:
  forall s1 s2 ctr ctr_id dsc_id I O sc,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id frce_desc I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 11 /\
      tr_currency tr = USD.
Proof.
  intros.
  induction H.
  - subst. find_contradiction H2.
  - assert (H' := H). assert (H'' := H).
    eapply steps_preserves_consistent_state in H'; eauto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eapply frce_step_O_to_I; eauto.
    + subst ctr. simpl in *.
      apply IHsteps in H.
      destruct H as [tr [S2 H]].
      exists tr. split; trivial.
      eapply step_does_not_remove_transactions; eauto.
    + eapply step_does_not_remove_events in H; eauto.
      eapply step_preserves_consistent_state in H'; eauto.
      destruct H' as [_ [_ [H' [T P]]]].
      subst ctr. simpl in *.
      contradiction P with (e := ctr_id0).
      split; trivial.
Qed.

Print frce_steps_O_to_I.
