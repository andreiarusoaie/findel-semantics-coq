Load helpers.

Definition currency_exchange_desc :=
  (And
     (Give (Scale 23 (One USD)))
     (Scale 20 (One EUR))
  ).


Definition exchange_ctr
           (alice bob : Address)
           (ctr_id dsc_id : Id) :=
  finctr ctr_id
         dsc_id
         currency_exchange_desc
         alice
         bob
         bob
         1.

Ltac exec_exchange H :=
  match type of H with
  | exec_ctr_in_state_with_owner (exchange_ctr _ _ _ _) _ _ = Some _ =>
    unfold exchange_ctr, currency_exchange_desc, exec_ctr_in_state_with_owner in H; simpl in H; inversion H; clear H
  end.


Lemma exchange_alice_gets_paid_by_bob :
  forall s1 alice bob ctr_id dsc_id result,
    exec_ctr_in_state_with_owner
      (exchange_ctr alice bob ctr_id dsc_id) s1 bob =
    Some result ->
    exists tr, # tr ∈ (res_ledger result) | ctr_id | bob --> alice | 23 $ USD #.
Proof.
  intros. exec_exchange H. subst result0.
  simpl. eexists.
  split.
  - right. left. trivial.
  - repeat split; trivial.
Qed.


Lemma exchange_alice_gets_paid_by_bob_step :
  forall s1 s2 alice bob ctr_id dsc_id,
    In (exchange_ctr alice bob ctr_id dsc_id)  (m_contracts s1) ->
    s1 → s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result tr,
      # tr ∈ (res_ledger result) | ctr_id | bob --> alice | 23 $ USD #.
Proof.
  intros until 1.
  step_intro.
  assert (H' := H0); auto.
  induction H0; intros; set (EX := (exchange_ctr alice bob ctr_id0 dsc_id0)).
  - unfold append_new_ctr_to_state in H8. subst s2. contradict_hyp H3.
  - same_ctr ctr EX s2.
    same_owner owner (ctr_owner EX) ctr EX.
    subst ctr EX. subst owner. simpl in H9.
    exists (result balance' ctrs' next' ledger').
    eapply exchange_alice_gets_paid_by_bob.
    exact H9.
  - same_ctr ctr EX s2. subst ctr EX.
    unfold exchange_ctr, currency_exchange_desc, ctr_primitive in H6. inversion H6.
  - same_ctr ctr EX s2. subst ctr EX.
    unfold exchange_ctr, currency_exchange_desc, ctr_primitive in H6. inversion H6.
  - subst s2. contradict_hyp H3.
  - subst s2. simpl in H3. contradiction.
Qed.


Theorem exchange_alice_gets_paid_by_bob_steps :
  forall s1 s2 alice bob ctr_id dsc_id,
    In (exchange_ctr alice bob ctr_id dsc_id)  (m_contracts s1) ->
    s1 ⇓ s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result tr,
      # tr ∈ (res_ledger result) | ctr_id | bob --> alice | 23 $ USD #.
Proof.
  intros.
  assert (H' := H); auto.
  eapply exists_step_in_steps in H'; eauto.
  destruct H' as [s [s' [H3' [H5' [H6' H7']]]]].
  eapply exchange_alice_gets_paid_by_bob_step; eauto.
Qed.


Lemma exchange_bob_gets_paid_by_alice :
  forall s1 alice bob ctr_id dsc_id result,
    exec_ctr_in_state_with_owner
      (exchange_ctr alice bob ctr_id dsc_id) s1 bob =
    Some result ->
    exists tr, # tr ∈ (res_ledger result) | ctr_id | alice --> bob | 20 $ EUR #.
Proof.
  intros. exec_exchange H. subst result0.
  simpl. eexists.
  split.
  - left. trivial.
  - repeat split; trivial.
Qed.


Lemma exchange_bob_gets_paid_by_alice_step :
  forall s1 s2 alice bob ctr_id dsc_id,
    In (exchange_ctr alice bob ctr_id dsc_id)  (m_contracts s1) ->
    s1 → s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result tr,
      # tr ∈ (res_ledger result) | ctr_id | alice --> bob | 20 $ EUR #.
Proof.
  intros until 1.
  step_intro.
  assert (H' := H0); auto.
  induction H0; intros; set (EX := (exchange_ctr alice bob ctr_id0 dsc_id0)).
  - unfold append_new_ctr_to_state in H8. subst s2. contradict_hyp H3.
  - same_ctr ctr EX s2.
    same_owner owner (ctr_owner EX) ctr EX.
    subst ctr EX. subst owner. simpl in H9.
    exists (result balance' ctrs' next' ledger').
    eapply exchange_bob_gets_paid_by_alice.
    exact H9.
  - same_ctr ctr EX s2. subst ctr EX.
    unfold exchange_ctr, currency_exchange_desc, ctr_primitive in H6. inversion H6.
  - same_ctr ctr EX s2. subst ctr EX.
    unfold exchange_ctr, currency_exchange_desc, ctr_primitive in H6. inversion H6.
  - subst s2. contradict_hyp H3.
  - subst s2. simpl in H3. contradiction.
Qed.


Theorem exchange_bob_gets_paid_by_alice_steps :
  forall s1 s2 alice bob ctr_id dsc_id,
    In (exchange_ctr alice bob ctr_id dsc_id)  (m_contracts s1) ->
    s1 ⇓ s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result tr,
      # tr ∈ (res_ledger result) | ctr_id | alice --> bob | 20 $ EUR #.
Proof.
  intros.
  assert (H' := H); auto.
  eapply exists_step_in_steps in H'; eauto.
  destruct H' as [s [s' [H3' [H5' [H6' H7']]]]].
  eapply exchange_bob_gets_paid_by_alice_step; eauto.
Qed.
