Load helpers.

Definition EXCHANGE_ADDR_EUR_TO_USD := 23.
Definition exchange_office (timestamp : Time) := 
  gateway EXCHANGE_ADDR_EUR_TO_USD 2 timestamp.


Definition currency_exchange_gtw_desc
           (amount : nat) :=
  (And
     (Give (Scale amount (One EUR)))
     (ScaleObs EXCHANGE_ADDR_EUR_TO_USD (Scale amount (One USD)))
  ).


Definition exchange_ctr
           (alice bob : Address)
           (ctr_id dsc_id : Id)
           (amount : nat) :=
  finctr ctr_id
         dsc_id
         (currency_exchange_gtw_desc amount)
         alice
         bob
         bob
         1.

Ltac exec_exchange H :=
  match type of H with
  | exec_ctr_in_state_with_owner (exchange_ctr _ _ _ _ _) _ _ = Some _ =>
    unfold exchange_ctr, currency_exchange_gtw_desc, exec_ctr_in_state_with_owner in H; simpl in H; inversion H; clear H
  end.


Lemma exchange_alice_gets_paid_by_bob :
  forall s1 alice bob ctr_id dsc_id result amount,
    exec_ctr_in_state_with_owner
      (exchange_ctr alice bob ctr_id dsc_id amount) s1 bob =
    Some result ->
    exists tr, # tr ∈ (res_ledger result) | ctr_id | bob --> alice | amount $ EUR #.
Proof.
  intros.
  exec_exchange H.
  case_eq (query (m_gateway s1) EXCHANGE_ADDR_EUR_TO_USD (m_global_time s1)); intros; rewrite H in H1; try inversion H1; clear H1.
    eexists. simpl.
    split.
    + right. left. trivial.
    + repeat split; trivial.
      simpl. omega.
Qed.
      

Lemma exchange_alice_gets_paid_by_bob_step :
  forall s1 s2 alice bob ctr_id dsc_id amount,
    In (exchange_ctr alice bob ctr_id dsc_id amount)  (m_contracts s1) ->
    s1 → s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result tr,
      # tr ∈ (res_ledger result) | ctr_id | bob --> alice | amount $ EUR #.
Proof.
  intros until 1.
  step_intro.
  assert (H' := H0); auto.
  induction H0; intros; set (EX := (exchange_ctr alice bob ctr_id0 dsc_id0 amount)).
  - unfold append_new_ctr_to_state in H8. subst s2. contradict_hyp H3.
  - same_ctr ctr EX s2.
    same_owner owner (ctr_owner EX) ctr EX.
    subst ctr EX. subst owner. simpl in H9.
    exists (result balance' ctrs' next' ledger').
    eapply exchange_alice_gets_paid_by_bob.
    exact H9.
  - same_ctr ctr EX s2. subst ctr EX.
    unfold exchange_ctr, currency_exchange_gtw_desc, ctr_primitive in H6. inversion H6.
  - same_ctr ctr EX s2. subst ctr EX.
    unfold exchange_ctr, currency_exchange_gtw_desc, ctr_primitive in H6. inversion H6.
  - subst s2. contradict_hyp H3.
  - subst s2. simpl in H3. contradiction.
Qed.


Theorem exchange_alice_gets_paid_by_bob_steps :
  forall s1 s2 alice bob ctr_id dsc_id amount,
    In (exchange_ctr alice bob ctr_id dsc_id amount)  (m_contracts s1) ->
    s1 ⇓ s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result tr,
      # tr ∈ (res_ledger result) | ctr_id | bob --> alice | amount $ EUR #.
Proof.
  intros.
  assert (H' := H); auto.
  eapply exists_step_in_steps in H'; eauto.
  destruct H' as [s [s' [H3' [H5' [H6' H7']]]]].
  eapply exchange_alice_gets_paid_by_bob_step; eauto.
Qed.


Definition check_gateway (s : State) :=
  query (m_gateway s) EXCHANGE_ADDR_EUR_TO_USD (m_global_time s).



Lemma exchange_bob_gets_paid_by_alice :
  forall s1 alice bob ctr_id dsc_id result amount rate,
    exec_ctr_in_state_with_owner
      (exchange_ctr alice bob ctr_id dsc_id amount) s1 bob = Some result ->
    check_gateway s1 = Some rate ->
    exists tr, # tr ∈ (res_ledger result) | ctr_id | alice --> bob | (rate * amount) $ USD #.
Proof.
  intros.
  exec_exchange H.
  case_eq (query (m_gateway s1) EXCHANGE_ADDR_EUR_TO_USD (m_global_time s1)); intros; rewrite H in H2; try inversion H2; clear H2.
    eexists. simpl.
    split.
    + left. trivial.
    + repeat split; trivial.
      simpl.
      apply gateway_is_consistent with (t1 := (m_global_time s1))(v1 := rate) in H; auto.
      subst. simpl.
      rewrite Nat.add_0_r.
      reflexivity.
Qed.



Lemma exchange_bob_gets_paid_by_alice_step :
  forall s1 s2 alice bob ctr_id dsc_id amount rate,
    In (exchange_ctr alice bob ctr_id dsc_id amount)  (m_contracts s1) ->
    s1 → s2 ⊢ ctr_id ->
    bob <> 0 ->
    check_gateway s1 = Some rate -> 
    exists result tr,
      # tr ∈ (res_ledger result) | ctr_id | alice --> bob | rate * amount $ USD #.
Proof.
  intros until 1.
  step_intro.
  assert (H' := H0); auto.
  induction H0; intros; set (EX := (exchange_ctr alice bob ctr_id0 dsc_id0 amount)).
  - unfold append_new_ctr_to_state in H8. subst s2. contradict_hyp H3.
  - same_ctr ctr EX s2.
    same_owner owner (ctr_owner EX) ctr EX.
    subst EX ctr owner. simpl in H9.
    exists (result balance' ctrs' next' ledger'). 
    eapply exchange_bob_gets_paid_by_alice.
    exact H9. auto.
  - same_ctr ctr EX s2. subst ctr EX.
    unfold exchange_ctr, currency_exchange_gtw_desc, ctr_primitive in H6. inversion H6.
  - same_ctr ctr EX s2. subst ctr EX.
    unfold exchange_ctr, currency_exchange_gtw_desc, ctr_primitive in H6. inversion H6.
  - subst s2. contradict_hyp H3.
  - subst s2. simpl in H3. contradiction.
Qed.


Theorem exchange_bob_gets_paid_by_alice_steps :
  forall s1 s2 alice bob ctr_id dsc_id amount rate,
    In (exchange_ctr alice bob ctr_id dsc_id amount)  (m_contracts s1) ->
    s1 ⇓ s2 ⊢ ctr_id ->
    bob <> 0 ->
    check_gateway s1 = Some rate ->
    gateway_stays_fresh s1 s2 ->
    exists result tr,
      # tr ∈ (res_ledger result) | ctr_id | alice --> bob | rate * amount $ USD #.
Proof.
  intros.
  assert (H' := H); auto.
  eapply exists_step_in_steps in H'; eauto.
  destruct H' as [s [s' [H3' [H5' [H6' H7']]]]].
  eapply exchange_bob_gets_paid_by_alice_step; eauto.
  unfold check_gateway in *.
  eapply gateway_is_consistent_on_steps; eauto.
  eapply gateway_stays_fresh_steps_left; eauto.
  destruct H5' as [H5' H5''].
  eapply tran_helper; eauto.
Qed.
