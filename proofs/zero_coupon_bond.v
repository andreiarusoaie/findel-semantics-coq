Load helpers.

Definition zero_coupon_bond
           (NOW : nat)
           (PERIOD : nat) :=
  (And
     (Give (Scale 10 (One USD)))
     (At (NOW + PERIOD) (Scale 11 (One USD)))
  ).


Definition zcb
           (alice bob : Address)
           (ctr_id dsc_id : Id)
           (now period : nat)  :=
  finctr ctr_id
         dsc_id
         (zero_coupon_bond now period)
         alice
         bob
         bob
         1.

Ltac exec_zcb H :=
  match type of H with
  | exec_ctr_in_state_with_owner (zcb _ _ _ _ _ _) _ _ = Some _ =>
    unfold zcb, zero_coupon_bond, exec_ctr_in_state_with_owner in H; simpl in H
  end.


Lemma zcb_alice_gets_paid_by_bob :
  forall s1 period alice bob ctr_id dsc_id time result,
    exec_ctr_in_state_with_owner
      (zcb alice bob ctr_id dsc_id time period) s1 bob =
    Some result ->
    exists tr, # tr ∈ (res_ledger result) | ctr_id | bob --> alice | 10 $ USD #.
Proof.
  intros.
  exec_zcb H.
  case_analysis H.
  case_analysis H2; eexists; split.
  - right. left. trivial.
  - repeat split; trivial.
  - left. trivial.
  - repeat split; trivial.
Qed.


Lemma zcb_alice_gets_paid :
  forall s1 s2 period alice bob ctr_id dsc_id time,
    In (zcb alice bob ctr_id dsc_id time period) (m_contracts s1) ->
    s1 → s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result tr,
      # tr ∈ (res_ledger result) | ctr_id | bob --> alice | 10 $ USD #.
Proof.
  intros until 1.
  step_intro.
  assert (H' := H0); auto.
  induction H0; intros; set (ZCB := (zcb alice bob ctr_id0 dsc_id0 time period)).
  - unfold append_new_ctr_to_state in H8. subst s2. contradict_hyp H3.
  - same_ctr ctr ZCB s2.
    same_owner owner (ctr_owner ZCB) ctr ZCB.
    subst ctr ZCB. subst owner. simpl in H9.
    exists (result balance' ctrs' next' ledger').
    eapply zcb_alice_gets_paid_by_bob.
    exact H9.
  - same_ctr ctr ZCB s2. subst ctr ZCB.
    unfold zcb, zero_coupon_bond, ctr_primitive in H6. inversion H6.
  - same_ctr ctr ZCB s2. subst ctr ZCB.
    unfold zcb, zero_coupon_bond, ctr_primitive in H6. inversion H6.
  - subst s2. contradict_hyp H3.
  - subst s2. simpl in H3. contradiction.
Qed.


Lemma zcb_alice_gets_paid_steps :
  forall s1 s2 period alice bob ctr_id dsc_id time,
    In (zcb alice bob ctr_id dsc_id time period) (m_contracts s1) ->
    s1 ⇓ s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result tr,
      # tr ∈ (res_ledger result) | ctr_id | bob --> alice | 10 $ USD #.
Proof.
  intros.
  assert (H' := H); auto.
  eapply exists_step_in_steps in H'; eauto.
  destruct H' as [s [s' [H3' [H5' [H6' H7']]]]].
  eapply zcb_alice_gets_paid in H5'; eauto.
Qed.


(* Interesting: the following lemma does not hold!
   It shouldn't: bob gets paid by alice only if he
                 executes the generated contract
                 precisely at now+period moment in
                 time.
 *)
Lemma zcb_bob_gets_paid_by_alice_failed :
  forall s1 time period alice bob ctr_id dsc_id result,
    exec_ctr_in_state_with_owner
      (zcb alice bob ctr_id dsc_id time period) s1 bob =
    Some result ->
    exists tr,
      # tr ∈ (res_ledger result) | ctr_id | alice --> bob | 11 $ USD #.
Proof.
  intros.
  exec_zcb H.
  case_analysis H.
  case_analysis H2.
  - subst result0.
    simpl.
    eexists.
    split.
    + left. trivial.
    + repeat split; trivial.
  - subst result0. simpl.
Abort.


Lemma zcb_bob_is_paid_or_claims_payment :
  forall s1 time period alice bob ctr_id dsc_id result,
    exec_ctr_in_state_with_owner
      (zcb alice bob ctr_id dsc_id time period) s1 bob =
    Some result ->
    (exists ctr,
        % ctr ∈ (res_contracts result) | alice --> bob | (Scale 11 (One USD)) %)
    \/
    exists tr,
      # tr ∈ (res_ledger result) | ctr_id | alice --> bob | 11 $ USD #.
Proof.
  intros.
  exec_zcb H.
  case_analysis H.
  case_analysis H2; subst result0; simpl.
  - right. eexists. split.
    + left. trivial.
    + repeat split; trivial.
  - left. eexists. split.
    + left. trivial.
    + repeat split; trivial.
Qed.


Lemma zcb_bob_is_paid_or_claims_payment_step :
  forall s1 s2 period alice bob ctr_id dsc_id time,
    In (zcb alice bob ctr_id dsc_id time period) (m_contracts s1) ->
    (s1 → s2 ⊢ ctr_id) ->
    bob <> 0 ->
    exists result,
    (exists ctr,
      % ctr ∈ (res_contracts result) | alice --> bob | (Scale 11 (One USD)) %)
    \/
    exists tr,
      # tr ∈ (res_ledger result) | ctr_id | alice --> bob | 11 $ USD #.
Proof.
  intros until 1.
  step_intro.
  inversion H0; intros; set (ZCB := (zcb alice bob ctr_id0 dsc_id0 time period)).
  - unfold append_new_ctr_to_state in H9. subst s2. contradict_hyp H3.
  - same_ctr ctr ZCB s2.
    same_owner owner (ctr_owner ZCB) ctr ZCB.
    subst ZCB. simpl in H11. subst owner.
    exists (result balance' ctrs' next' ledger').
    eapply zcb_bob_is_paid_or_claims_payment.
    subst ctr. exact H10.
  - same_ctr ctr ZCB s2. subst ctr ZCB.
    unfold zcb, zero_coupon_bond, ctr_primitive in H7. inversion H7.
  - same_ctr ctr ZCB s2. subst ctr ZCB.
    unfold zcb, zero_coupon_bond, ctr_primitive in H7. inversion H7.
  - subst s2. contradict_hyp H3.
  - subst s2. simpl in H3. contradiction.
Qed.


Lemma zcb_bob_is_paid_or_claims_payment_steps :
  forall s1 s2 period alice bob ctr_id dsc_id time,
    In (zcb alice bob ctr_id dsc_id time period) (m_contracts s1) ->
    (s1 ⇓ s2 ⊢ ctr_id) ->
    bob <> 0 ->
    exists result,
    (exists ctr,
      % ctr ∈ (res_contracts result) | alice --> bob | (Scale 11 (One USD)) %)
    \/
    exists tr,
      # tr ∈ (res_ledger result) | ctr_id | alice --> bob | 11 $ USD #.
Proof.
  intros.
  assert (H' := H); auto.
  eapply exists_step_in_steps in H'; eauto.
  destruct H' as [s [s' [H3' [H5' [H6' H7']]]]].
  eapply zcb_bob_is_paid_or_claims_payment_step in H5'; eauto.
Qed.
