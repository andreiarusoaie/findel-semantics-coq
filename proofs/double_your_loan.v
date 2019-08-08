Load helpers.

Definition double_your_loan_desc (t0 : Time) :=
  (And
     (Before t0 (Or (Give (One USD)) (Give (One EUR))))
     (After t0 (Scale 2 (One EUR)))
  ).


Definition double_your_loan_ctr
           (alice bob : Address)
           (ctr_id dsc_id : Id)
           (t0 : Time) :=
  finctr ctr_id
         dsc_id
         (double_your_loan_desc t0)
         alice
         bob
         bob
         1.

Ltac exec_double_your_loan H :=
  match type of H with
  | exec_ctr_in_state_with_owner (double_your_loan_ctr _ _ _ _ _) _ _ = Some _ =>
    unfold double_your_loan_ctr, double_your_loan_desc, exec_ctr_in_state_with_owner in H; simpl in H; inversion H; clear H
  end.


Lemma bob_requests_double_loan_from_alice :
  forall s1 alice bob ctr_id dsc_id result t0,
    exec_ctr_in_state_with_owner
      (double_your_loan_ctr alice bob ctr_id dsc_id t0) s1 bob =
    Some result ->
    exists ctr,
      % ctr ∈ (res_contracts result) | alice --> bob | (Timebound t0 INF (Scale 2 (One EUR))) %.
Proof.
  intros.
  exec_double_your_loan H.
  case_eq (t0 <? m_global_time s1); intros H; rewrite H in H1.
  - inversion H1.
  - case_eq (0 <? m_global_time s1); intros H2; rewrite H2 in H1.
    case_eq (INF <? m_global_time s1); intros H3; rewrite H3 in H1.
    + inversion H1.
    + inversion H1.
      simpl. 
      eexists.
      split.
      * right. left. trivial.
      * try repeat split; trivial.
    + case_eq (INF <? m_global_time s1); intros H3; rewrite H3 in H1.
      * inversion H1.
      * inversion H1.
        simpl.
        eexists.
        split.
        ** right. left. trivial.
        ** repeat split; trivial.
Qed.



Lemma bob_requests_double_loan_from_alice_step :
  forall s1 s2 alice bob ctr_id dsc_id t0,
    In (double_your_loan_ctr alice bob ctr_id dsc_id t0) (m_contracts s1) ->
    s1 → s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result ctr,
      % ctr ∈ (res_contracts result) | alice --> bob | (Timebound t0 INF (Scale 2 (One EUR))) %.
Proof.
  intros until 1.
  step_intro.
  assert (H' := H0); auto.
  induction H0; intros; set (LOAN := (double_your_loan_ctr alice bob ctr_id0 dsc_id0 t0)).
  - unfold append_new_ctr_to_state in H8. subst s2. contradict_hyp H3.
  - same_ctr ctr LOAN s2.
    same_owner owner (ctr_owner LOAN) ctr LOAN.
    subst ctr LOAN. subst owner. simpl in H9.
    exists (result balance' ctrs' next' ledger').
    eapply bob_requests_double_loan_from_alice.
    exact H9.
  - same_ctr ctr LOAN s2. subst ctr LOAN.
    unfold double_your_loan_ctr, double_your_loan_desc, ctr_primitive in H6. inversion H6.
  - same_ctr ctr LOAN s2. subst ctr LOAN.
    unfold double_your_loan_ctr, double_your_loan_desc, ctr_primitive in H6. inversion H6.
  - subst s2. contradict_hyp H3.
  - subst s2. simpl in H3. contradiction.
Qed.


Theorem bob_requests_double_loan_from_alice_steps :
  forall s1 s2 alice bob ctr_id dsc_id t0,
    In (double_your_loan_ctr alice bob ctr_id dsc_id t0) (m_contracts s1) ->
    s1 ⇓ s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result ctr,
      % ctr ∈ (res_contracts result) | alice --> bob | (Timebound t0 INF (Scale 2 (One EUR))) %.
Proof.
  intros.
  assert (H' := H); auto.
  eapply exists_step_in_steps in H'; eauto.
  destruct H' as [s [s' [H3' [H5' [H6' H7']]]]].
  eapply bob_requests_double_loan_from_alice_step; eauto.
Qed.


Lemma alice_requests_loan_from_bob :
  forall s1 alice bob ctr_id dsc_id result t0,
    exec_ctr_in_state_with_owner
      (double_your_loan_ctr alice bob ctr_id dsc_id t0) s1 bob =
    Some result ->
    (exists ctr,
      % ctr ∈ (res_contracts result) | alice --> bob | (Timebound 0 t0 (Or (Give (One USD)) (Give (One EUR)))) %)
    \/
    exists ctr,
      % ctr ∈ (res_contracts result) | alice --> bob | (Or (Give (One USD)) (Give (One EUR))) %.
Proof.
  intros.
  exec_double_your_loan H.
  case_analysis H1.
  case_analysis H2; case_analysis H3; simpl.
  - right. eexists. split; trivial.
    + left. trivial.
    + simpl. repeat split; trivial. 
  - left. eexists. split; trivial.
    + left. trivial.
    + simpl. repeat split; trivial.
Qed.


Lemma alice_requests_loan_from_bob_step :
  forall s1 s2 alice bob ctr_id dsc_id t0,
    In (double_your_loan_ctr alice bob ctr_id dsc_id t0) (m_contracts s1) ->
    s1 → s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result,
    (exists ctr,
        % ctr ∈ (res_contracts result) | alice --> bob | (Timebound 0 t0 (Or (Give (One USD)) (Give (One EUR)))) %) \/
    exists ctr,
      % ctr ∈ (res_contracts result) | alice --> bob | Or (Give (One USD)) (Give (One EUR)) %.
Proof.
  intros until 1.
  step_intro.
  assert (H' := H0); auto.
  induction H0; intros; set (LOAN := (double_your_loan_ctr alice bob ctr_id0 dsc_id0 t0)).
  - unfold append_new_ctr_to_state in H8. subst s2. contradict_hyp H3.
  - same_ctr ctr LOAN s2.
    same_owner owner (ctr_owner LOAN) ctr LOAN.
    subst ctr LOAN. subst owner. simpl in H9.
    exists (result balance' ctrs' next' ledger').
    eapply alice_requests_loan_from_bob.
    exact H9.
  - same_ctr ctr LOAN s2. subst ctr LOAN.
    unfold double_your_loan_ctr, double_your_loan_desc, ctr_primitive in H6. inversion H6.
  - same_ctr ctr LOAN s2. subst ctr LOAN.
    unfold double_your_loan_ctr, double_your_loan_desc, ctr_primitive in H6. inversion H6.
  - subst s2. contradict_hyp H3.
  - subst s2. simpl in H3. contradiction.
Qed.


Lemma alice_requests_loan_from_bob_steps :
  forall s1 s2 alice bob ctr_id dsc_id t0,
    In (double_your_loan_ctr alice bob ctr_id dsc_id t0) (m_contracts s1) ->
    s1 ⇓ s2 ⊢ ctr_id ->
    bob <> 0 ->
    exists result,
    (exists ctr,
        % ctr ∈ (res_contracts result) | alice --> bob | (Timebound 0 t0 (Or (Give (One USD)) (Give (One EUR)))) %) \/
    exists ctr,
      % ctr ∈ (res_contracts result) | alice --> bob | Or (Give (One USD)) (Give (One EUR)) %.
Proof.
  intros.
  assert (H' := H); auto.
  eapply exists_step_in_steps in H'; eauto.
  destruct H' as [s [s' [H3' [H5' [H6' H7']]]]].
  eapply alice_requests_loan_from_bob_step; eauto.
Qed.
