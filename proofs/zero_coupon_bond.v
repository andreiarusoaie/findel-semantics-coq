Load metaproperties.

(* Zero coupon bond *)
Definition zcb_desc
           (NOW : nat)
           (PERIOD : nat) :=
  (And
     (Give (Scale 10 (One USD)))
     (At (NOW + PERIOD) (Scale 11 (One USD)))
  ).

Lemma zcb_execute_O_to_I :
  forall sc now period I O bal time gtw ctr_id dsc_id next_id ledger result,
    execute (zcb_desc now period)  sc I O bal time gtw ctr_id dsc_id next_id ledger =
    Some result ->
    exists tr,
      In tr (res_ledger result) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 10 /\
      tr_timestamp tr = time.
Proof.
  unfold zcb_desc. intros.
  simpl in H.
  case_analysis H.
  case_analysis H2; simpl in *.
  - eexists.
    split.
    + right. left. trivial.
    + repeat split; trivial.
  - eexists.
    split.
    + left. trivial.
    + repeat split; trivial.
Qed.


Lemma zcb_execute_I_to_O :
  forall sc now period I O bal time gtw ctr_id dsc_id next_id ledger result,
    execute (zcb_desc now period)  sc I O bal time gtw ctr_id dsc_id next_id ledger =
    Some result ->
    exists tr,
      In tr (res_ledger result) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11 /\
      tr_timestamp tr = time.
Proof.
  unfold zcb_desc. intros.
  simpl in H.
  case_analysis H.
  case_analysis H2; simpl in *.
  - eexists.
    split.
    + left. trivial.
    + repeat split; trivial.
  - admit. (* This case cannot be proved. Timebounds generates a new contract.  *)
Admitted.

Lemma zcb_execute_I_to_O_new_ctr :
  forall sc now period I O bal time gtw ctr_id dsc_id next_id ledger result,
    execute (zcb_desc now period)  sc I O bal time gtw ctr_id dsc_id next_id ledger =
    Some result ->
    (exists tr,
      In tr (res_ledger result) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11 /\
      tr_timestamp tr = time) \/
    exists ctr,
      In ctr (res_contracts result) /\
      ctr_primitive ctr = (At (now + period) (Scale 11 (One USD))) /\
      ctr_issuer ctr = I /\
      ctr_owner ctr = O /\
      ctr_scale ctr = sc.
Proof.
  unfold zcb_desc. intros.
  simpl in H.
  case_analysis H.
  case_analysis H2; simpl in *.
  - left. eexists.
    split.
    + left. trivial.
    + repeat split; trivial.
  - right.
    eexists. split.
    + left. trivial.
    + simpl. unfold At. repeat split; trivial.
Qed.


Lemma zcb_step_O_to_I :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    ~ In (Executed ctr_id) (m_events s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 10 /\
      tr_timestamp tr = (m_global_time s1).
Proof.
  intros.
  assert (S := H).
  induction H.
  - subst s2. simpl in *.
    destruct H4 as [H4 | H4]; try inversion H4; try contradiction.
  - apply step_executes_only_one_contract
      with (ctr := ctr) (ctr' := ctr0) in S; subst ctr; auto.
    + subst ctr0 s2. simpl in *.
      destruct H4 as [H4 | H4]; try contradiction.
      unfold exec_ctr_in_state_with_owner in H11.
      apply zcb_execute_O_to_I in H11.
      destruct H11 as [tr H11].
      exists tr. simpl in H11.
      unfold can_join in H6.
      simpl in H6.
      destruct H6 as [H6 | H6]; auto.
      ++ subst owner. auto.
      ++ contradiction.
    + subst s2. simpl in *. left. trivial.
  - apply step_executes_only_one_contract
      with (ctr := ctr) (ctr' := ctr0) in S; subst ctr; auto.
    + subst ctr0. simpl in *. unfold zcb_desc in H8. inversion H8.
    + subst s2. simpl in *. left. trivial.
  - apply step_executes_only_one_contract
      with (ctr := ctr) (ctr' := ctr0) in S; subst ctr; auto.
    + subst ctr0. simpl in *. unfold zcb_desc in H8. inversion H8.
    + subst s2. simpl in *. left. trivial.
  - apply step_executes_only_one_contract
      with (ctr := ctr) (ctr' := ctr0) in S; subst ctr; auto;
      subst s2; simpl in *;
        destruct H4 as [H4 | H4]; try inversion H4; try contradiction.
  - subst s2. simpl in *. contradiction.
Qed.


Lemma zcb_steps_O_to_I :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    ~ In (Executed ctr_id) (m_events s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    exists time tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 10 /\
      tr_timestamp tr = time.
Proof.
  intros.
  induction H.
  - subst. contradiction.
  - assert (H' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eexists.
      eapply zcb_step_O_to_I; eauto.
      destruct H' as [_ [_ [_ [T _]]]].
      apply T in H.
      destruct H as [H _]; subst ctr; auto.
    + subst ctr. simpl in *.
      apply IHsteps in H.
      destruct H as [time [tr [H HT]]].
      exists time, tr.
      split; trivial.
      eapply step_does_not_remove_transactions; eauto.
    + eapply step_preserves_consistent_state in H'; eauto.
      eapply step_does_not_remove_events in H6; eauto.
      destruct H' as [_ [_ [_ [_ T]]]].
      unfold not in T.
      exfalso.
      eapply T. subst ctr.
      split; eauto.
Qed.


Lemma ltb_n_Sn:
  forall n, n <? S n = true.
Proof.
  induction n; simpl; unfold Nat.ltb; trivial.
Qed.


Lemma leb_sound_true:
  forall n m,
    n <=? m = true -> n <= m.
Proof.
  induction n.
  - induction m; intros; try omega.
  - intros m.
    case_eq m; intros; subst m; simpl in H0.
    + inversion H0.
    + apply IHn in H0. omega.
Qed.


Lemma leb_sound_false:
  forall n m,
    n <=? m = false -> ~ n <= m.
Proof.
  induction n.
  - induction m; intros; simpl in H; inversion H.
  - intros m.
    case_eq m; intros; subst m; simpl in H0.
    + omega.
    + apply IHn in H0. omega.
Qed.


Lemma ltb_sound_true:
  forall n m,
    n <? m = true -> n < m.
Proof.
  unfold Nat.ltb.
  intros.
  simpl in H.
  case_eq m; intros; subst m.
  - inversion H.
  - apply leb_sound_true in H. omega.
Qed.


Lemma ltb_sound_false:
  forall n m,
    n <? m = false -> ~ n < m.
Proof.
  unfold Nat.ltb.
  intros.
  simpl in H.
  case_eq m; intros; subst m.
  - omega.
  - apply leb_sound_false in H. omega.
Qed.


SearchPattern (_ - _ < _).


Lemma zcb_step_I_to_O :
  forall s s' ctr_id dsc_id now period I O sc ctr,
    step s s' ->
    consistent_state s ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s) ->
    ~ In (Executed ctr_id) (m_events s) ->
    In (Executed ctr_id) (m_events s') ->
    O <> 0 ->
    m_global_time s = now + period ->
    m_global_time s' = now + period ->
    Δ <= now + period ->
    exists time tr,
      In tr (m_ledger s') /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11 /\
      tr_timestamp tr = time.
Proof.
  intros.
  induction H; subst s'; simpl in *.
  - destruct H4 as [H4 | H4]; try inversion H4; try contradiction.
  - destruct H4 as [H4 | H4].
    case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    + subst ctr0.
      unfold can_join in H9.
      destruct H9 as [H9 | H9]; intros.
      * subst. simpl in *.
        unfold exec_ctr_in_state_with_owner, zcb_desc in *.
        simpl in *.
        case_analysis H14.
        case_analysis H16.
        ** eexists. eexists.
           split. simpl. left. trivial.
           repeat split; trivial.
        ** rewrite H7 in *.
           apply ltb_sound_false in H9.
           exfalso. unfold not in H9.
           apply H9.
           apply Nat.sub_lt; trivial.
           unfold Δ. omega.
      * subst ctr. simpl in *. subst. contradiction.
    + contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr. unfold zcb_desc, ctr_primitive in *. inversion H11.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr. unfold zcb_desc, ctr_primitive in *. inversion H11.
  - destruct H4 as [H4 | H4]; try inversion H4; try contradiction.
  - contradiction.
Qed.


Lemma zcb_step_I_to_O_new_ctr :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    ~ In (Executed ctr_id) (m_events s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists time tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11 /\
      tr_timestamp tr = time) \/
    exists ctr,
      In ctr (m_contracts s2) /\
      ctr_primitive ctr = (At (now + period) (Scale 11 (One USD))) /\
      ctr_issuer ctr = I /\
      ctr_owner ctr = O /\
      ctr_scale ctr = sc.
Proof.
  intros.
  induction H; subst s2.
  - simpl in *. destruct H4 as [H4 | H4]; try inversion H4.
    contradiction.
  - simpl in *. unfold exec_ctr_in_state_with_owner in H11.
    unfold can_join in H6.
    destruct H6 as [H6 | H6]; intros.
    case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr.
    apply zcb_execute_I_to_O_new_ctr in H11.
    simpl in *.
    destruct H11 as
        [[tr (A1 & A2 & A3 & A4 & A5 & A6)] |
         [ctr (A1 & A2 & A3 & A4 & A5 )]].
    + subst. left. exists (m_global_time s1), tr.
      repeat split; trivial.
    + subst. right. exists ctr.
      repeat split; trivial.
      apply in_app_iff. right. trivial.
    + case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
      subst ctr0 ctr.
      simpl in H6. subst O. contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr. unfold zcb_desc in *. simpl in *. inversion H8.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr. unfold zcb_desc in *. simpl in *. inversion H8.
  - simpl in *. destruct H4 as [H4 | H4]. inversion H4. contradiction.
  - simpl in *. contradiction.
Qed.


Lemma zcb_steps_I_to_O_new_ctr :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    ~ In (Executed ctr_id) (m_events s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists time tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11 /\
      tr_timestamp tr = time) \/
    exists ctr,
      In ctr (m_contracts s2) /\
      ctr_primitive ctr = (At (now + period) (Scale 11 (One USD))) /\
      ctr_issuer ctr = I /\
      ctr_owner ctr = O /\
      ctr_scale ctr = sc.
Proof.
  intros.
  induction H.
  - subst. contradiction.
  - assert (H' := H). assert (H'' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eapply zcb_step_I_to_O_new_ctr; eauto.
      destruct H' as [_ [_ [_ [H' _]]]].
      apply H' in H.
      destruct H as [H _].
      subst ctr. simpl in H. trivial.
    + subst ctr. simpl in H.
      apply IHsteps in H.
      destruct H as [[t [tr [H A]]] | [ctr [H [A1 [A2 [A3 A4]]]]]].
      * left. exists t, tr.
        split; trivial.
        eapply step_does_not_remove_transactions; eauto.
      * clear H2 H3 H4. clear IHsteps.
        apply step_effect_over_contract with (ctr := ctr) in H6.
        destruct H6 as [H6 | [H6 | H6]].
        ** right. exists ctr. repeat split; trivial.
        ** left. 
        induction H6; subst s2; simpl in *.
        ** 

        right. exists ctr.
        split; trivial.




  - simpl in *. destruct H4 as [H4 | H4]; try inversion H4.
    contradiction.
  - simpl in *. unfold exec_ctr_in_state_with_owner in H11.
    unfold can_join in H6.
    destruct H6 as [H6 | H6]; intros.
    case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr.
    apply zcb_execute_I_to_O_new_ctr in H11.
    simpl in *.
    destruct H11 as
        [[tr (A1 & A2 & A3 & A4 & A5 & A6)] |
         [ctr (A1 & A2 & A3 & A4 & A5 )]].
    + subst. left. exists (m_global_time s1), tr.
      repeat split; trivial.
    + subst. right. exists ctr.
      repeat split; trivial.
      apply in_app_iff. right. trivial.
    + case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
      subst ctr0 ctr.
      simpl in H6. subst O. contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr. unfold zcb_desc in *. simpl in *. inversion H8.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr. unfold zcb_desc in *. simpl in *. inversion H8.
  - simpl in *. destruct H4 as [H4 | H4]. inversion H4. contradiction.
  - simpl in *. contradiction.
Qed.

Lemma zcb_steps_I_to_O :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    ~ In (Executed ctr_id) (m_events s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists time tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11 /\
      tr_timestamp tr = time) \/
    exists ctr,
      In ctr (m_contracts s2) /\
      ctr_primitive ctr = (At (now + period) (Scale 11 (One USD))) /\
      ctr_issuer ctr = I /\
      ctr_owner ctr = O /\
      ctr_scale ctr = sc.
Proof.
  intros.
  induction H.
  - subst. contradiction.
  - apply zcb_execute_I_to_O_new_ctr in H6.
    assert (H' := H). assert (H'' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eapply zcb_execute_I_to_O_new_ctr in H9.


zcb_execute_I_to_O_new_ctr


Lemma zcb_steps_I_to_O :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    ~ In (Executed ctr_id) (m_events s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    m_global_time s1 = now ->
    m_global_time  s2 = (now + period) ->
    Δ <= now + period ->
    exists time tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11 /\
      tr_timestamp tr = time.
Proof.
  intros.
  induction H.
  - subst. contradiction.
  - assert (H' := H). assert (H'' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eapply zcb_step_I_to_O; eauto.
      * destruct H' as [_ [_ [_ [H' _]]]].
        apply H' in H.
        destruct H as [H _]. subst ctr. simpl in H. trivial.
      * eapply no_tick_if_event_generated'; eauto.
        exists (Executed ctr_id0).
        split; auto.
        destruct H' as [_ [_ [_ [H' _]]]].
        apply H' in H.
        destruct H as [H _]. subst ctr. simpl in H. trivial.
    + subst ctr. simpl in H.
      eapply IHsteps in H. clear IHsteps.
      * destruct H as [time [tr [H HT]]].
        exists time, tr.
        split; trivial.
        eapply steps_does_not_remove_transactions; eauto.
        eapply tran; eauto. eapply refl. trivial.
      * apply time_passes_one_step_at_a_time' with (n := now + period - 1)in H9.
        clear H2 IHsteps.
        destruct H9 as [H9 | H9].
        ** admit.
        ** admit.
        ** 
        
    + subst ctr. simpl in H.
      assert (TH: In (Deleted ctr_id0) (m_events s2)).
      eapply step_does_not_remove_events; eauto.
      apply step_preserves_consistent_state with (s' := s2)in H'; auto.
      destruct H' as [_ [_ [_ [_ H']]]].
      unfold not in H'.
      exfalso.
      eapply H'; eauto.
Admitted.





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
        % ctr ∈ (res_contracts result) | alice --> bob | (At (time + period) (Scale 11 (One USD))) %)
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
      % ctr ∈ (res_contracts result) | alice --> bob | (At (time + period) (Scale 11 (One USD))) %)
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
      % ctr ∈ (res_contracts result) | alice --> bob | At (time + period) (Scale 11 (One USD)) %)
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
