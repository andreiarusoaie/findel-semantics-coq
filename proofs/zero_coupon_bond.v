Load metaproperties.

(* Zero coupon bond *)
Definition zcb_desc
           (NOW : nat)
           (PERIOD : nat) :=
  (And
     (Give (Scale 10 (One USD)))
     (At (NOW + PERIOD) (Scale 11 (One USD)))
  ).

Lemma consistent_impl_exec:
  forall s ctr,
    consistent_state s ->
    In ctr (m_contracts s) ->
    ~ In (Executed (ctr_id ctr)) (m_events s).
Proof.
  intros.
  destruct H as [_ [_ [_ [H _]]]].
  apply H in H0.
  destruct H0 as [H0 _].
  trivial.
Qed.


(* The owner pays the issuer *)
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

Lemma zcb_step_O_to_I :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
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
  assert (C : ~ In (Executed (ctr_id ctr)) (m_events s1)).
  apply consistent_impl_exec; auto.
  induction H.
  - subst s2. simpl in *.
    destruct H3 as [H3 | H3]; try inversion H3.
    subst ctr.
    contradiction.
  - apply step_executes_only_one_contract
      with (ctr := ctr) (ctr' := ctr0) in S; subst ctr; auto.
    + subst ctr0 s2. simpl in *.
      destruct H3 as [H3 | H3]; try contradiction.
      unfold exec_ctr_in_state_with_owner in H10.
      apply zcb_execute_O_to_I in H10.
      destruct H10 as [tr H10].
      exists tr. simpl in H10.
      unfold can_join in H5.
      simpl in H5.
      destruct H5 as [H5 | H5]; auto.
      ++ subst owner. auto.
      ++ contradiction.
    + subst s2. simpl in *. left. trivial.
  - apply step_executes_only_one_contract
      with (ctr := ctr) (ctr' := ctr0) in S; subst ctr; auto.
    + subst ctr0. simpl in *. unfold zcb_desc in H7. inversion H7.
    + subst s2. simpl in *. left. trivial.
  - apply step_executes_only_one_contract
      with (ctr := ctr) (ctr' := ctr0) in S; subst ctr; auto.
    + subst ctr0. simpl in *. unfold zcb_desc in H7. inversion H7.
    + subst s2. simpl in *. left. trivial.
  - apply step_executes_only_one_contract
      with (ctr := ctr) (ctr' := ctr0) in S; subst ctr; auto;
      subst s2; simpl in *;
        destruct H3 as [H3 | H3]; try inversion H3; try contradiction.
  - subst s2. simpl in *. subst ctr. contradiction.
Qed.


Lemma zcb_steps_O_to_I :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
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
  assert (C : ~ In (Executed (ctr_id ctr)) (m_events s1)).
  apply consistent_impl_exec; auto.
  rewrite H1 in C. simpl in C.
  induction H.
  - subst. contradiction.
  - assert (H' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eexists.
      eapply zcb_step_O_to_I; eauto.
    + subst ctr. simpl in *.
      apply IHsteps in H.
      destruct H as [time [tr [H HT]]].
      exists time, tr.
      split; trivial.
      eapply step_does_not_remove_transactions; eauto.
    + eapply step_preserves_consistent_state in H'; eauto.
      eapply step_does_not_remove_events in H5; eauto.
      destruct H' as [_ [_ [_ [_ T]]]].
      unfold not in T.
      exfalso.
      eapply T. subst ctr.
      split; eauto.
Qed.


(* The owner's rights: either paid or can trigger payment. *)

(* Failed attempt: cannot prove that the owner always gets paid! *)
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
  - admit. (* This case cannot be proved. Timebounds generates a new contract
              whose execution can be triggered later.  *)
Admitted.


(* Contract execution either produces a transaction or a new contract. *) 
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
      ctr_proposed_owner ctr = O /\
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


Lemma zcb_step_I_to_O_new_ctr :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
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
      ctr_proposed_owner ctr = O /\
      ctr_scale ctr = sc.
Proof.
  intros.
  assert (C : ~ In (Executed (ctr_id ctr)) (m_events s1)).
  apply consistent_impl_exec; auto.
  rewrite H1 in C. simpl in C.
  induction H; subst s2.
  - simpl in *. destruct H3 as [H3 | H3]; try inversion H3.
    contradiction.
  - simpl in *. unfold exec_ctr_in_state_with_owner in H10.
    unfold can_join in H5.
    destruct H5 as [H5 | H5]; intros.
    case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr.
    apply zcb_execute_I_to_O_new_ctr in H10.
    simpl in *.
    destruct H10 as
        [[tr (A1 & A2 & A3 & A4 & A5 & A6)] |
         [ctr (A1 & A2 & A3 & A4 & A5 )]].
    + subst. left. exists (m_global_time s1), tr.
      repeat split; trivial.
    + subst. right. exists ctr.
      repeat split; trivial.
      apply in_app_iff. right. trivial.
    + case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
      subst ctr0 ctr.
      simpl in H5. subst O. contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr. unfold zcb_desc in *. simpl in *. inversion H7.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr. unfold zcb_desc in *. simpl in *. inversion H7.
  - simpl in *. destruct H3 as [H3 | H3]. inversion H3. contradiction.
  - simpl in *. contradiction.
Qed.


Lemma zcb_steps_I_to_O_new_ctr :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    steps s1 s2 ->
    now + period + Δ <=? m_global_time s2 = false ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11) \/
    exists ctr,
      In ctr (m_contracts s2) /\
      ctr_primitive ctr = (At (now + period) (Scale 11 (One USD))) /\
      ctr_issuer ctr = I /\
      ctr_proposed_owner ctr = O /\
      ctr_scale ctr = sc.
Proof.
  intros s1 s2 ctr_id0 dsc_id0 now period I O sc ctr H CH. intros.
  assert (C : ~ In (Executed (ctr_id ctr)) (m_events s1)).
  apply consistent_impl_exec; auto.
  rewrite H1 in C. simpl in C.
  induction H.
  - subst. contradiction.
  - assert (H' := H). assert (H'' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eapply zcb_step_I_to_O_new_ctr in H5; eauto.
      destruct H5 as [(t & tr & A1 & A2 & A3 & A4 & A5 & A6) | H5]; auto.
      left. exists tr. repeat split; trivial.
    + rewrite H1 in H. simpl in H.
      apply IHsteps in H.
      destruct H as [H | H].
      ++ left. destruct H as [tr [A1 [A2 A3]]].
         exists tr. split; auto.
         eapply steps_does_not_remove_transactions; eauto.
         eapply tran; eauto. apply refl. trivial.
      ++ clear IHsteps C H'' H1 H2 H3 H0.
         destruct H as [ct [H HT]].
         assert (CP := H5).
         apply step_effect_over_contract with (ctr := ct) in H5; trivial.
         destruct H5 as [H5 | [H5 | H5]].
         ** right. exists ct. split; trivial.
         ** induction CP.
            *** subst s2. right. exists ct. split; trivial.
                simpl. right. trivial.
            *** case_eq (ctr_eq_dec ctr0 ct); intros; try contradiction.
                subst ctr0.
                unfold exec_ctr_in_state_with_owner in H8.
                destruct HT as [HT [B1 [B2 B3]]].
                rewrite HT in H8.
                simpl in H8.
                case_if H8.
                case_if H12.
                **** left. subst s2 ledger'. simpl.
                     eexists. split. left. eauto. simpl.
                     repeat split; trivial.
                     unfold can_join in H1.
                     destruct H1 as [H1 | H1].
                     subst. trivial.
                     subst. contradiction.
                     rewrite B3. trivial.
                **** right. subst s2 ctrs'. eexists.
                     split; simpl.
                     rewrite in_app_iff. right. simpl. left. eauto.
                     simpl. unfold At. repeat split; auto.
                     unfold can_join in H1.
                     destruct H1 as [H1 | H1].
                     subst. trivial.
                     subst. contradiction.
            *** case_eq (ctr_eq_dec ctr0 ct); intros; try contradiction.
                subst ctr0. destruct HT as [HT [B1 [B2 B3]]].
                rewrite HT in H3. inversion H3.
            *** case_eq (ctr_eq_dec ctr0 ct); intros; try contradiction.
                subst ctr0. destruct HT as [HT [B1 [B2 B3]]].
                rewrite HT in H3. inversion H3.
            *** case_eq (ctr_eq_dec ctr0 ct); intros; try contradiction.
                subst ctr0. destruct HT as [HT [B1 [B2 B3]]].
                subst s2. simpl in H5.
                destruct H5 as [H5 | H5]; try inversion H5.
                contradict H5.
                apply consistent_impl_exec; auto.
            *** subst s2. simpl in *. right.
                exists ct. split; trivial.
         ** induction CP.
            *** subst s2. simpl in H5.
                destruct H5 as [H5 | H5]; try inversion H5.
                destruct H' as [_ [_ [_ [H' _]]]].
                apply H' in H.
                destruct H as [_ H].
                contradiction.
            *** case_eq (ctr_eq_dec ctr0 ct); intros; try contradiction.
                subst ctr0. destruct HT as [HT [B1 [B2 B3]]].
                subst s2. simpl in *.
                destruct H5 as [H5 | H5]; try inversion H5.
                destruct H' as [_ [_ [_ [H' _]]]].
                apply H' in H.
                destruct H as [_ H].
                contradiction.
            *** case_eq (ctr_eq_dec ctr0 ct); intros; try contradiction.
                subst ctr0. destruct HT as [HT [B1 [B2 B3]]].
                rewrite HT in H3. inversion H3.
            *** case_eq (ctr_eq_dec ctr0 ct); intros; try contradiction.
                subst ctr0. destruct HT as [HT [B1 [B2 B3]]].
                rewrite HT in H3. inversion H3.
            *** case_eq (ctr_eq_dec ctr0 ct); intros; try contradiction.
                subst ctr0. destruct HT as [HT [B1 [B2 B3]]].
                subst s2. simpl in *.
                destruct H5 as [H5 | H5].
                **** unfold exec_ctr_in_state_with_owner in H6.
                     rewrite HT in H6.
                     simpl in H6.
                     case_if H6.
                     unfold Nat.ltb in H7.
                     apply leb_sound_true in H7.
                     apply leb_sound_false in CH.
                     exfalso.
                     apply CH.
                     omega.
                     case_if H10.
                **** destruct H' as [_ [_ [_ [H' _]]]].
                     apply H' in H.
                     destruct H as [_ H].
                     contradiction.
            *** subst s2. simpl in *. right.
                exists ct. split; trivial.
      ++ apply leb_sound_false in CH.
         apply propleb_sound_false.
         intros not.
         apply CH.
         apply time_inc in H5.
         omega.
    + eapply step_does_not_remove_events in H; eauto.
      eapply step_preserves_consistent_state in H'; eauto.
      subst ctr. simpl in H.
      destruct H' as [_ [_ [_ [_ H']]]].
      exfalso.
      eapply H'; eauto.
Qed.
