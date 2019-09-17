Load metaproperties.

(* Zero coupon bond *)
Definition zcb_desc
           (NOW : nat)
           (PERIOD : nat) :=
  (And
     (Give (Scale 10 (One USD)))
     (At (NOW + PERIOD) (Scale 11 (One USD)))
  ).

(* The issuer's rights *)
Lemma zcb_execute_O_to_I :
  forall sc now period I O bal time gtw ctr_id dsc_id next_id ledger result,
    execute (zcb_desc now period) sc I O bal time gtw ctr_id dsc_id next_id ledger =
    Some result ->
    exists tr,
      In tr (res_ledger result) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 10.
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
      tr_amount tr = sc * 10.
Proof.
  intros.
  induction H.
  - subst s2. find_contradiction H2.
    destruct H3 as [H3 | H3]; try inversion H3; try contradiction.
  - ctr_case_analysis ctr ctr0.
    subst ctr s2. simpl in *.
    destruct H3 as [H3 | H3]; try contradiction.
    unfold exec_ctr_in_state_with_owner in *.
    simpl in H10. inversion H10.
    case_analysis H11.
    case_analysis H14.
    + eexists. simpl. split.
      * right. left. eauto.
      * simpl. repeat split; trivial.
        resolve_owner H5.
    + eexists. simpl. split.
      * left. eauto.
      * simpl. repeat split; trivial.
        resolve_owner H5.
  - ctr_case_analysis ctr ctr0. subst ctr s2. simpl in H7.
    unfold zcb_desc in H7. inversion H7.
  - ctr_case_analysis ctr ctr0. subst ctr s2. simpl in H7.
    unfold zcb_desc in H7. inversion H7.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - subst. simpl in *. find_contradiction H2.
Qed.


(* If the owner joins, the issuer receives sc * 10 USD from the owner *)
Proposition zcb_steps_O_to_I :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    steps s1 s2 ->
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
      tr_amount tr = sc * 10.
Proof.
  intros.
  induction H.
  - subst. find_contradiction H2.
  - assert (H' := H). assert (H'' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eapply zcb_step_O_to_I; eauto.
    + subst ctr. simpl in *.
      apply IHsteps in H.
      destruct H as [tr [H HT]].
      exists tr.
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

Print zcb_steps_O_to_I.


(* The owner's rights:
1. If  current time < now + period -> the owner can trigger payment later.
2. If current time  = now + period and the owner triggers -> the owner gets paid.
*)

Lemma zcb_step_I_to_O :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (m_global_time s1) > now + period - Δ ->
    (m_global_time s2) > now + period + Δ ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.
  intros.
  induction H.
  - subst s2. find_contradiction H2.
    destruct H3 as [H3 | H3]; try inversion H3; try contradiction.
  - ctr_case_analysis ctr ctr0.
    subst ctr s2. simpl in *.
    destruct H3 as [H3 | H3]; try contradiction. clear H3.
    + unfold exec_ctr_in_state_with_owner in H12.
      simpl in H12. inversion H12. clear H12.
      case_analysis H3.
      case_analysis H13.
      * simpl. eexists. split.
        ** left. eauto.
        ** repeat split; trivial. simpl. resolve_owner H7.
      * apply ltb_sound_false in H3.
        apply ltb_sound_false in H1.
        contradict H3. omega.
  - ctr_case_analysis ctr ctr0. subst ctr s2. simpl in H9.
    unfold zcb_desc in H9. inversion H9.
  - ctr_case_analysis ctr ctr0. subst ctr s2. simpl in H9.
    unfold zcb_desc in H9. inversion H9.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - subst. simpl in *. find_contradiction H2.
Qed.

Lemma zcb_step_I_to_O' :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (m_global_time s2) < now + period - Δ ->
    exists ctr,
      In ctr (m_contracts s2) /\
      ctr_primitive ctr = (At (now + period) (Scale 11 (One USD))) /\
      ctr_issuer ctr = I /\
      ctr_proposed_owner ctr = O /\
      ctr_scale ctr = sc.
Proof.
  intros.
  induction H.
  - subst s2. find_contradiction H2.
    destruct H3 as [H3 | H3]; try inversion H3; try contradiction.
  - ctr_case_analysis ctr ctr0.
    subst ctr s2. simpl in *.
    destruct H3 as [H3 | H3]; try contradiction.
    + unfold exec_ctr_in_state_with_owner in *.
      simpl in H12. inversion H12.
      case_analysis H12.
      case_analysis H15.
      * apply ltb_sound_true in H12.
        apply ltb_sound_false in H1.
        omega.
      * eexists. split; simpl.
        ** rewrite in_app_iff. right. simpl. left. eauto.
        ** repeat split; trivial. resolve_owner H6.
  - ctr_case_analysis ctr ctr0. subst ctr s2. simpl in H8.
    unfold zcb_desc in H8. inversion H8.
  - ctr_case_analysis ctr ctr0. subst ctr s2. simpl in H8.
    unfold zcb_desc in H8. inversion H8.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - subst. simpl in *. find_contradiction H2.
Qed.


Lemma zcb_steps_I_to_O':
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (m_global_time s1) > now + period + Δ ->
    (m_global_time s2) < now + period - Δ ->
    exists ctr,
      In ctr (m_contracts s2) /\
      ctr_primitive ctr = (At (now + period) (Scale 11 (One USD))) /\
      ctr_issuer ctr = I /\
      ctr_proposed_owner ctr = O /\
      ctr_scale ctr = sc.
Proof.
  intros.
  induction H.
  - subst. find_contradiction H2.
  - assert (H' := H). assert (H'' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eapply zcb_step_I_to_O'; eauto.
    + assert (S := H6).
      apply time_inc in H6.
      assert (m_global_time s <= now + period - Δ); try omega.
      subst ctr. simpl in *.
      apply IHsteps in H; auto.
      destruct H as [ctr [H [A HT]]].
      exists ctr.
      split; trivial.
      ++ induction S; subst s2; simpl; auto.
         ** ctr_case_analysis ctr ctr0.
            destruct ctr. simpl in *.
            rewrite A in H13.
            clear H14 H12 H10 H9 IHsteps H12 H3 H4 H1 H8 H2 H A HT.
            unfold exec_ctr_in_state_with_owner in H13. simpl in *.
            case_if H13.
            case_if H17.
            *** apply ltb_sound_true in H1.
                apply ltb_sound_false in H.
                omega.
            *** apply ltb_sound_false in H1.
                apply ltb_sound_false in H. 
                contradict H13. auto.

            destruct (ctr_primitive ctr); try inversion A.
            subst. simpl in H5, H6.


        struct (ctr_primitive ctr); inversion A.
         subst. 
         

      admit.
    + eapply step_preserves_consistent_state in H'; eauto.
      eapply step_does_not_remove_events in H6; eauto.
      destruct H' as [_ [_ [_ [_ T]]]].
      unfold not in T.
      exfalso.
      eapply T. subst ctr.
      split; eauto.
Admitted.

Lemma timebound_postpone:
  forall s s' c p t0 t1,
    step s s' ->
    consistent_state s ->
    In c (m_contracts s) ->
    m_global_time s <= t0 ->
    m_global_time s' <= t0 ->
    ctr_primitive c = (Timebound t0 t1 p) ->
    exists c', In c' (m_contracts s') /\ ctr_primitive c' = p.
Proof.
  intros.
  induction H; subst s'; simpl.
  - right. trivial.
  - ctr_case_analysis c ctr.
    apply in_app_iff.
    unfold exec_ctr_in_state_with_owner in H8.
    induction (ctr_primitive c); simpl in *; try inversion H3.
    subst. 
    clear H6 H.
    subst.
    clear H10 H3.
    
    + apply ltb_sound_true in H9.
      apply ltb_sound_false in H12.
      try omega.
    + simpl. subst.
      clear H2 H5 H0.




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


Lemma zcb_step_I_to_O :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
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
  intros.
  induction H; subst s2.
  - simpl in *. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0. simpl in *. destruct H3 as [H3 | H3].
    + unfold exec_ctr_in_state_with_owner in H10.
      rewrite H1 in H10. simpl in H10.
      case_analysis H10.
      case_analysis H14.
      * left. eexists. split. simpl. left. trivial.
        simpl. repeat split; trivial.
        unfold can_join in H5.
        destruct H5 as [H5 | H5]; subst; simpl in *; trivial.
        subst O. contradiction.
      * right. eexists. split. rewrite in_app_iff.
        right. simpl. left. trivial.
        simpl. repeat split; trivial.
        unfold can_join in H5.
        destruct H5 as [H5 | H5]; subst; simpl in *; trivial.
        subst O. contradiction.
    + subst ctr. simpl in *. contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr. unfold zcb_desc in *. simpl in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0 ctr. unfold zcb_desc in *. simpl in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0. simpl in *. destruct H3 as [H3 | H3]; try inversion H3.
    apply consistent_impl_exec in H2; auto.
    subst ctr. simpl in *. contradiction.
  - subst. simpl in *.    
    apply consistent_impl_exec in H2; auto.
    simpl in *. contradiction.
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
    + eapply zcb_step_I_to_O in H5; eauto.
      destruct H5 as [(tr & A1 & A2 & A3 & A4 & A5) | H5]; auto.
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



(* Lemma zcb_step_I_to_O' : *)
(*   forall s1 s2 ctr_id dsc_id now period I O sc ctr, *)
(*     step s1 s2 -> *)
(*     consistent_state s1 -> *)
(*     ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc -> *)
(*     In ctr (m_contracts s1) -> *)
(*     In (Executed ctr_id) (m_events s2) -> *)
(*     O <> 0 -> *)
(*     (m_global_time s2) > now + period -> *)
(*     (exists tr, *)
(*       In tr (m_ledger s2) /\ *)
(*       tr_ctr_id tr = ctr_id /\ *)
(*       tr_from tr = I /\ *)
(*       tr_to tr = O /\ *)
(*       tr_amount tr = sc * 11). *)
(* Proof. *)
(* Admitted. *)

(* Lemma zcb_steps_I_to_O' : *)
(*   forall s1 s2 ctr_id dsc_id now period I O sc ctr, *)
(*     steps s1 s2 -> *)
(*     consistent_state s1 -> *)
(*     ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc -> *)
(*     In ctr (m_contracts s1) -> *)
(*     In (Executed ctr_id) (m_events s2) -> *)
(*     O <> 0 -> *)
(*     (m_global_time s2) > now + period -> *)
(*     (m_global_time s1) = now -> *)
(*     (exists tr, *)
(*       In tr (m_ledger s2) /\ *)
(*       tr_ctr_id tr = ctr_id /\ *)
(*       tr_from tr = I /\ *)
(*       tr_to tr = O /\ *)
(*       tr_amount tr = sc * 11). *)
(* Proof. *)
(*   intros. *)
(*   induction H. *)
(*   - subst s2. omega. *)
(*   - assert (Ss := H). assert (S := H7). *)
(*     eapply steps_effect_over_contract in H; eauto. *)
(*     eapply steps_preserves_consistent_state in Ss; eauto. *)
(*     destruct H as [H | [H | H]]. *)
(*     + eapply zcb_step_I_to_O' in S; eauto. *)
(*     + rewrite H1 in H. simpl in H. *)
(*       eapply IHsteps in H. *)
(*       * destruct H as [tr [H H']]. *)
(*         exists tr. split; trivial. *)
(*         eapply step_does_not_remove_transactions; eauto. *)
(*       * induction H7; subst s2. *)
(*         ** find_contradiction H2. *)
(*         ** ctr_case_analysis ctr ctr0. simpl in H5. trivial. *)
(*         ** ctr_case_analysis ctr ctr0. simpl in H5. trivial. *)
(*         ** ctr_case_analysis ctr ctr0. simpl in H5. trivial. *)
(*         ** ctr_case_analysis ctr ctr0. simpl in H5. trivial. *)
(*         ** simpl in *. f *)
