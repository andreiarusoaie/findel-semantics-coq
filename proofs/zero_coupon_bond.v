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
Proposition zcb_O_to_I:
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    joins O ctr s1 s2 now ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 10.
Proof.
  intros.
  destruct_join H1.
  - insert_consistent s Ss.
    induction St; subst s'.
    -- inversion_event Ev. find_contradiction M.
    -- ctr_case_analysis ctr ctr0.
       execute_own ctr H9.
       case_analysis H9.
       case_analysis H12.
       ++ eexists. split.
          +++ eapply steps_does_not_remove_transactions; eauto.
              simpl. subst ledger'. right. left. eauto.
          +++ repeat split; trivial. resolve_owner H4.
       ++ eexists. split.
          +++ eapply steps_does_not_remove_transactions; eauto.
              simpl. subst ledger'. left. eauto.
          +++ repeat split; trivial. resolve_owner H4.
    -- not_or ctr ctr0 H6.
    -- not_or ctr ctr0 H6.
    -- ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
    -- find_contradiction M.
  - insert_consistent s Ss.
    induction St; subst s'.
    -- inversion_event Ev. find_contradiction_del M.
    -- ctr_case_analysis ctr ctr0.
       subst ctr. inversion_event Ev.
       simpl in *.
       execute_own ctr H9.
       case_analysis H9.
       case_analysis H12.
       ++ eexists. split.
          +++ eapply steps_does_not_remove_transactions; eauto.
              simpl. subst ledger'. right. left. eauto.
          +++ repeat split; trivial. resolve_owner H4.
       ++ eexists. split.
          +++ eapply steps_does_not_remove_transactions; eauto.
              simpl. subst ledger'. left. eauto.
          +++ repeat split; trivial. resolve_owner H4.
    -- not_or ctr ctr0 H6.
    -- not_or ctr ctr0 H6.
    -- ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
    -- find_contradiction M.

    insert_consistent s Ss.


    insert_consistent s' St.
    find_contradiction_del M.
Qed.

Print zcb_O_to_I.


(* The owner's rights - see Proposition after this lemma *)

(* helper lemma for the inner contract *) 
Lemma inner_ctr_proof:
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (At (now + period) (Scale 11 (One USD))) I O O sc ->
    joins O ctr s1 s2 (now + period) ->
    O <> 0 ->
    period > Δ ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.
  intros.
  destruct_join H1.
  insert_consistent s Ss.
  induction St; subst s'.
  - inversion_event Ev. find_contradiction M.
  - ctr_case_analysis ctr ctr0.
    execute_own ctr H10.
    case_if H10.
    case_if H14.
    + eexists. split.
      ++ eapply steps_does_not_remove_transactions; eauto.
         subst ledger'. simpl. left. eauto.
      ++ repeat split; trivial. resolve_owner H5.
    + eapply ltb_sound_false in H10. contradict H10. rewrite <- T. unfold Δ. omega.
  - not_or ctr ctr0 H7.
  - not_or ctr ctr0 H7.
  - ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
  - find_contradiction M.
Qed.

Proposition zcb_I_to_O:
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    joins_generated O ctr s1 s2 now (now + period) ->
    O <> 0 ->
    period > Δ ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.
  intros.
  destruct_join_gen H1.
  insert_consistent s Ss.
  insert_consistent s' St.
  induction St; subst s'.
  - inversion_event Ev. find_contradiction M.
  - ctr_case_analysis ctr ctr1.
    simpl in Ev. inversion_event Ev.
    execute_own ctr H11.
    case_analysis H11.
    case_analysis H15.
    + eexists. split.
      eapply steps_does_not_remove_transactions. exact Ss0.
      subst ledger'. simpl. left. eauto.
      repeat split; trivial.
      simpl. resolve_owner H6.
    + destruct_join J.
      simpl in Exec.
      rewrite H0, H11 in Exec.
      inversion Exec. clear Exec. subst res.
      simpl in M0. destruct M0 as [M0 | M0]; try contradiction.
      eapply inner_ctr_proof; eauto.
      unfold joins. exists s0, s'. unfold At.
      repeat split; subst ctr0; simpl in *; try exact M1; trivial.
  - not_or ctr ctr1 H8.
  - not_or ctr ctr1 H8.
  - ctr_case_analysis ctr ctr1. inversion_event Ev. find_contradiction M.
  - find_contradiction M.
Qed.

Print zcb_I_to_O.


Lemma O_joins_generated_too_late_inner:
  forall s1 s2 c_id dsc_id now period I O sc ctr T,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (At (now + period) (Scale 11 (One USD))) I O O sc ->
    joins O ctr s1 s2 T ->
    T > now + period + Δ ->
    period > Δ ->
    O <> 0 ->
    In (Deleted (ctr_id ctr)) (m_events s2).
Proof.
  intros.
  destruct_join H1.
  insert_consistent s Ss.
  induction St; subst s'.
  - inversion_event Ev. find_contradiction M.
  - ctr_case_analysis ctr ctr0.
    execute_own ctr H11.
    simpl in *.
    case_if H11.
    case_if H14; rewrite T0 in *; apply ltb_sound_false in H0; contradict H0; omega.
  - not_or ctr ctr0 H8.
  - not_or ctr ctr0 H8.
  - ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
  - find_contradiction M.
Qed.


  Lemma O_joins_generated_too_late:
  forall s1 s2 c_id dsc_id now period I O sc ctr T,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (zcb_desc now period) I O O sc ->
    joins_generated O ctr s1 s2 now T ->
    T > now + period + Δ ->
    period > Δ ->
    O <> 0 ->
    exists ctr',
      In (Deleted (ctr_id ctr')) (m_events s2) /\
      ctr_primitive ctr' = (At (now + period) (Scale 11 (One USD))) /\
      ctr_issuer ctr = I /\
      ctr_proposed_owner ctr = O /\
      ctr_scale ctr = sc.
Proof.
  intros.
  destruct_join_gen H1.
  insert_consistent s Ss.
  induction St; subst s'.
  - inversion_event Ev. find_contradiction M.
  - ctr_case_analysis ctr ctr1.
    execute_own ctr H11.
    case_analysis H11.
    case_analysis H14.
    + rewrite <- T0 in *.
      apply ltb_sound_true in H11.
      apply ltb_sound_false in H0.
      contradict H0. unfold Δ. omega.
    + destruct_join J. simpl in Exec.
      rewrite H0, H11 in Exec.
      inversion Exec. subst res.
      simpl. eexists.
      split. eapply steps_does_not_remove_events; eauto.
      eexists. repeat split; trivial.
  - not_or ctr ctr1 H7.
  - not_or ctr ctr1 H7.
  - ctr_case_analysis ctr ctr1. inversion_event Ev. find_contradiction M.
  - find_contradiction M.
Qed.


(* 
Proposition zcb_I_to_O:
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    joins_generated O ctr s1 s2 now (now + period) ->
    O <> 0 ->
    (now + period > Δ) ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.


Lemma zcb_step_I_to_O :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    is_executed ctr s1 s2 O ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.


Lemma zcb_step_I_to_O :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (m_global_time s2) > now + period - Δ ->
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
    + unfold exec_ctr_in_state_with_owner in H11.
      simpl in H11. inversion H11. clear H11.
      case_analysis H3.
      case_analysis H12.
      * simpl. eexists. split.
        ** left. eauto.
        ** repeat split; trivial. simpl. resolve_owner H6.
      * apply ltb_sound_false in H3.
        apply ltb_sound_false in H1.
        contradict H3. omega.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    unfold zcb_desc in H8. inversion H8.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    unfold zcb_desc in H8. inversion H8.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - subst. simpl in *. find_contradiction H2.
Qed.


Lemma zcb_steps_I_to_O :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (m_global_time s2) > now + period - Δ ->
    exists s s', steps s1 s /\ step s s' /\ steps s' s2 /\ In 
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.


Lemma zcb_step_I_to_O' :
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (m_global_time s1) <= now + period - Δ ->
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
      simpl in H11. inversion H11.
      case_analysis H11.
      case_analysis H14.
      * apply ltb_sound_true in H12.
        apply ltb_sound_false in H1.
        omega.
      * eexists. split; simpl.
        ** rewrite in_app_iff. right. simpl. left. eauto.
        ** repeat split; trivial. resolve_owner H6.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    unfold zcb_desc in H8. inversion H8.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    unfold zcb_desc in H8. inversion H8.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - subst. simpl in *. find_contradiction H2.
Qed.








(*




WHOAAAA

 *)



Lemma zcb_step_I_to_O'' :
  forall s1 s2 ctr_id dsc_id period I O sc ctr,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc (m_global_time s1) period) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    (m_global_time s2) > (m_global_time s1) + period - Δ ->
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
    unfold exec_ctr_in_state_with_owner in H11.
    simpl in H11. inversion H11. clear H11.
    case_analysis H3.
    case_analysis H11.
    * eexists. split.
      ** simpl. left. eauto.
      ** repeat split; trivial. resolve_owner H6.
    *  apply ltb_sound_false in H1.
       apply ltb_sound_false in H3.
       contradict H3. omega.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    unfold zcb_desc in H8. inversion H8.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    unfold zcb_desc in H8. inversion H8.
  - ctr_case_analysis ctr ctr0. subst ctr s2.
    simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - subst. simpl in *. find_contradiction H2.
Qed.


Lemma gt_implies_ge_Sn :
  forall n m,
    n > m -> n >= S m.
Admitted.

Lemma ge_implies_eq_or_gt:
  forall n m,
    n >= m -> n = m \/ n > m.
Admitted.



Lemma helper1 :
  forall s1 s2 ctr period O,
    steps s1 s2 ->
    In ctr (m_contracts s1) ->
    consistent_state s1 ->
    In (Executed (ctr_id ctr)) (m_events s2) ->
    ctr_primitive ctr = zcb_desc (m_global_time s1) period ->
    O <> 0 ->
    m_global_time s2 > m_global_time s1 + period -  Δ.
Proof.
  intros.
  induction H.
  - subst s2. find_contradiction H2.
  - assert (H' := H). assert (H'' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + induction H5; subst s2; simpl.
      ++ simpl in H2. destruct H2 as [H2 | H2]; try inversion H2.
         find_contradiction H0.
      ++ ctr_case_analysis ctr ctr0.
         simpl in H2. destruct H2 as [H2 | H2]; try contradiction. clear H2.
         unfold exec_ctr_in_state_with_owner in H11. rewrite H3 in H11.
         simpl in H11.
         case_analysis H11.
         case_analysis H14.
         ** apply ltb_sound_true in H11. auto.
         ** apply ltb_sound_false in H11.
            apply ltb_sound_false in H2.
         

    + eapply IHsteps in H. admit.
    + admit.
Admitted.


Lemma zcb_steps_I_to_O'' :
  forall s1 s2 ctr_id dsc_id period I O sc ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc (m_global_time s1) period) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    O <> 0 ->
    period - Δ > 0 ->
    (m_global_time s2) > (m_global_time s1) + period - Δ ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.
  intros.
  induction H.
  - subst. find_contradiction H2.
  - assert (H' := H). assert (H'' := H).
    apply steps_preserves_consistent_state in H'; auto.
    apply steps_effect_over_contract with (ctr := ctr) in H; trivial.
    destruct H as [H|[H|H]]; trivial.
    + eapply zcb_step_I_to_O; eauto.
    + rewrite H1 in H. simpl in H.
      eapply helper1 with (period := period) in H''; eauto.
      ++ eapply IHsteps in H''; eauto.
         destruct H'' as [tr [H'' H''']].
         eexists. split; eauto.
         eapply step_does_not_remove_transactions; eauto.
      ++ subst ctr. trivial.
      ++ subst ctr. trivial.
    + assert (C := H7). rewrite H1 in H. simpl in H.
      eapply step_preserves_consistent_state in C; eauto.
      eapply step_does_not_remove_events in H7.
      unfold consistent_state in C.
      destruct C as [_ [_ [_ [_ C]]]].
      unfold not in C.
      exfalso. eapply C; eauto.
      trivial.
Admitted.



      assert (HT := H7).
      assert (N : m_global_time s > m_global_time s1 + period + Δ).
      {
        induction H''; intros.
        - subst s0. find_contradiction H.
        - induction H8; subst s0.
          + simpl in *. destruct H as [H | H]; try inversion H.
            apply IHH'' in H; auto.


        }
      eapply timebound_steps in H; eauto.

      apply gt_implies_ge_Sn in H6.
      eapply time_passes_one_step_at_a_time in H6; eauto.
      apply ge_implies_eq_or_gt in H6.
      destruct H6 as [H6 | H6].
      ++ rewrite H6 in *.

      eapply zcb_step_I_to_O''; eauto.
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

