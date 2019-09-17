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



(* The owner's rights *)


Definition executed
           (ctr : FinContract)
           (s s' : State)
           (at_ : Time) :=
  exists s s',
    step s s' /\
    In ctr (m_contracts s) /\
    In (Executed (ctr_id ctr)) (m_events s') /\
    at_ = m_global_time s.

Definition joins
           (O : Address)
           (ctr : FinContract)
           (s1 s2 : State)
           (at_ : Time) :=
  exists s s', steps s1 s /\ steps s' s2 /\ executed ctr s s' at_.
Print Result.
Print execute.
Definition generates
           (ctr new_ctr : FinContract) (s : State) (O : Address) :=
  exists result,
    execute (ctr_primitive ctr) (ctr_scale ctr) (ctr_issuer ctr) O
            (m_balance s) (m_global_time s) (m_gateway s) (ctr_id ctr)
            (ctr_desc_id ctr) (m_fresh_id s) (m_ledger s) = Some result /\
    In new_ctr (res_contracts result).

Definition joins_generated
           (O : Address)
           (ctr : FinContract)
           (s1 s2 : State)
           (t_first t_second : Time) :=
  exists s s' new_ctr, steps s1 s /\ steps s' s2 /\ executed ctr s s' t_first /\
               joins O new_ctr s' s2 t_second /\ generates ctr new_ctr s O.


Lemma oups:
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (zcb_desc now period) I O O sc ->
    joins_generated O ctr s1 s2 now (now + period) ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.


(* Definition is_generated *)
(*            (child parent : FinContract) *)
(*            (s1 s2 : State) *)
(*            (proposed_owner : Address) *)
(*            (at_ : Time) := *)
(*   exists s s' bal' ctrs' next' ledger', *)
(*     steps s1 s /\ *)
(*     step s s' /\ *)
(*     steps s' s2 /\ *)
(*     In parent (m_contracts s) /\ *)
(*     ~ In (Executed (ctr_id ctr)) (m_events s') /\  *)
(*     execute (ctr_primitive parent) (ctr_scale parent) (ctr_issuer parent) proposed_owner *)
(*             (m_balance s) (m_global_time s) (m_gateway s) (ctr_id parent)  *)
(*             (ctr_desc_id parent) (m_fresh_id s) (m_ledger s) = *)
(*     Some (result bal' ctrs' next' ledger') /\ *)
(*     In child ctrs' /\ at_ = m_global_time s. *)

    
(*     p_owner <> 0 /\ *)


Lemma oups:
  forall s1 s2 ctr_id dsc_id now period I O sc ctr,
    consistent_state s1 ->
    O <> 0 ->
    (exists new_ctr, is_generated_and_executed new_ctr ctr s1 s2 O now) ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 11.
Proof.
  intros.
  destruct H3 as [new_ctr H3].
  destruct H as (s & s' & S1 & S & S2 & IN & OW & E).
  induction S; subst s'.
  - simpl in E. destruct E as [E | E]; try inversion E.
    find_contradiction IN.
    eapply steps_preserves_consistent_state; eauto.
  - ctr_case_analysis ctr ctr0.
    unfold exec_ctr_in_state_with_owner in H9.
    rewrite H1 in H9. simpl in H9.
    case_analysis H9.
    case_analysis H13.
    + eexists. split.
      eapply steps_does_not_remove_transactions.
      exact S2. simpl. subst ledger'. simpl. left. eauto.
      repeat split; eauto. simpl. resolve_owner H4.
    + destruct H3 as (gs & gs' & bal' & ctrs'' & x' & L & G1 & GS & G2 & GIN & EXEC & GEN & L').
      rewrite H1 in EXEC. simpl in EXEC.
      case_analysis EXEC.
      case_analysis H13.
      ++ eexists. split.
         eapply steps_does_not_remove_transactions.
         exact G2. simpl. subst ledger'. simpl. right. left. eauto.
      repeat split; eauto. simpl. resolve_owner H4.


Admitted. 



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

