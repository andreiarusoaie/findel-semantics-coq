Load metaproperties.

(* firl = fixed interest rate loan *)
Definition firl_description (t : Time) :=
  (And
     (Before t (Or (Give (One USD)) (Give (One EUR))))
     (After (t + 2) (Scale 2 (One EUR)))
  ).


Lemma firl_generates_contracts :
  forall t scale I O balance time gtw ctr_id dsc_id next_id ledger result,
    execute (firl_description t) scale I O balance time
            gtw ctr_id dsc_id next_id ledger = Some result
    ->
    res_contracts result <> [].
Proof.
  intros.
  unfold firl_description in H.
  simpl in H.
  case_analysis H; case_analysis H2; case_analysis H3; case_analysis H4;
    simpl; unfold not; intros H'; inversion H'.
Qed.


(* Without time constraints on states anything can happen:
 - the contract is executed, the owner joins and a payment is made
 - the contract is executed, but the owner does not join
 - the contract is postponed due to time boundaries imposed by Timebound
 *)
Lemma firl_step_O_to_I :
  forall s1 s2 t I O sc ctr ctr_id dsc_id,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (firl_description t) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) -> 
    O <> 0 ->
    (exists tr,
        In tr (m_ledger s2) /\
        tr_from tr = O /\
        tr_to tr = I /\
        tr_amount tr = sc) \/
    (exists ctr,
        In ctr (m_contracts s2) /\
        ctr_primitive ctr = (Or (Give (One USD)) (Give (One EUR))) /\
        ctr_issuer ctr = I /\
        ctr_proposed_owner ctr = O /\
        ctr_scale ctr = sc) \/
    (exists ctr,
        In ctr (m_contracts s2) /\
        ctr_primitive ctr = (Before t (Or (Give (One USD)) (Give (One EUR)))) /\
        ctr_issuer ctr = I /\
        ctr_proposed_owner ctr = O /\
        ctr_scale ctr = sc).
Proof.
  intros.
  induction H; subst s2.
  - simpl in H3. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - ctr_case_analysis ctr ctr0.
    simpl in *. destruct H3 as [H3 | H3].
    + unfold exec_ctr_in_state_with_owner in H10.
      rewrite H1 in H10. simpl in H10.
      case_analysis H10.
      case_analysis H14.
      * case_analysis H15.
        case_analysis H16; right; left; eexists; split; try rewrite in_app_iff; try right.
        ** simpl. left. trivial.
        ** simpl. repeat split; trivial.
           resolve_owner H5.
        ** simpl. left. trivial.
        ** simpl. repeat split; trivial.
           resolve_owner H5.
      * case_analysis H15.
        case_analysis H16.
        ** simpl in *. right. right.
           eexists. split; simpl.
           rewrite in_app_iff.
           right. simpl. left. trivial.
           simpl. unfold Before.
           repeat split; trivial.
           resolve_owner H5.
        ** simpl in *. right. right.
           eexists. split; simpl.
           rewrite in_app_iff.
           right. simpl. left. trivial.
           simpl. unfold Before.
           repeat split; trivial.
           resolve_owner H5.
    + apply consistent_impl_exec in H; auto. subst ctr. simpl in *. contradiction.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *. unfold firl_description in H7. inversion H7.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *. unfold firl_description in H7. inversion H7.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *.
    simpl in *. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - simpl in *. find_contradiction H2.
Qed.


Theorem firl_steps_O_to_I :
  forall s1 s2 t I O sc ctr ctr_id dsc_id,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (firl_description t) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) -> 
    O <> 0 ->
    (exists tr,
        In tr (m_ledger s2) /\
        tr_from tr = O /\
        tr_to tr = I /\
        tr_amount tr = sc) \/
    (exists ctr,
        In ctr (m_contracts s2) /\
        ctr_primitive ctr = (Or (Give (One USD)) (Give (One EUR))) /\
        ctr_issuer ctr = I /\
        ctr_proposed_owner ctr = O /\
        ctr_scale ctr = sc) \/
    (exists ctr,
        In ctr (m_contracts s2) /\
        ctr_primitive ctr = (Before t (Or (Give (One USD)) (Give (One EUR)))) /\
        ctr_issuer ctr = I /\
        ctr_proposed_owner ctr = O /\
        ctr_scale ctr = sc).
Proof.
  intros.
  induction H.
  - subst s2. find_contradiction H2.
  - assert (HC := H). assert (HC' := H5).
    eapply steps_effect_over_contract in H; eauto.
    destruct H as [H | [H | H]].
    + eapply firl_step_O_to_I; eauto.
      eapply steps_preserves_consistent_state; eauto.
    + rewrite H1 in H. simpl in H.  apply IHsteps in H.
      destruct H as [H | [H | H]].
      ++ left. destruct H as [tr [H H']].
         exists tr. split; trivial.
         eapply step_does_not_remove_transactions; eauto.
      ++ destruct H as [ct [H H']].
         case_eq (ctr_eq_dec ct ctr); intros.
         +++ destruct H' as [H' H'']. subst ctr ct. simpl in H'.
             unfold firl_description in H'. inversion H'.
         +++ contradiction.
      ++ destruct H as [ct [H H']].
         case_eq (ctr_eq_dec ct ctr); intros.
         +++ destruct H' as [H' H'']. subst ctr ct. simpl in H'.
             unfold firl_description in H'. inversion H'.
         +++ contradiction.
    + eapply step_does_not_remove_events in H5.
      exfalso.
      apply steps_preserves_consistent_state in HC; auto.
      apply step_preserves_consistent_state in HC'; auto.
      destruct HC' as [_ [_ [_ [_ HC']]]].
      eapply HC'; eauto.
      subst ctr. simpl in *. trivial.
Qed.



(* If the time on s2 is >= t, then a contract has been generated;
the owner can now demand the execution of this contract;
no payment is done in one step!
 *)
Lemma firl_step_O_to_I' :
  forall s1 s2 t I O sc ctr ctr_id dsc_id,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (firl_description t) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    (m_global_time s2) >= t ->
    t > 0 -> 
    O <> 0 ->
    (exists ctr,
        In ctr (m_contracts s2) /\
        ctr_primitive ctr = (Or (Give (One USD)) (Give (One EUR))) /\
        ctr_issuer ctr = I /\
        ctr_proposed_owner ctr = O /\
        ctr_scale ctr = sc).
Proof.
  intros.
  induction H; subst s2.
  - simpl in H3. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - ctr_case_analysis ctr ctr0.
    simpl in *. destruct H3 as [H3 | H3].
    + unfold exec_ctr_in_state_with_owner in H12.
      rewrite H1 in H12. simpl in H12.
      case_analysis H12.
      case_analysis H16.
      * case_analysis H17.
        case_analysis H18.
        ** apply ltb_sound_false in H14.
           apply ltb_sound_true in H16.
           contradict H14. omega.
        ** eexists. split. rewrite in_app_iff. 
           simpl. right. left. eauto.
           repeat split; trivial.
           simpl. resolve_owner H7.
      * case_analysis H17.
        case_analysis H18.
        ** apply ltb_sound_false in H12.
           apply ltb_sound_true in H16.
           contradict H12. omega.
        ** clear H20.
           apply ltb_sound_false in H16.
           apply ltb_sound_false in H14.
           apply ltb_sound_false in H12.
           contradict H14. omega.
    + find_contradiction H.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *. unfold firl_description in H9. inversion H9.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *. unfold firl_description in H9. inversion H9.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *.
    simpl in *. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - simpl in *. find_contradiction H2.
Qed.


(* If the time of s1 is > 0, then (Before t ...) is executed *)
Lemma firl_step_O_to_I'' :
  forall s1 s2 t I O sc ctr ctr_id dsc_id,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (firl_description t) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    (m_global_time s1) > 0 ->
    O <> 0 ->
    (exists tr,
        In tr (m_ledger s2) /\
        tr_from tr = O /\
        tr_to tr = I /\
        tr_amount tr = sc) \/
    (exists ctr,
        In ctr (m_contracts s2) /\
        ctr_primitive ctr = (Or (Give (One USD)) (Give (One EUR))) /\
        ctr_issuer ctr = I /\
        ctr_proposed_owner ctr = O /\
        ctr_scale ctr = sc).
Proof.
  intros.
  induction H; subst s2.
  - simpl in H3. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - ctr_case_analysis ctr ctr0.
    simpl in *. destruct H3 as [H3 | H3].
    + unfold exec_ctr_in_state_with_owner in H11.
      rewrite H1 in H11. simpl in H11.
      case_analysis H11.
      case_analysis H15.
      * case_analysis H16.
        case_analysis H17; right; eexists; split; try rewrite in_app_iff.
        ** right. simpl. left. trivial.
        ** simpl. repeat split; trivial.
           resolve_owner H6.
        ** right. simpl. left. trivial.
        ** simpl. repeat split; trivial.
           resolve_owner H6.
      * apply ltb_sound_false in H11. contradict H11. auto.
    + find_contradiction H.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *. unfold firl_description in H8. inversion H8.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *. unfold firl_description in H8. inversion H8.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *.
    simpl in *. destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - simpl in *. find_contradiction H2.
Qed.


Theorem firl_steps_O_to_I'' :
  forall s1 s2 t I O sc ctr ctr_id dsc_id,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (firl_description t) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) ->
    (m_global_time s1) > 0 ->
    O <> 0 ->
    (exists tr,
        In tr (m_ledger s2) /\
        tr_from tr = O /\
        tr_to tr = I /\
        tr_amount tr = sc) \/
    (exists ctr,
        In ctr (m_contracts s2) /\
        ctr_primitive ctr = (Or (Give (One USD)) (Give (One EUR))) /\
        ctr_issuer ctr = I /\
        ctr_proposed_owner ctr = O /\
        ctr_scale ctr = sc).
Proof.
  intros.
  induction H.
  - subst s2. find_contradiction H2.
  - assert (HC := H). assert (HI := H). assert (HC' := H5).
    eapply steps_effect_over_contract in H; eauto.
    eapply steps_preserves_consistent_state in HI; eauto.
    destruct H as [H | [H | H]].
    + eapply firl_step_O_to_I''; eauto.
      eapply time_inc_steps in HC.
      omega.
    + rewrite H1 in H. simpl in H.
      apply IHsteps in H.
      destruct H as [H | H].
      * destruct H as [tr [H H']].
        left. exists tr.
        split; trivial.
        eapply step_does_not_remove_transactions; eauto.
      * destruct H as [ctr' [H H']].
        induction H6.
        ** subst s2. 
           right. exists ctr'.
           split; trivial.
           simpl. right. trivial.
        ** ctr_case_analysis ctr' ctr0.
           subst s2. simpl in *.
           unfold exec_ctr_in_state_with_owner in H12.
           destruct H' as [A [B [C D]]].
           rewrite A, B, D in H12.
           simpl in H12. inversion H12. clear H12.
           right.  eexists. split. rewrite in_app_iff. right.
           simpl. left. trivial.
           simpl. repeat split; trivial.
           resolve_owner H7.
        ** ctr_case_analysis ctr' ctr0.
           unfold exec_prim_ctr_in_state_with_owner in H12.
           destruct H' as [A [B [C D]]].
           rewrite A in H9.
           inversion H9.
           subst c1.
           simpl in H12. inversion H12. clear H12.
           left. eexists. subst s2 ledger'. simpl.
           split; eauto. simpl. repeat split; trivial.
           resolve_owner H7.
        ** ctr_case_analysis ctr' ctr0.
           unfold exec_prim_ctr_in_state_with_owner in H12.
           destruct H' as [A [B [C D]]].
           rewrite A in H9.
           inversion H9.
           subst c2.
           simpl in H12. inversion H12. clear H12.
           left. eexists. subst s2 ledger'. simpl.
           split; eauto. simpl. repeat split; trivial.
           resolve_owner H7.
        ** ctr_case_analysis ctr' ctr0.
           subst s2.
           unfold exec_ctr_in_state_with_owner in H10.
           destruct H' as [A [B [C D]]].
           rewrite A in H10. inversion H10.
        ** subst s2. simpl in *. right. exists ctr'. split; trivial.
    + apply step_does_not_remove_events with (s' := s2) in H; auto.
      exfalso.
      apply steps_preserves_consistent_state in HC; auto.
      eapply step_preserves_consistent_state in HI; eauto.
      destruct HI as [_ [_ [_ [_ HI]]]].
      eapply HI; eauto.
      subst ctr. simpl in *. eauto.
Qed.

(* Owner's rights without time constraints over states:
 - if the contract is executed and the owner joins the generated
   contract, then a payment from I to O is registered;
 - if the contract is executed, the owner can ask for its execution
   later; *)
Lemma firl_step_I_to_O :
  forall s1 s2 t I O sc ctr ctr_id dsc_id,
    step s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (firl_description t) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) -> 
    O <> 0 ->
    (exists tr,
        In tr (m_ledger s2) /\
        tr_from tr = I /\
        tr_to tr = O /\
        tr_amount tr = sc * 2) \/
    (exists ctr,
        In ctr (m_contracts s2) /\
        ctr_primitive ctr = After (t + 2) (Scale 2 (One EUR)) /\
        ctr_issuer ctr = I /\
        ctr_proposed_owner ctr = O /\
        ctr_scale ctr = sc).
Proof.
  intros.
  induction H; subst s2.
  - simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H2.
  - ctr_case_analysis ctr ctr0.
    simpl in *. destruct H3 as [H3 | H3].
    + unfold exec_ctr_in_state_with_owner in H10.
      rewrite H1 in H10. simpl in H10.
      case_analysis H10.
      case_analysis H14.
      * case_analysis H15.
        case_analysis H16.
        ** left. eexists. simpl. split. left. trivial.
           repeat split; trivial. simpl.
           resolve_owner H5.
        ** right. eexists. simpl. split. rewrite in_app_iff.
           right. simpl. right. left. trivial.
           simpl. unfold After. repeat split; trivial.
           resolve_owner H5.
      * case_analysis H15.
        case_analysis H16.
        ** left. eexists. simpl. split. left. trivial.
           repeat split; trivial. simpl.
           resolve_owner H5.
        ** right. eexists. simpl. split. rewrite in_app_iff.
           right. simpl. right. left. trivial.
           simpl. unfold After. repeat split; trivial.
           resolve_owner H5.
    + apply consistent_impl_exec in H; auto. subst ctr. simpl in *. contradiction.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *. unfold firl_description in H7. inversion H7.
  - ctr_case_analysis ctr ctr0.
    subst ctr. simpl in *. unfold firl_description in H7. inversion H7.
  - ctr_case_analysis ctr ctr0. 
    subst ctr. simpl in *.
    simpl in *. 
    destruct H3 as [H3 | H3]; try inversion H3.
    find_contradiction H3.
  - simpl in *. find_contradiction H2.
Qed.


Lemma firl_steps_I_to_O :
  forall s1 s2 t I O sc ctr ctr_id dsc_id,
    steps s1 s2 ->
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (firl_description t) I O O sc ->
    In ctr (m_contracts s1) ->
    In (Executed ctr_id) (m_events s2) -> 
    O <> 0 ->
    (exists tr,
        In tr (m_ledger s2) /\
        tr_from tr = I /\
        tr_to tr = O /\
        tr_amount tr = sc * 2) \/
    (exists ctr,
        In ctr (m_contracts s2) /\
        ctr_primitive ctr = After (t + 2) (Scale 2 (One EUR)) /\
        ctr_issuer ctr = I /\
        ctr_proposed_owner ctr = O /\
        ctr_scale ctr = sc).
Proof.
  intros.
  induction H.
  - subst s2. find_contradiction H2.
  - assert (HC := H). assert (HC' := H5).
    eapply steps_effect_over_contract in H; eauto.
    destruct H as [H | [H | H]].
    + eapply firl_step_I_to_O; eauto.
      eapply steps_preserves_consistent_state; eauto.
    + rewrite H1 in H. simpl in H.  apply IHsteps in H.
      destruct H as [H | H].
      ++ left. destruct H as [tr [H H']].
         exists tr. split; trivial.
         eapply step_does_not_remove_transactions; eauto.
      ++ destruct H as [ct [H H']].
         case_eq (ctr_eq_dec ct ctr); intros.
         +++ destruct H' as [H' H'']. subst ctr ct. simpl in H'.
             unfold firl_description in H'. inversion H'.
         +++ contradiction.
    + eapply step_does_not_remove_events in H5.
      exfalso.
      apply steps_preserves_consistent_state in HC; auto.
      apply step_preserves_consistent_state in HC'; auto.
      destruct HC' as [_ [_ [_ [_ HC']]]].
      eapply HC'; eauto.
      subst ctr. simpl in *. trivial.
Qed.
