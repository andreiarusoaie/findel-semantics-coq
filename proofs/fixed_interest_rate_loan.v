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


(* The owner can be either paid or can trigger payment *)
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
  - simpl in H3.
    destruct H3 as [H3 | H3]; try inversion H3.
    apply consistent_impl_exec in H2; auto.
    subst ctr. contradiction.
  - case_eq (ctr_eq_dec ctr0 ctr); intros; try contradiction.
    subst ctr0. simpl in *. destruct H3 as [H3 | H3].
    + unfold exec_ctr_in_state_with_owner in H10.
      rewrite H1 in H10. simpl in H10.
      case_analysis H10.
      case_analysis H14.
      * case_analysis H15.
        case_analysis H16; right; left; eexists; split; try rewrite in_app_iff; try right.
        ** simpl. left. trivial.
        ** simpl. repeat split; trivial.
           unfold can_join in H5.
           destruct H5 as [H5 | H5]; subst; simpl in *; trivial.
           subst O. contradiction.
        ** simpl. left. trivial.
        ** simpl. repeat split; trivial.
           unfold can_join in H5.
           destruct H5 as [H5 | H5]; subst; simpl in *; trivial.
           subst O. contradiction.
      * case_analysis H15.
        case_analysis H16.
        ** simpl in *. right. right.
           eexists. split; simpl.
           rewrite in_app_iff.
           right. simpl. left. trivial.
           simpl. unfold Before.
           repeat split; trivial.
           unfold can_join in H5.
           destruct H5 as [H5 | H5]; subst; simpl in *; trivial.
           subst O. contradiction.
        ** simpl in *. right. right.
           eexists. split; simpl.
           rewrite in_app_iff.
           right. simpl. left. trivial.
           simpl. unfold Before.
           repeat split; trivial.
           unfold can_join in H5.
           destruct H5 as [H5 | H5]; subst; simpl in *; trivial.
           subst O. contradiction.
    + apply consistent_impl_exec in H; auto. subst ctr. simpl in *. contradiction.
  - case_eq (ctr_eq_dec ctr0 ctr); intros; try contradiction.
    subst ctr0 ctr. simpl in *. unfold firl_description in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr0 ctr); intros; try contradiction.
    subst ctr0 ctr. simpl in *. unfold firl_description in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr0 ctr); intros; try contradiction.
    subst ctr0 ctr. simpl in *.
    simpl in *. destruct H3 as [H3 | H3]; try inversion H3.
    apply consistent_impl_exec in H; auto. contradiction.
  - simpl in *. apply consistent_impl_exec in H2; auto. subst ctr. contradiction.
Qed.


Lemma firl_steps_O_to_I :
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
  - subst s2.
    apply consistent_impl_exec in H2; auto. subst ctr. contradiction.
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
    apply consistent_impl_exec in H2; auto.
    subst ctr. contradiction.
  - case_eq (ctr_eq_dec ctr0 ctr); intros; try contradiction.
    subst ctr0. simpl in *. destruct H3 as [H3 | H3].
    + unfold exec_ctr_in_state_with_owner in H10.
      rewrite H1 in H10. simpl in H10.
      case_analysis H10.
      case_analysis H14.
      * case_analysis H15.
        case_analysis H16.
        ** left. eexists. simpl. split. left. trivial.
           repeat split; trivial. simpl. unfold can_join in H5.
           destruct H5 as [H5 | H5]; subst; simpl in *; trivial.
           subst O. contradiction.
        ** right. eexists. simpl. split. rewrite in_app_iff.
           right. simpl. right. left. trivial.
           simpl. unfold After. repeat split; trivial.
           destruct H5 as [H5 | H5]; subst; simpl in *; trivial.
           subst O. contradiction.
      * case_analysis H15.
        case_analysis H16.
        ** left. eexists. simpl. split. left. trivial.
           repeat split; trivial. simpl. unfold can_join in H5.
           destruct H5 as [H5 | H5]; subst; simpl in *; trivial.
           subst O. contradiction.
        ** right. eexists. simpl. split. rewrite in_app_iff.
           right. simpl. right. left. trivial.
           simpl. unfold After. repeat split; trivial.
           destruct H5 as [H5 | H5]; subst; simpl in *; trivial.
           subst O. contradiction.
    + apply consistent_impl_exec in H; auto. subst ctr. simpl in *. contradiction.
  - case_eq (ctr_eq_dec ctr0 ctr); intros; try contradiction.
    subst ctr0 ctr. simpl in *. unfold firl_description in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr0 ctr); intros; try contradiction.
    subst ctr0 ctr. simpl in *. unfold firl_description in H7. inversion H7.
  - case_eq (ctr_eq_dec ctr0 ctr); intros; try contradiction.
    subst ctr0 ctr. simpl in *.
    simpl in *. destruct H3 as [H3 | H3]; try inversion H3.
    apply consistent_impl_exec in H; auto. contradiction.
  - simpl in *. apply consistent_impl_exec in H2; auto. subst ctr. contradiction.
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
  - subst s2.
    apply consistent_impl_exec in H2; auto. subst ctr. contradiction.
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
