Load metaproperties.

Definition option_derivative (t period : Time) :=
  (And
     (Before t (Give (Or (One USD) (One EUR))))
     (After (t + period) (Scale 2 (One EUR)))
  ).


(* The owners rights *)
Lemma option_I_to_O_helper:
  forall s1 s2 t T period I O sc ctr ctr_id dsc_id,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (After (t + period) (Scale 2 (One EUR))) I O O sc ->
    joins O ctr s1 s2 T ->
    T > t + period ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 2.
Proof.
  intros.
  destruct_join H1.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction H.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H10.
      case_if H10.
      case_if H13.
      * eexists. split.
        ** eapply steps_does_not_remove_transactions; eauto.
           simpl. subst ledger'. left. eauto.
        ** repeat split; trivial. resolve_owner H5.
      * simpl in *. rewrite <- T0 in *.
        apply ltb_sound_false in H10. contradiction H10.
    + not_or ctr ctr0 H7.
    + not_or ctr ctr0 H7.
    + inversion_event Ev. find_contradiction H.
    + find_contradiction H.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del H.
    + inversion_event Ev. find_contradiction_del H.
    + not_or ctr ctr0 H7.
    + not_or ctr ctr0 H7.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H8.
      case_if H8.
      * apply ltb_sound_true in H0.
        apply Nat.lt_asymm in H0.
        contradict H0. apply infinite.
      * case_if H11.
    + find_contradiction_del H.
Qed.

Proposition option_I_to_O :
  forall s1 s2 t T gen_ctr period I O sc ctr c_id dsc_id,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (option_derivative t period) I O O sc ->
    joins_generated O ctr gen_ctr s1 s2 t T ->
    (ctr_primitive gen_ctr) = After (t + period) (Scale 2 (One EUR)) ->
    T > t + period ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = (ctr_id gen_ctr) /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 2.
Proof.
  intros.
  destruct_join_gen H1.
  - insert_consistent s Ss.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H12.
      case_analysis H12.
      case_analysis H15.
      * case_analysis H16.
        case_analysis H17; simpl in *;
          rewrite H0, H12, H14, H15 in Exec; inversion Exec; clear Exec;
            rewrite <- H17 in M0; simpl in M0.
        ** destruct M0 as [M0 | M0]; try contradiction.
           rewrite <- M0 in H2. simpl in H2. inversion H2.
        ** destruct M0 as [M0 | [M0 | M0]]; try contradiction.
           *** rewrite <- M0 in H2. simpl in H2. inversion H2.
           *** eapply option_I_to_O_helper; eauto.
               rewrite <- M0 in J.
               rewrite <- M0. simpl.               
               exact J.
      * case_analysis H16.
        case_analysis H17; simpl in *;
          rewrite H0, H12, H14, H15 in Exec; inversion Exec; clear Exec;
            rewrite <- H17 in M0; simpl in M0.
        ** destruct M0 as [M0 | M0]; try contradiction.
           rewrite <- M0 in H2. simpl in H2. inversion H2.
        ** destruct M0 as [M0 | [M0 | M0]]; try contradiction.
           *** rewrite <- M0 in H2. simpl in H2. inversion H2.
           *** eapply option_I_to_O_helper; eauto.
               rewrite <- M0 in J.
               rewrite <- M0. simpl.               
               exact J.
    + not_or ctr ctr0 H9.
    + not_or ctr ctr0 H9.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - insert_consistent s Ss.
    destruct_deleted D.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + not_or ctr ctr0 H9.
    + not_or ctr ctr0 H9.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H10.
      case_analysis H10.
      * unfold option_derivative in Exec. simpl in Exec.
        rewrite H0 in Exec. inversion Exec.
      * case_analysis H13.
        ** case_analysis H14.
           *** unfold option_derivative in Exec. simpl in Exec.
               rewrite H0, H10, H12 in Exec. inversion Exec.
           *** case_analysis H15.
        ** case_analysis H15.
           *** unfold option_derivative in Exec. simpl in Exec.
               rewrite H0, H10, H12 in Exec. inversion Exec.
           *** case_analysis H15.
    + find_contradiction_del M.
Qed.

Print option_I_to_O.


(* The issuer does have an option!  *)
Proposition I_does_have_a_choice :
  forall s1 s2 s' t period I O sc ctr c_id dsc_id,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (option_derivative t period) I O O sc ->
    O <> 0 ->
    t > 0 -> 
    joins_at_s' O ctr s1 s2 s' t ->
    exists gen_ctr,
      In gen_ctr (m_contracts s') /\
      ctr_primitive gen_ctr = Or (One USD) (One EUR) /\
      ctr_issuer gen_ctr = O /\
      ctr_owner gen_ctr = I.
Proof.
  intros.
  destruct H3 as [s [Ss1 [Ss2 [E | D]]]].
  - insert_consistent s Ss1.
    destruct_executed E.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0. simpl.
      execute_own ctr H10.
      case_analysis H10.
      case_analysis H13.
      * case_analysis H14.
        case_analysis H15; subst ctrs'; eexists; split.
        ** rewrite in_app_iff. right.  simpl. left. trivial.
        ** repeat split; trivial. resolve_owner H5.
        ** rewrite in_app_iff. right. simpl. left. trivial.
        ** repeat split; trivial. resolve_owner H5.
      * case_analysis H14.
        case_analysis H15.
        ** subst t. apply ltb_sound_true in H13. contradict H13. omega.
        ** subst t. apply ltb_sound_false in H10. contradict H10. omega.
    + not_or ctr ctr0 H7.
    + not_or ctr ctr0 H7.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - insert_consistent s Ss1.
    destruct_deleted D.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction_del M.
    + not_or ctr ctr0 H7.
    + not_or ctr ctr0 H7.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H8.
      case_analysis H8.
      * subst t. apply ltb_sound_true in H0. contradict H0. omega.
      * case_analysis H11.
        ** case_analysis H12.
           ***  apply ltb_sound_true in H10.
                apply Nat.lt_asymm in H10.
                contradict H10. apply infinite.
           *** case_analysis H13.
        ** case_analysis H12.
           ***  apply ltb_sound_true in H10.
                apply Nat.lt_asymm in H10.
                contradict H10. apply infinite.
           *** case_analysis H13.
    + find_contradiction_del M.
Qed.     

Print I_does_have_a_choice.


(* The issuer's rights: the issuer is paid if he joins twice *)
Lemma option_O_to_I_helper:
  forall s1 s2 t I O sc ctr c_id dsc_id,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (Or (One USD) (One EUR)) O I I sc ->
    joins I ctr s1 s2 t ->
    I <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = c_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc.
Proof.
  intros.
  destruct_join H1.
  - insert_consistent s Ss.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0. subst ctr. simpl in H7. contradiction.
    + ctr_case_analysis ctr ctr0.
      rewrite H0 in H10, H7. simpl in H7. inversion H7.
      unfold exec_prim_ctr_in_state_with_owner in H10.
      subst c1 c2. simpl in H10. inversion H10.
      eexists. split.
      * eapply steps_does_not_remove_transactions; eauto.
        subst ledger'. simpl. left. trivial.
      * repeat split; trivial. resolve_owner H5.
    + ctr_case_analysis ctr ctr0.
      rewrite H0 in H10, H7. simpl in H7. inversion H7.
      unfold exec_prim_ctr_in_state_with_owner in H10.
      subst c1 c2. simpl in H10. inversion H10.
      eexists. split.
      * eapply steps_does_not_remove_transactions; eauto.
        subst ledger'. simpl. left. trivial.
      * repeat split; trivial. resolve_owner H5.
    + ctr_case_analysis ctr ctr0. execute_own ctr H8. inversion H8.
    + find_contradiction M.
  - insert_consistent s Ss.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + ctr_case_analysis ctr ctr0. subst ctr. simpl in H7. contradiction.
    + simpl in Ev. inversion_event Ev. find_contradiction_del M.
    + simpl in Ev. inversion_event Ev. find_contradiction_del M.
    + ctr_case_analysis ctr ctr0. execute_own ctr H8. inversion H8.
    + find_contradiction_del M.
Qed.

Proposition option_O_to_I:
  forall s1 s2 t T gen_ctr period I O sc ctr c_id dsc_id,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (option_derivative t period) I O O sc ->
    joins_generated' O I ctr gen_ctr s1 s2 t T ->
    (ctr_primitive gen_ctr) = Or (One USD) (One EUR) ->
    O <> 0 ->
    I <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = (ctr_id gen_ctr) /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc.
Proof.
  intros.
  destruct_join_gen H1.
  - insert_consistent s Ss.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H12.
      case_analysis H12.
      case_analysis H15.
      * case_analysis H16.
        case_analysis H17.
        ** subst t. apply ltb_sound_true in H15. contradict H15. omega.
        ** simpl in Exec. rewrite H0, H12, H14, H15 in Exec.
           inversion Exec. subst res. simpl in *.
           destruct M0 as [M0 | [M0 | M0]]; try contradiction.
           *** eapply option_O_to_I_helper in J; auto; rewrite <- M0. simpl.
               exact J. eauto.
           *** rewrite <- M0 in H2. simpl in H2. inversion H2.
      * case_analysis H15.
        case_analysis H16.
        ** subst t. apply ltb_sound_true in H15. contradict H15. omega.
        ** simpl in Exec. rewrite H0, H12, H14, H15 in Exec.
           inversion Exec. subst res. simpl in *.
           destruct M0 as [M0 | [M0 | M0]]; try contradiction;
             rewrite <- M0 in H2; simpl in H2; inversion H2.
    + not_or ctr ctr0 H9.
    + not_or ctr ctr0 H9.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - insert_consistent s Ss.
    destruct_deleted D.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + not_or ctr ctr0 H9.
    + not_or ctr ctr0 H9.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H10.
      case_analysis H10.
      * simpl in Exec. rewrite H0 in Exec. inversion Exec.
      * case_analysis H13;
         case_analysis H14; try case_analysis H15;
           apply ltb_sound_true in H12;
           apply Nat.lt_asymm in H12;
           contradict H12; eapply infinite.
    + find_contradiction_del M.
Qed.

Print option_O_to_I.
