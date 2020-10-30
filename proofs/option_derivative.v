Load metaproperties.

(* An option derivative *)
Definition option_derivative (t period : Time) :=
  (And
     (Before t (Or (Give (One USD)) (Give (One EUR))))
     (After (t + period) (One GBP))
  ).


(* The owners rights *)
Lemma option_I_to_O_helper:
  forall s1 s2 t T period I O sc ctr ctr_id dsc_id,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (After (t + period) (One GBP)) I O O sc ->
    joins O ctr s1 s2 T ->
    T > t + period ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc.
Proof.
  intros.
  destruct_join H1.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction H.
    + same_ctr Ev.  subst ctr0.
      execute_own ctr H10.
      case_if H10.
      * eexists. split.
        ** eapply steps_does_not_remove_transactions; eauto.
           simpl. subst ledger'. left. eauto.
        ** repeat split; trivial. resolve_owner H5.
      * simpl in *. rewrite <- T0 in *. 
        apply ltb_sound_false in H0. contradiction H0.
    + same_ctr Ev. subst ctr0. not_or' ctr H7.
    + same_ctr Ev. subst ctr0. not_or' ctr H7.
    + inversion_event Ev. find_contradiction H.
    + find_contradiction H.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del H.
    + inversion_event Ev. find_contradiction_del H.
    + inversion_event Ev. find_contradiction_del H.
    + inversion_event Ev. find_contradiction_del H.
    + same_ctr_del Ev. subst ctr0. execute_own ctr H8. case_if H8.
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
      tr_amount tr = sc.
Proof.
  intros.
  destruct_join_gen H1.
  - insert_consistent s Ss.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + same_ctr Ev. subst ctr0.
      execute_own ctr H12.
      case_analysis H12.
      case_analysis H15.
      * apply ltb_sound_false in H0.
        apply ltb_sound_true in H12.
        omega.
      * simpl in *.
        rewrite H0, H12 in Exec; inversion Exec. clear Exec.
        subst res.
        simpl in M0.
        destruct M0 as [M0 | [M0 | M0]]; try contradiction.
        ** rewrite <- M0 in H2. inversion H2.
        ** eapply option_I_to_O_helper; eauto.
           rewrite <- M0 in J.
           rewrite <- M0. simpl.
           exact J.
    + same_ctr Ev. subst ctr0. not_or' ctr H9.
    + same_ctr Ev. subst ctr0. not_or' ctr H9.
    + inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - insert_consistent s Ss.
    destruct_deleted D.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + same_ctr_del Ev. subst ctr0.
      execute_own ctr H10.
      case_analysis H10.
      * unfold option_derivative in Exec. simpl in Exec.
        rewrite H0 in Exec. inversion Exec.
      * case_analysis H13.
    + find_contradiction_del M.
Qed.

Print option_I_to_O.


(* The issuer does not have a choice! *)
Proposition I_does_not_have_a_choice :
  forall s1 s2 s t period I O sc ctr c_id dsc_id,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (option_derivative t period) I O O sc ->
    O <> 0 ->
    O <> I -> 
    joins_in_s O ctr s1 s2 s t ->
    forall gen_ctr, generates ctr gen_ctr s I O -> ctr_owner gen_ctr <> I.
Proof.
  intros.
  destruct H3 as [s' [Ss1 [Ss2 [E | D]]]].
  - destruct_executed E.
    insert_consistent s Ss1.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + same_ctr Ev. subst ctr0.
      execute_own ctr H11.
      destruct_generates H4.
      simpl in Exec.
      case_analysis H11.
      case_analysis H14. rewrite H0, H4 in *.
      * apply ltb_sound_false in H0.
        apply ltb_sound_true in H4.
        omega.
      * subst res.
        simpl in M0.
        destruct M0 as [M0 | [M0 | M0]]; try contradiction.
        ** subst gen_ctr. simpl. trivial.
        ** subst gen_ctr. simpl. trivial.
    + same_ctr Ev. subst ctr0. not_or' ctr H8.
    + same_ctr Ev. subst ctr0. not_or' ctr H8.
    + inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - destruct_deleted D.
    insert_consistent s Ss1.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + same_ctr_del Ev. subst ctr0.
      execute_own ctr H9.
      destruct_generates H4.
      simpl in Exec.
      case_analysis H9.
      case_analysis H12; rewrite H0, H4 in *.
      * apply ltb_sound_false in H0.
        apply ltb_sound_true in H4.
        omega.
      * subst res.
        simpl in M0.
        destruct M0 as [M0 | [M0 | M0]]; try contradiction.
        ** subst gen_ctr. simpl. trivial.
        ** subst gen_ctr. simpl. trivial.
    + find_contradiction_del M.
Qed.


Print I_does_not_have_a_choice.

(* The issuer's rights: the issuer is paid if the owner joins the generated Or *)
Lemma option_O_to_I_helper:
  forall s1 s2 t I O sc ctr c_id dsc_id,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (Or (Give (One USD)) (Give (One EUR))) I O O sc ->
    joins O ctr s1 s2 t ->
    O <> 0 ->
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
    + same_ctr Ev. subst ctr0 ctr. simpl in H7. contradiction.
    + same_ctr Ev. subst ctr0.
      rewrite H0 in H10, H7. simpl in H7. inversion H7.
      unfold exec_prim_ctr_in_state_with_owner in H10.
      subst c1 c2. simpl in H10. inversion H10.
      eexists. split.
      * eapply steps_does_not_remove_transactions; eauto.
        subst ledger'. simpl. left. trivial.
      * repeat split; trivial. resolve_owner H5.
    + same_ctr Ev. subst ctr0.
      rewrite H0 in H10, H7. simpl in H7. inversion H7.
      unfold exec_prim_ctr_in_state_with_owner in H10.
      subst c1 c2. simpl in H10. inversion H10.
      eexists. split.
      * eapply steps_does_not_remove_transactions; eauto.
        subst ledger'. simpl. left. trivial.
      * repeat split; trivial. resolve_owner H5.
    + inversion_event Ev. find_contradiction M.
    + find_contradiction M.
  - insert_consistent s Ss.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + same_ctr_del Ev. subst ctr0. execute_own ctr H8. inversion H8.
    + find_contradiction_del M.
Qed.

Proposition option_O_to_I:
  forall s1 s2 t T gen_ctr period I O sc ctr c_id dsc_id,
    consistent_state s1 ->
    ctr = finctr c_id dsc_id (option_derivative t period) I O O sc ->
    joins_generated O ctr gen_ctr s1 s2 t T ->
    (ctr_primitive gen_ctr) = Or (Give (One USD)) (Give (One EUR)) ->
    O <> 0 ->
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
    + same_ctr Ev. subst  ctr0.
      execute_own ctr H11.
      case_analysis H11.
      case_analysis H14.
      * apply ltb_sound_false in H0.
        apply ltb_sound_true in H11.
        omega.
      * simpl in Exec.
        rewrite H0, H11 in Exec.  inversion Exec; clear Exec.
        subst res.
        destruct M0 as [M0 | [M0 | M0]]; try contradiction.
        ** eapply option_O_to_I_helper; eauto.
           rewrite <- M0 in *.
           simpl.  exact J.
        ** rewrite <- M0 in H2. simpl in H2. inversion H2.
    + same_ctr Ev. subst  ctr0. not_or' ctr H8.
    + same_ctr Ev. subst  ctr0. not_or' ctr H8.
    + inversion_event Ev.  find_contradiction M.
    + find_contradiction M.
  - insert_consistent s Ss.
    destruct_deleted D.
    insert_consistent s' St.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + inversion_event Ev. find_contradiction_del M.
    + same_ctr_del Ev. subst ctr0.
      execute_own ctr H9.
      case_analysis H9.
      * simpl in Exec. rewrite H0 in Exec. inversion Exec.
      * case_analysis H12.
    + find_contradiction_del M.
Qed.

Print option_O_to_I.
