Load metaproperties.

(* ERCE : External rate currency exchange *)
Definition erce_desc (addr : Address) :=
  (And
     (Give (One EUR))
     (ScaleObs addr (One USD))
  ).


Proposition frce_I_to_O :
  forall s1 s2 s ctr_id dsc_id I O sc ctr t addr r,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (erce_desc addr) I O O sc ->
    joins_in_s O ctr s1 s2 s t ->
    O <> 0 ->
    query (m_gateway s) addr t = Some r ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * r /\
      tr_currency tr = USD).
Proof.
  intros.
  destruct H1 as [s' [Ss1 [Ss2 [E | D]]]].
  - destruct_executed E.
    insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction Ev.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H10. subst t. rewrite H3 in *.
      inversion H10. subst. clear H10.
      eexists. split.
      eapply steps_does_not_remove_transactions; eauto.
      simpl. left. trivial.
      repeat split; trivial. resolve_owner H5.
    + not_or ctr ctr0 H7.
    + not_or ctr ctr0 H7.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction Ev.
    + find_contradiction Ev.
  - destruct_deleted D.
    insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del Ev.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction_del Ev.
    + not_or ctr ctr0 H7.
    + not_or ctr ctr0 H7.
    + ctr_case_analysis ctr ctr0. execute_own ctr H8.
      subst t. rewrite H3 in *. inversion H8.
    + find_contradiction_del Ev.
Qed.


Print frce_I_to_O.


Proposition frce_O_to_I :
  forall s1 s2 s ctr_id dsc_id I O sc ctr t addr r,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (erce_desc addr) I O O sc ->
    joins_in_s O ctr s1 s2 s t ->
    O <> 0 ->
    query (m_gateway s) addr t = Some r ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc /\
      tr_currency tr = EUR).
Proof.
  intros.
  destruct H1 as [s' [Ss1 [Ss2 [E | D]]]].
  - destruct_executed E.
    insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction Ev.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H10. subst t. rewrite H3 in *.
      inversion H10. subst. clear H10.
      eexists. split.
      eapply steps_does_not_remove_transactions; eauto.
      simpl. right. left. trivial.
      repeat split; trivial. resolve_owner H5.
    + not_or ctr ctr0 H7.
    + not_or ctr ctr0 H7.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction Ev.
    + find_contradiction Ev.
  - destruct_deleted D.
    insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del Ev.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction_del Ev.
    + not_or ctr ctr0 H7.
    + not_or ctr ctr0 H7.
    + ctr_case_analysis ctr ctr0. execute_own ctr H8.
      subst t. rewrite H3 in *. inversion H8.
    + find_contradiction_del Ev.
Qed.

Print frce_O_to_I.


(* A failed external query implies no changes in the ledger *)
Proposition failed_gateway_query_preserves_ledger :
  forall s s' ctr_id dsc_id I O sc ctr t addr,
    ((executed ctr s s' t) \/ (deleted ctr s s' t)) -> 
    consistent_state s ->
    ctr = finctr ctr_id dsc_id (erce_desc addr) I O O sc ->
    O <> 0 ->
    query (m_gateway s) addr t = None ->
    m_ledger s = m_ledger s'.
Proof.
  intros *.
  intros [E | D] C CT NA H.
  - destruct_executed E.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H6. subst t. rewrite H in *.
      inversion H6.
    + not_or ctr ctr0 H3.
    + not_or ctr ctr0 H3.
    + simpl. trivial.
    + simpl. trivial.
  - destruct_deleted D.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction M.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H6. subst t. rewrite H in *.
      inversion H6.
    + not_or ctr ctr0 H3.
    + not_or ctr ctr0 H3.
    + simpl. trivial.
    + simpl. trivial.
Qed.

Print failed_gateway_query_preserves_ledger.
