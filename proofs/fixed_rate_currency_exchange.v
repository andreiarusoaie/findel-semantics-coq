Load metaproperties.

(* fixed rate currency exchange *)
Definition frce_desc :=
  (And
     (Give (Scale 11 (One USD)))
     (Scale 10 (One EUR))
  ).
Ltac print_numgoals := let n := numgoals in idtac "# of goals:" n.


(* The issuer receives scale * 10 EUR from the owner (who joins) *)
Proposition frce_I_to_O :
  forall s1 s2 ctr_id dsc_id I O sc ctr t,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id frce_desc I O O sc ->
    joins O ctr s1 s2 t ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sc * 10 /\
      tr_currency tr = EUR.
Proof.
  intros.
  destruct_join H1; insert_consistent s Ss.
  - induction St; subst s'. 
    + inversion_event Ev. inconsistent H1 Ev.
    + same_ctr Ev. subst ctr0.
      execute_own ctr H9.
      inversion H9. clear H9.
      eexists; split.
      eapply steps_does_not_remove_transactions; eauto.
      simpl. subst ledger'. simpl. left. trivial.
        repeat split; trivial. resolve_owner H4.
    + same_ctr Ev. subst ctr0. not_or' ctr H6.
    + same_ctr Ev. subst ctr0. not_or' ctr H6.
    + inversion_event Ev. inconsistent H1 Ev.
    + find_contradiction Ev.
  - induction St; subst s'.
    + try inversion_event Ev; try find_contradiction_del Ev.
    + try inversion_event Ev; try find_contradiction_del Ev.
    + try inversion_event Ev; try find_contradiction_del Ev.
    + try inversion_event Ev; try find_contradiction_del Ev.
    + same_ctr_del Ev. subst ctr0. execute_own ctr H7. inversion H7.
    + try find_contradiction_del Ev.
Qed.

Print frce_I_to_O.


(* The owner receives scale * 11 USD from the issuer *)
Proposition frce_O_to_I :
  forall s1 s2 ctr_id dsc_id I O sc ctr t,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id frce_desc I O O sc ->
    joins O ctr s1 s2 t ->
    O <> 0 ->
    exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = sc * 11 /\
      tr_currency tr = USD.
Proof.
  intros.
  destruct_join H1; insert_consistent s SS.
  - induction St; subst s'.
    + inversion_event Ev. inconsistent H1 Ev.
    + same_ctr Ev. subst ctr0.
      execute_own ctr H9.
      inversion H9.
      eexists. split.
      eapply steps_does_not_remove_transactions; eauto.
      simpl. subst ledger'. simpl. right. left. trivial.
      repeat split; trivial. resolve_owner H4.
    + same_ctr Ev. subst ctr0. not_or' ctr H6.
    + same_ctr Ev. subst ctr0. not_or' ctr H6.
    + inversion_event Ev. inconsistent H1 Ev.
    + find_contradiction Ev.
  - induction St; subst s'.
    + inversion_event Ev; find_contradiction_del Ev.
    + inversion_event Ev; find_contradiction_del Ev.
    + inversion_event Ev; find_contradiction_del Ev.
    + inversion_event Ev; find_contradiction_del Ev.
    + same_ctr_del Ev. subst ctr0. execute_own ctr H7. inversion H7.
    + find_contradiction_del Ev.
Qed.

Print frce_O_to_I.
