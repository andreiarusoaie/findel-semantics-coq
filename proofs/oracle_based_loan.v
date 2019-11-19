Load metaproperties.
Definition PayWithPenalty (sum : nat)
           (penalty_addr : Address) :=
  (And
     (Scale sum (One USD))
     (ScaleObs penalty_addr (One USD))).

Definition PenaltyCtr (sum : nat)
           (oracle_payment_check penalty_addr : Address) :=
  (If (oracle_payment_check)
      Zero
      (Give (PayWithPenalty sum penalty_addr))).

Definition Oracle_based_loan
           (sum : nat) (now period : nat)
           (oracle_salary_check
              oracle_payment_check
              penalty_addr : Address) :=
  If oracle_salary_check
     (And
        (Give (Scale sum (One USD)))
        (Give
           (After (now + period)
                  (PenaltyCtr sum oracle_payment_check penalty_addr))))
     Zero.

Check query.
Proposition PayWithPenalty_I_to_O :
  forall s1 s2 s ctr_id dsc_id I O ctr t sum penalty_addr penalty,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (PayWithPenalty sum penalty_addr) I O O 1 ->
    joins_in_s O ctr s1 s s2 t ->
    O <> 0 ->
    query (m_gateway s1) penalty_addr t = Some penalty ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sum)  /\ 
    exists tr',
      In tr' (m_ledger s2) /\
      tr_ctr_id tr' = ctr_id /\
      tr_from tr' = I /\
      tr_to tr' = O /\
      tr_amount tr' = penalty.
Proof.
  intros.
  destruct_join_in_s H1.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction Ev.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H10. clear H11. subst t.
      case_match H10; try inversion H10.
      destruct r. inversion H12. clear H12. subst.
      case_match H0; try inversion H0. subst.
      inversion H13. subst. clear H13.
      split; eexists; split. 
      * eapply steps_does_not_remove_transactions; eauto.
        simpl. subst ledger'. left. trivial.
      repeat split; trivial. resolve_owner H4.
    + not_or ctr ctr0 H6.
    + not_or ctr ctr0 H6.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction Ev.
    + find_contradiction Ev.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del Ev.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction_del Ev.
    + not_or ctr ctr0 H6.
    + not_or ctr ctr0 H6.
    + ctr_case_analysis ctr ctr0. execute_own ctr H7. inversion H7.
    + find_contradiction_del Ev.
Qed.


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
  destruct_join H1.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction Ev.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H9.
      inversion H9.
      eexists. split.
      eapply steps_does_not_remove_transactions; eauto.
      simpl. subst ledger'. simpl. left. trivial.
      repeat split; trivial. resolve_owner H4.
    + not_or ctr ctr0 H6.
    + not_or ctr ctr0 H6.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction Ev.
    + find_contradiction Ev.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del Ev.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction_del Ev.
    + not_or ctr ctr0 H6.
    + not_or ctr ctr0 H6.
    + ctr_case_analysis ctr ctr0. execute_own ctr H7. inversion H7.
    + find_contradiction_del Ev.
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
  destruct_join H1.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction Ev.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H9.
      inversion H9.
      eexists. split.
      eapply steps_does_not_remove_transactions; eauto.
      simpl. subst ledger'. simpl. right. left. trivial.
      repeat split; trivial. resolve_owner H4.
    + not_or ctr ctr0 H6.
    + not_or ctr ctr0 H6.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction Ev.
    + find_contradiction Ev.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction_del Ev.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction_del Ev.
    + not_or ctr ctr0 H6.
    + not_or ctr ctr0 H6.
    + ctr_case_analysis ctr ctr0. execute_own ctr H7. inversion H7.
    + find_contradiction_del Ev.
Qed.

Print frce_O_to_I.
