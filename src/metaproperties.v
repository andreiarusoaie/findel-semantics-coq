Load findel.

Ltac case_match H :=
  let H' := fresh "H" in
  match goal with
  | H : match ?c with
        | Some _ => _
        | None => _
        end = _ |- _
    => case_eq c; intros * H'; rewrite H' in H; inversion H; clear H
  end.

Ltac case_if H :=
  let H' := fresh "H" in
  match goal with
  | H : (if ?c then _ else _) = _ |- _
    => case_eq c; intros * H'; rewrite H' in H; inversion H; clear H
  end.

(* The execute function only appends transactions to the existing legder *)
Lemma ledger_consistent_execute:
  forall P sc I O balance time gtw
         ctr_id dsc_id next_id ledger result,
    execute P sc I O balance time gtw
            ctr_id dsc_id next_id ledger = Some result ->
    exists L', (res_ledger result) = L' ++ ledger.
Proof.
  induction P; intros; simpl in H; inversion H; clear H; subst; simpl.
  - exists []. simpl. trivial.
  - exists [{|
               tr_id := next_id;
               tr_ctr_id := ctr_id0;
               tr_from := I;
               tr_to := O;
               tr_amount := sc;
               tr_currency := c;
        tr_timestamp := time |}].
    simpl.
    trivial.
  - eapply IHP; eauto.
  - case_match H1.
    eapply IHP; eauto.
  - eapply IHP; eauto.
  - case_match H1.
    destruct r.
    case_match H2.
    destruct r.
    apply IHP2 in H0.
    destruct H0 as [L2 H0].
    apply IHP1 in H.
    destruct H as [L1 H].
    simpl in *.
    subst res_ledger0 res_ledger1.
    exists (L2 ++ L1).
    inversion H3.
    simpl.
    rewrite app_assoc.
    trivial.
  - exists []. simpl. trivial.
  - case_match H1.
    case_eq (n =? 0); intros H'; rewrite H' in H2.
    + eapply IHP2; eauto.
    + eapply IHP1; eauto.
  - case_if H1.
    case_if H2.
    + eapply IHP; eauto.
    + exists []. simpl; auto.
Qed.

(* execute does not remove transactions from the ledger *)
Lemma execute_does_not_remove_transactions:
  forall tr P sc I O balance time gtw
         ctr_id dsc_id next_id ledger result,
    execute P sc I O balance time gtw
            ctr_id dsc_id next_id ledger = Some result ->
    In tr ledger ->
    In tr (res_ledger result).
Proof.
  intros.
  apply ledger_consistent_execute in H.
  destruct H as [L' H].
  rewrite H.
  rewrite in_app_iff.
  right.
  trivial.
Qed.


(* The step relation preserves the existing legder *)
Lemma ledger_consistent_step:
  forall s1 s2,
    step s1 s2 ->
    exists L', (m_ledger s2) = L' ++ (m_ledger s1).
Proof.
  intros s1 s2 H.
  induction H; subst s2.
  - exists []. subst. simpl. trivial.
  - unfold exec_ctr_in_state_with_owner in H5.
    apply ledger_consistent_execute in H5.
    destruct H5 as [L' H5].
    exists L'.
    simpl in *.
    trivial.
  - unfold exec_prim_ctr_in_state_with_owner in H5.
    apply ledger_consistent_execute in H5.
    destruct H5 as [L' H5].
    exists L'.
    simpl in *.
    trivial.
  - unfold exec_prim_ctr_in_state_with_owner in H5.
    apply ledger_consistent_execute in H5.
    destruct H5 as [L' H5].
    exists L'.
    simpl in *.
    trivial.
  - exists []. simpl. trivial.
  - exists []. simpl. trivial.
Qed.


(* step does not remove transactions from the ledger *)
Lemma step_does_not_remove_transactions:
  forall tr s1 s2,
    step s1 s2 ->
    In tr (m_ledger s1)->
    In tr (m_ledger s2).
Proof.
  intros.
  apply ledger_consistent_step in H.
  destruct H as [L' H].
  rewrite H.
  rewrite in_app_iff.
  right.
  trivial.
Qed.


(* The steps relation preserves the existing legder *)
Lemma ledger_consistent_steps:
  forall s1 s2,
    steps s1 s2 ->
    exists L', (m_ledger s2) = L' ++ (m_ledger s1).
Proof.
  intros.
  induction H; subst.
  - exists []. simpl. trivial.
  - apply ledger_consistent_step in H0.
    destruct H0 as [L1 H0].
    destruct IHsteps as [L2 H'].
    rewrite H' in H0.
    rewrite H0.
    exists (L1 ++ L2).
    rewrite app_assoc.
    trivial.
Qed.


(* step does not remove transactions from the ledger *)
Lemma steps_does_not_remove_transactions:
  forall tr s1 s2,
    steps s1 s2 ->
    In tr (m_ledger s1)->
    In tr (m_ledger s2).
Proof.
  intros.
  apply ledger_consistent_steps in H.
  destruct H as [L' H].
  rewrite H.
  rewrite in_app_iff.
  right.
  trivial.
Qed.
