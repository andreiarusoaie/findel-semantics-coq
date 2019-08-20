Load findel.

(* Handy tactics *)
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


Ltac case_analysis H :=
  let H' := fresh "H" in
  match goal with
  | H : match (if ?c then _ else _)  with
        | Some _ => _
        | None => _
        end = _ |- _
    => case_eq c; intros H'; rewrite H' in H; try inversion H; clear H
  end.


(* Misc *)

Definition consistent_state (s : State) :=
  (forall ctr ctr', In ctr (m_contracts s) -> In ctr' (m_contracts s) -> (ctr_id ctr = ctr_id ctr') -> ctr = ctr') /\
  forall ctr, In ctr (m_contracts s) -> (~ In (Executed (ctr_id ctr)) (m_events s) /\ ~ In (Deleted (ctr_id ctr)) (m_events s)).

Lemma rest_not_equal_to_list (A : Type):
  forall (l : list A) a, a :: l <> l.
Proof.
  induction l; intros.
  - unfold not.
    intros H.
    inversion H.
  - unfold not in *.
    intros H'.
    inversion H'.
    subst a.
    eapply IHl.
    exact H1.
Qed.
(* End misc *)


(* Metaproperties about the ledger *)

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


(* Metaproperties about events *)
Lemma step_preserves_consistent_state:
  forall s s',
    step s s' ->
    consistent_state s ->
    consistent_state s'.
Proof.
Admitted.

Lemma steps_preserves_consistent_state:
  forall s s',
    steps s s' ->
    consistent_state s ->
    consistent_state s'.
Proof.
Admitted.


Lemma events_consistent_step:
  forall s s' e,
    step s s' ->
    In e (m_events s) ->
    In e (m_events s').
Proof.
  intros.
  induction H; subst s'; simpl; trivial; try right; try trivial.
Qed.

(* This lemma avoids the use of the classical logic *)
Lemma classic_step:
  forall s s' c,
    step s s' ->
    consistent_state s ->
    In c (m_contracts s) ->
    (In (Executed (ctr_id c)) (m_events s') \/ ~ In (Executed (ctr_id c)) (m_events s')).
Proof.
  intros.
  induction H; subst s'.
  - unfold append_new_ctr_to_state. simpl.
    right. unfold not. intros.
    destruct H6 as [H6 | H6]; try inversion H6.
    unfold consistent_state in H0.
    destruct H0 as [H' H''].
    apply H'' in H1.
    destruct H1 as [H1 H1'].
    contradiction.
  - case_eq (ctr_eq_dec c ctr); intros.
    + subst. simpl. left. left. trivial.
    + contradiction.
  - case_eq (ctr_eq_dec c ctr); intros.
    + subst. simpl. left. left. trivial.
    + contradiction.
  - case_eq (ctr_eq_dec c ctr); intros.
    + subst. simpl. left. left. trivial.
    + contradiction.
  - simpl. right. unfold not. intros.
    destruct H6 as [H6 | H6]; try inversion H6.
    unfold consistent_state in H0.
    destruct H0 as [H' H''].
    apply H'' in H1.
    destruct H1 as [H1 H1'].
    contradiction.
  - simpl. right.
    unfold consistent_state in H0.
    destruct H0 as [H' H''].
    apply H'' in H1.
    destruct H1 as [H1 H1'].
    trivial.
Qed.

(* Metaproperties about state consistency *)



(* Metaproperties about contract execution *)


Lemma step_effect_over_contract:
  forall ctr s s',
    step s s' ->
    In ctr (m_contracts s) ->
    (In ctr (m_contracts s') \/
     In (Executed (ctr_id ctr)) (m_events s') \/
     In (Deleted (ctr_id ctr)) (m_events s')).
Proof.
  intros *.
  intros H H'.
  induction H.
  - left. unfold append_new_ctr_to_state in H4.
    subst s'. simpl. right. trivial.
  - subst s'. simpl.
    case_eq (ctr_eq_dec ctr0 ctr); intros.
    + subst ctr0. right. left. left. trivial.
    + contradiction.
  - case_eq (ctr_eq_dec ctr0 ctr); intros.
    + subst. right. left. simpl. left. trivial.
    + contradiction.
  - case_eq (ctr_eq_dec ctr0 ctr); intros.
    + subst. right. left. simpl. left. trivial.
    + contradiction.
  - case_eq (ctr_eq_dec ctr0 ctr); intros.
    + subst. right. right. simpl. left. trivial.
    + contradiction.
  - subst s'. simpl. left. trivial.
Qed.

Lemma steps_effect_over_contract:
  forall ctr s s',
    steps s s' ->
    In ctr (m_contracts s) ->
    (In ctr (m_contracts s') \/
     In (Executed (ctr_id ctr)) (m_events s') \/
     In (Deleted (ctr_id ctr)) (m_events s')).
Proof.
  intros.
  induction H.
  - subst s2. left. trivial.
  - destruct IHsteps as [N | [E | D]].
    + eapply step_effect_over_contract; eauto.
    + eapply events_consistent_step in E; eauto.
    + eapply events_consistent_step in D; eauto.
Qed.


(* Lemma classic_steps: *)
(*   forall s s' c, *)
(*     steps s s' -> *)
(*     consistent_state s -> *)
(*     In c (m_contracts s) -> *)
(*     (In (Executed (ctr_id c)) (m_events s') \/ ~ In (Executed (ctr_id c)) (m_events s')). *)
(* Proof. *)
(*   intros. *)
(*   induction H. *)
(*   - subst. *)
(*     unfold consistent_state in H0. *)
(*     destruct H0 as [H' H'']. *)
(*     apply H'' in H1. *)
(*     destruct H1 as [H1 H1']. *)
(*     right. trivial. *)
(*   - destruct IHsteps as [H' | H']. *)
(*     + apply events_consistent_step with (s' := s2) in H'; auto. *)
(*     + apply classic_step with (c := c) in H2. *)
(*       * trivial. *)
(*       * eapply steps_preserves_consistent_state; eauto. *)
(*       * apply steps_effect_over_contract with (ctr := c) in H; auto. *)
(*         destruct H as [H | [H | H]]; trivial. *)
(*         ** contradiction. *)
(*         ** unfold consistent_state in H0. *)
(*            destruct H0 as [H0 H0']. *)
(*            admit. *)
(* Admitted. *)

(* Qed. *)


(* Metaproperties about events *)
Lemma only_tick_modifies_time:
  forall s s',
    step s s' ->
    (exists e, m_events s' = e :: (m_events s)) ->
    m_global_time s = m_global_time s'.
Proof.
  intros s s' H [e He].
  induction H; subst s'; trivial.
  simpl in *.
  symmetry in He.
  contradict He.
  apply rest_not_equal_to_list.
Qed.
