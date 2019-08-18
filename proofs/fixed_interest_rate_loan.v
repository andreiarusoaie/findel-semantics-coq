Load helpers.

(* firl = fixed interest rate loan *)
Definition firl_description (t : Time) :=
  (And
     (Before t (Or (Give (One USD)) (Give (One EUR))))
     (After (t + 2) (Scale 2 (One EUR)))
  ).

Print execute.

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


Lemma firl_generates_transactions :
  forall t scale I O balance time gtw ctr_id dsc_id next_id ledger result,
    execute (firl_description t) scale I O balance time
            gtw ctr_id dsc_id next_id ledger = Some result
    ->
    res_ledger result <> ledger.
Proof.
  intros.
  unfold firl_description in H.
  simpl in H.
  case_analysis H.
  case_analysis H2.
  - case_analysis H3.
    case_analysis H4; simpl.
    + apply rest_not_equal_to_list.
    + admit. (* This proof path shows that the ledger might not get changed. *)
  - case_analysis H3.
    case_analysis H4; simpl.
    + apply rest_not_equal_to_list.
    + admit. (* This proof path shows that the ledger might not get changed. *)
Admitted.

Check firl_description.
Check finctr.
Print FinContract.
Print State.
Check Executed.

Definition is_executed (c_id : Id) (s : State) := In (Executed c_id) (m_events s).

Definition is_issued (c_id dsc_id : Id)(P : Primitive) (I O: Address) (sc : nat) (s : State):=
  In (finctr c_id dsc_id P I O O sc) (m_contracts s).
 
Print State.
Print Transaction.

Lemma firl_pays_the_owner_if_time_is_t_plus_2 :
  forall s1 s2 t I O sc c_id dsc_id,
    steps s1 s2 ->
    m_global_time s1 = t ->
    m_global_time s2 >= t + 2 ->
    is_issued c_id dsc_id (firl_description t) I O sc s1 ->
    ~ is_executed c_id s1 ->
    is_executed c_id s2 ->
    exists tr tr_id,
      In tr (m_ledger s2) /\
      tr = (transaction tr_id c_id I O 2 EUR (t+2)).
Proof.
  intros.
  induction H; try subst; try contradiction.
  


Print exec_ctr_in_state_with_owner.


Definition double_your_loan_ctr
           (alice bob : Address)
           (ctr_id dsc_id : Id)
           (t0 : Time) :=
  finctr ctr_id
         dsc_id
         (double_your_loan_desc t0)
         alice
         bob
         bob
         1.

Ltac exec_double_your_loan H :=
  match type of H with
  | exec_ctr_in_state_with_owner (double_your_loan_ctr _ _ _ _ _) _ _ = Some _ =>
    unfold double_your_loan_ctr, double_your_loan_desc, exec_ctr_in_state_with_owner in H; simpl in H; inversion H; clear H
  end.


Lemma bob_requests_double_loan_from_alice :
  forall s1 alice bob ctr_id dsc_id result t0,
    exec_ctr_in_state_with_owner
      (double_your_loan_ctr alice bob ctr_id dsc_id t0) s1 bob =
    Some result ->
    exists ctr,
      % ctr ∈ (res_contracts result) | alice --> bob | (Timebound t0 INF (Scale 2 (One EUR))) %.
Proof.
