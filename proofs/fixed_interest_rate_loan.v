Load metaproperties.

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
    + admit.
    + admit. (* This proof path shows that the ledger might not get changed. *)
  - case_analysis H3.
    case_analysis H4; simpl.
    + admit.
    + admit. (* This proof path shows that the ledger might not get changed. *)
Admitted.


Definition is_executed (c_id : Id) (s : State) := In (Executed c_id) (m_events s).

Definition is_issued (c_id dsc_id : Id)(P : Primitive) (I O: Address) (sc : nat) (s : State):=
  In (finctr c_id dsc_id P I O O sc) (m_contracts s).


Lemma ltb_sound :
  forall a b, a <? b = true -> a < b.
Admitted.

Lemma issuer_pays_the_owner_if_time_is_t_plus_2' :
  forall s1 s2 t I O c_id dsc_id,
    step s1 s2 ->
    m_global_time s1 >= t + 2 ->
    m_global_time s2 >= t + 2 ->
    consistent_state s1 ->
    is_issued c_id dsc_id (firl_description t) I O 1 s1 ->
    O <> 0 ->  (* O is field is not 0x0 *) 
    ~ is_executed c_id s1 ->
    is_executed c_id s2 ->
    exists tr tr_id,
      In tr (m_ledger s2) /\
      tr = (transaction tr_id c_id I O 2 EUR (t+2)).
Proof.
  intros.
  assert (H' := H).
  unfold is_issued, is_executed in *.
  eapply tick_not_applied in H'; eauto.
  induction H.
  - unfold append_new_ctr_to_state in *.
    subst s2.
    simpl in *.
    unfold is_executed in H6.
    simpl in H6.
    destruct H6 as [H6 | H6]; try inversion H6.
    unfold consistent_state in H2.
    destruct H2 as [_ H2].
    apply H2 in H3.
    destruct H3 as [H3 _]; try contradiction.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.


Lemma issuer_pays_the_owner_if_time_is_t_plus_2 :
  forall s1 s2 t I O c_id dsc_id,
    steps s1 s2 ->
    m_global_time s1 = t ->
    m_global_time s2 >= t + 2 ->
    consistent_state s1 ->
    is_issued c_id dsc_id (firl_description t) I O 1 s1 ->
    O <> 0 ->  (* O is field is not 0x0 *) 
    ~ is_executed c_id s1 ->
    is_executed c_id s2 ->
    exists tr tr_id,
      In tr (m_ledger s2) /\
      tr = (transaction tr_id c_id I O 2 EUR (t+2)).
Proof.
  intros.
  induction H; intros.
  - subst s2. omega.
  - assert (S1 := H). assert (S2 := H7).
    unfold is_executed in *.
    set (c := {|
      ctr_id := c_id;
      ctr_desc_id := dsc_id0;
      ctr_primitive := firl_description t;
      ctr_issuer := I;
      ctr_owner := O;
      ctr_proposed_owner := O;
      ctr_scale := 1 |}).
    apply steps_effect_over_contract with (ctr := c) in H; auto.
    destruct H as [H | [H | H]].
    + eapply issuer_pays_the_owner_if_time_is_t_plus_2'; eauto.
      eapply tick_not_applied in H7; eauto.
      rewrite H7. auto.
      apply steps_preserves_consistent_state in S1; auto.
      apply steps_preserves_consistent_state in S1; auto.
      apply steps_preserves_consistent_state in S1; auto.
      unfold consistent_state in S1.
      destruct S1 as [_ S1].
      apply S1 in H.
      destruct H as [H _]; try contradiction.
      unfold is_executed. subst c. simpl in *. trivial.
    + 
Admitted.
