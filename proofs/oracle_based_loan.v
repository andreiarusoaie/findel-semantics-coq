Load metaproperties.


(*
Credit default swap

Assume that Alice holds a financial obligation from
a company called C whose price is P = 1000 dollars.
The maturity of the obligation is M = 3 years:
C pays a fee per year of FY = 100 dollars to Alice,
and at the end of the 3 years (maturity reached)
it pays back to Alice P, that is, 1000 dollars.
Therefore, Alice should receive

  P + M * FY = 1000 + (3 * 100)

dollars at the end of the 3 years.

Since Alice knows that C has financial issues and it is
possible that C may not be able to pay the yearly fees
(i.e., C defaults), Alice buys a Credit Swap Derivative
(CDS) from a bank B.
A CDS acts as an insurance: Alice pays a fee of F = 20
dollars per year to B, and in exchange, B will pay
1000 + (YL * 100) dollars if C. That is, B pays to Alice
P + YL * 100, where YL is the number of years left until
the obligation reaches its maturity.
For instance, if C defaults in the first year, YL = M - 1
and B pays P + YL * 100 = 1000 + 200 = 1200 dollars to Alice.

Here we want to prove that Alice recovers P + M * FY, that is,
1300 dollars.
The bank B receives a fee F = k * 20 from Alice, where
k = M - YL.
*)


Definition pay_sum (sum : nat) (c : Currency) :=
  Scale sum (One c).

Definition default_payment (defaulted_addr : Address)
           (price FY : nat) (YL : Time) :=
  If defaulted_addr
     (pay_sum (price + (YL * FY)) USD)
     Zero.

Definition yearly_check (defaulted_addr : Address)
           (price FY F : nat) (YL time : Time) :=
  And (Give (pay_sum F USD))
      (At time (default_payment defaulted_addr price FY YL)).

Definition CDS (Alice C : Address)
           (defaulted_addr : Address)
           (price FY F : nat) (YL now : Time)
  :=
  (
    And
      (yearly_check defaulted_addr price FY F 3 (now + 1))
      (
        And (yearly_check defaulted_addr price FY F 2 (now + 2))
            (yearly_check defaulted_addr price FY F 1 (now + 3))
      )
  ).

(* The issuer pays the owner *)
Proposition pay_sum_I_to_O :
  forall s1 s2 ctr_id dsc_id I O ctr t sum c,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (pay_sum sum c) I O O 1 ->
    joins O ctr s1 s2 t ->
    O <> 0 ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = sum).
Proof.
  intros.
  destruct_join H1.
  - insert_consistent s Ss.
    induction St; subst s'.
    + inversion_event Ev. find_contradiction Ev.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H9. inversion H9. clear H9. subst.
      simpl in *.
      eexists. split.
      * eapply steps_does_not_remove_transactions; eauto; simpl. left. trivial.
      * repeat split; trivial. resolve_owner H4.
        simpl. omega.
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

(* If the payment is defaulted, then the insurance pays the
 price + YL * FY *)
Proposition defaulted_payment_true :
  forall s1 s2 s ctr_id dsc_id I O ctr t response defaulted_addr FY YL price,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (default_payment defaulted_addr price FY YL) I O O 1 ->
    joins_in_s O ctr s1 s2 s t ->
    O <> 0 ->
    query (m_gateway s) defaulted_addr (m_global_time s) = Some response ->
    response <> 0 ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = price + (YL * FY)).
Proof.
  intros.
  destruct_joins_in H1.
  - insert_consistent s Ss.
    induction St; subst s0.
    + inversion_event Ev. find_contradiction Ev.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H11.
      rewrite H3 in H11.
      case_eq (response); intros; subst response.
      * contradiction.
      *
        simpl in H11.
        inversion H11.
        subst.
        eexists. split.
        eapply steps_does_not_remove_transactions; eauto.
        simpl. left. trivial.
        repeat split; trivial. resolve_owner H6.
        simpl. omega.
    + not_or ctr ctr0 H8.
    + not_or ctr ctr0 H8.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction Ev.
    + find_contradiction Ev.
  - insert_consistent s Ss.
    induction St; subst s0.
    + inversion_event Ev. find_contradiction_del Ev.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction_del Ev.
    + not_or ctr ctr0 H8.
    + not_or ctr ctr0 H8.
    + ctr_case_analysis ctr ctr0. execute_own ctr H9.
      rewrite H3 in H9.
      case_eq (response); intros; subst response; simpl in *; try contradiction.
      inversion H9.
    + find_contradiction_del Ev.
Qed.


(* Definition yearly_check (defaulted_addr : Address) *)
(*            (price FY F : nat) (YL time : Time) := *)
(*   And (Give (pay_sum F USD)) *)
(*       (At time (default_payment defaulted_addr price FY YL)). *)


Lemma ltb_complete_true:
  forall a b,
    a < b -> a <? b = true.
Proof.
  induction a; intros.
  - destruct b. inversion H. unfold Nat.ltb. simpl. trivial.
  - destruct b.
    + inversion H.
    + apply lt_S_n in H. assert (H' := H). apply IHa in H.
      unfold Nat.ltb in *. simpl in *. destruct b; auto.
Qed.

Lemma ltb_complete_false:
  forall a b,
    ~ a < b -> a <? b = false.
Proof.
  induction a; intros.
  - destruct b; auto. contradict H. omega.
  - destruct b.
    + unfold Nat.ltb. simpl. trivial.
    + SearchPattern (_ -> S _ < S _).
      unfold not in H.
      assert (H' : a < b -> False).
      intros. apply H. apply lt_n_S. assumption.
      apply IHa in H'.
      unfold Nat.ltb in *. simpl in *. destruct b; auto.
Qed.

Lemma helper :
  forall b a,
    a > b ->
    b > 0 ->
    a - b <? a = true.
Proof.
  intros. apply ltb_complete_true. omega.
Qed.

Lemma helper' : forall a b,
    a > b ->
    a + b <? a = false.
Proof.
  intros. apply ltb_complete_false. omega.
Qed.


(*
If the C fails to pay the yearly fee (FY), then
the bank B should pay Alice price + (YL * FY),
where YL is the number of years left until maturity.
Alice should pay upfront an yearly fee F to B.
 *)
Proposition yearly_check_default_true_Alice_rights :
  forall s1 s2 s ctr_id dsc_id I O ctr defaulted_addr price FY F YL time response,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (yearly_check defaulted_addr price FY F YL time) I O O 1 ->
    joins_in_s O ctr s1 s2 s time ->
    O <> 0 ->
    query (m_gateway s) defaulted_addr (m_global_time s) = Some response ->
    response <> 0 ->
    time > Δ ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = I /\
      tr_to tr = O /\
      tr_amount tr = price + (YL * FY)).
Proof.
  intros.
  destruct_joins_in H1.
  - insert_consistent s Ss.
    induction St; subst s0.
    + inversion_event Ev. find_contradiction Ev.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H12.
      case_eq (response); intros; subst response; try contradiction.
      rewrite H3 in H12. simpl in H12.
      case_match H12.
      case_if H12.
      case_if H16.
      * destruct r. inversion H17. subst.
        eexists. split.
        ** inversion H15.
           eapply steps_does_not_remove_transactions; eauto.
           simpl. subst ledger'. simpl. left. trivial.
        ** repeat split; trivial. resolve_owner H7.
           simpl. omega.
      * apply helper in H5; eauto. subst time. rewrite H5 in H0. inversion H0.
        unfold Δ. omega.
    + not_or ctr ctr0 H9.
    + not_or ctr ctr0 H9.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction Ev.
    + find_contradiction Ev.
  - insert_consistent s Ss.
    induction St; subst s0.
    + inversion_event Ev. find_contradiction_del Ev.
    + ctr_case_analysis ctr ctr0. inversion_event Ev. find_contradiction_del Ev.
    + not_or ctr ctr0 H9.
    + not_or ctr ctr0 H9.
    + ctr_case_analysis ctr ctr0. execute_own ctr H10.
      case_eq (response); intros; subst response; try contradiction.
      rewrite H3 in H10. simpl in H10.
      case_match H10.
      case_if H0.
      case_if H14.
      * destruct r. inversion H15; clear H15; subst.
        inversion H13.
      * apply helper in H5; eauto. subst time. rewrite H5 in H0. inversion H0.
        unfold Δ. omega.
      * case_if H0.
        ** subst. contradict H10. rewrite helper'; auto.
        ** case_if H13.
    + find_contradiction_del Ev.
Qed.
