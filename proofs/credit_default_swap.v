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


Definition CDS (Alice C : Address)
           (defaulted_addr : Address)
           (price FY F : nat) (now : Time)
           (Y1 Y2 Y3 : nat)
  :=
  (
    And
      (* first year *)
      (And (Give (Scale F (One USD)))
           (At (now + Y1)
               (If defaulted_addr
                   (Scale (price + (2 * FY)) (One USD))
                   Zero)
           )
      )

      (
        And
          (At (now + Y1)
              (If defaulted_addr
                  Zero
                  (And (Give (Scale F (One USD)))
                       (At (now + Y2)
                           (If defaulted_addr
                               (Scale (price + FY) (One USD))
                               Zero)
                       )
                  )
              )
          )

          (At (now + Y2)
              (If defaulted_addr
                  Zero
                  (And (Give (Scale F (One USD)))
                       (At (now + Y3)
                           (If defaulted_addr
                               (Scale (price + FY) (One USD))
                               Zero)
                       )
                  )
              )
          )
      )
  ).


Definition is_executed_at (c : FinContract)
           (s1 s2 state1 state2 : State)
           (time : Time) :=
    steps s1 state1 /\
    step state1 state2 /\
    steps state2 s2 /\
    can_join (ctr_owner c) c /\ 
    In c (m_contracts state1) /\
    In (Executed (ctr_id c)) (m_events state2) /\
    time = (m_global_time state1).

Ltac destruct_exec H :=
  let Step := fresh "Step" in
  let Ss1 := fresh "Ss" in
  let Ss2 := fresh "Ss" in
  let Join := fresh "Join" in
  let InCtr := fresh "InCtr" in
  let InEv := fresh "InEv" in
  let T := fresh "T" in
  destruct H as [Ss1 [Step [Ss2 [Join [inCtr [InEv T]]]]]].

Definition generates_new_ctr_when_executed_at (c c': FinContract)
           (proposed_owner : Address)
           (s1 s2 state1 state2 : State)
           (time : Time) :=
    (* is_executed_at *)
    steps s1 state1 /\
    step state1 state2 /\
    steps state2 s2 /\
    can_join (ctr_owner c) c /\ 
    In c (m_contracts state1) /\
    In (Executed (ctr_id c)) (m_events state2) /\
    time = (m_global_time state1) /\
    (* generates new ctr with proposed_owner *)
    ~ In c' (m_contracts state1) /\
    In c' (m_contracts state2) /\
    (ctr_proposed_owner c' = proposed_owner).

Ltac destruct_gen_new_ctr H :=
  let Ss1 := fresh "Ss" in
  let Ss2 := fresh "Ss" in
  let Step := fresh "Step" in
  let Join := fresh "Join" in
  let InCtr := fresh "InCtr" in
  let InEv := fresh "InEv" in
  let T := fresh "T" in
  let InCtr' := fresh "InCtr" in
  let NInCtr := fresh "NInCtr" in
  let SamePrim := fresh "SamePrim" in
  destruct H as [Ss1 [Step [Ss2 [Join [inCtr [InEv [T [NInCtr [InCtr' SamePrim]]]]]]]]].


Definition internal_1 (t : Time) (C Alice defaulted_addr : Address)
           (price B2AliceFee : nat) :=
  (At t
      (If defaulted_addr
          (Scale (price + (B2AliceFee + (B2AliceFee + 0)))
                 (One USD)) Zero)).
    

Proposition CDS_default_Y1_Alice_rights_first_ctr:
  forall s1 s2 s s' c_id dsc_id defaulted_addr price
         B2AliceFee c C Alice t response,
    c = finctr c_id dsc_id
               (internal_1 t C Alice defaulted_addr price B2AliceFee)
               C Alice Alice 1 ->
    s1 ~~> s2 ->
    consistent_state s1 ->
    is_executed_at c s1 s2 s s' t ->
    response <> 0 ->
    query (m_gateway s) defaulted_addr (m_global_time s) = Some response ->
    Alice <> 0 ->
    m_global_time s > Δ ->
    (* conclusion *)
    (exists tr,
        In tr (m_ledger s2) /\
        tr_ctr_id tr = (ctr_id c) /\
        tr_from tr = C /\
        tr_to tr = Alice /\
        tr_amount tr = price + (2 * B2AliceFee)
    ).
Proof.
  intros.
  destruct_exec H2.
  insert_consistent s Ss.
  induction Step; subst s'.
  - inversion_event InEv. find_contradiction I2.
  - ctr_case_analysis c ctr.
    execute_own c H13.
    case_if H13.
    case_if H16.
    + rewrite H4 in H17; auto.
      case_if H17.
      * destruct response. contradiction.
        simpl in H15. inversion H15.
      * subst. simpl in *. clear H14.
        eexists.
        apply steps_does_not_remove_transactions with
            (tr := {|
           tr_id := m_fresh_id s;
           tr_ctr_id := c_id;
           tr_from := C;
           tr_to := owner;
           tr_amount := price + (B2AliceFee + (B2AliceFee + 0)) + 0;
           tr_currency := USD;
           tr_timestamp := m_global_time s |}) in Ss0.
        repeat split; eauto; simpl.
        ** resolve_owner H8.
        ** omega.
        ** simpl. left. trivial.
    + subst t. apply ltb_sound_false in H13. contradict H13.
      unfold Δ. omega.
  - not_or c ctr H10.
  - not_or c ctr H10.
  - ctr_case_analysis c ctr. inversion_event InEv. find_contradiction InEv.
  - find_contradiction InEv.
Qed.



Proposition CDS_default_Y1_Alice_rights:
  forall s1 s2 CDSctr CDSctr_id dsc_id Alice C defaulted_addr price B2AliceFee Alice2CFee state1 state2 state3 state4 response now c' Y1 Y2 Y3 t' p1 p2,
    s1 ~~> s2 ->
    consistent_state s1 ->
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         B2AliceFee Alice2CFee now Y1 Y2 Y3)
                    C Alice Alice 1 ->
    generates_new_ctr_when_executed_at CDSctr c' Alice s1 s2 state1 state2 now ->

    (* defaulted at now + Y1; primitive(c') = At t' (If defaulted_addr p1 p2) /\ p1 <> Zero  *)
    is_executed_at c' state2 s2 state3 state4 (now + Y1) ->
    (ctr_primitive c') = At t' (If defaulted_addr p1 p2) ->
    p1 <> Zero ->
    response <> 0 ->
    (forall t s, t >= now + Y1 ->
                 query (m_gateway s) defaulted_addr t = Some response) ->
    (* not defaulted until now + Y1 *)
    (forall t s, t < now + Y1 ->
                 query (m_gateway s) defaulted_addr t = Some 0) ->

    (* technical conditions: the global time and Yrs are all greater than 30 sec. *)
    (forall s, m_global_time s > Δ) ->
    Y1 > Δ -> Y2 > Δ -> Y3 > Δ -> Y2 - Y1 > Δ -> Y3 - Y2 > Δ ->
    Alice <> 0 ->
    (* conclusion *)
    (exists tr,
        In tr (m_ledger s2) /\
        tr_ctr_id tr = (ctr_id c') /\
        tr_from tr = C /\
        tr_to tr = Alice /\
        tr_amount tr = price + (2 * B2AliceFee)
    ).
Proof.
  intros.
  destruct_gen_new_ctr H2.
  insert_consistent state1 Ss.
  insert_consistent state2 Ss.
  Check step_implies_execute_result.
  induction Step; subst state2.
  - inversion_event InEv.
    apply consistent_impl_exec in inCtr; auto. contradiction.
  - ctr_case_analysis CDSctr ctr.
    execute_own CDSctr H23.
    rewrite H8 in H23. simpl in H23.
    case_match H23.
    + destruct r. case_match H26. destruct r. inversion H27. clear H27. subst now.
      case_match H23. destruct r.
      case_match H27. destruct r. inversion H28. clear H28. subst ctrs'.
      case_if H23.
      case_if H28.
      * apply ltb_sound_true in H23. contradict H23. omega.
      * subst res_next3 res_ledger3 res_contracts3 res_balance2 res_balance1 res_next1 res_ledger1. simpl in *.
        case_if H25.
        case_if H29.
        ** apply ltb_sound_true in H25. contradict H25. omega.
        ** rewrite H25, H26 in H1.
           inversion H1. clear H1.
           subst res_contracts0 res_next0 res_ledger0 res_ledger2 res_contracts2 res_next2 res_balance0 res_balance3.
           inversion H32. clear H32.
           subst ledger' next' res_contracts1.
           repeat rewrite in_app_iff in InCtr0.
           destruct InCtr0 as [In | [In | [In | In]]].
           *** admit. (*apply contradiction + lemma *)
           *** simpl in In. destruct In as [In | In]; try contradiction.
               unfold can_join in H18. simpl in H18. destruct H18 as [H18 | H18]; try contradiction.
               eapply CDS_default_Y1_Alice_rights_first_ctr.
               
               **** unfold internal_1, At. eauto.
               **** simpl. apply H7. admit.
               **** admit.
               **** eexists. 

           *** rewrite <- In in H4. simpl in H4. unfold At in H4.
               inversion H4. subst p1. contradiction.
           *** simpl in In. destruct In as [In | In]; try contradiction.
               rewrite <- In in H4. simpl in H4. unfold At in H4.
               inversion H4. subst p1. contradiction.
    + case_match H22. subst now. omega.
  - ctr_case_analysis CDSctr ctr.
    subst CDSctr. unfold CDS in H19. simpl in H19. inversion H19.
  - ctr_case_analysis CDSctr ctr.
    subst CDSctr. unfold CDS in H19. simpl in H19. inversion H19.
  - simpl in InEv. destruct InEv as [I1 | I2]; try inversion I1.
    apply consistent_impl_exec in inCtr; trivial. contradiction.
  - simpl in InCtr0. contradiction.
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
If C fails to pay the yearly fee (FY), then
the bank B should pay Alice (price + (YL * FY)),
where YL is the number of years left until maturity,
and FY is the yearly fee that C should pay to Alice.
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



(*
Alice should pay upfront an yearly fee F to B.
 *)
Proposition yearly_check_default_false_C_rights :
  forall s1 s2 s ctr_id dsc_id I O ctr defaulted_addr price FY F YL time response,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (yearly_check defaulted_addr price FY F YL time) I O O 1 ->
    joins_in_s O ctr s1 s2 s time ->
    O <> 0 ->
    query (m_gateway s) defaulted_addr (m_global_time s) = Some response ->
    response = 0 ->
    time > Δ ->
    (exists tr,
      In tr (m_ledger s2) /\
      tr_ctr_id tr = ctr_id /\
      tr_from tr = O /\
      tr_to tr = I /\
      tr_amount tr = F).
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
      case_if H4.
      case_if H16.
      * destruct r. inversion H15. subst.
        eexists. split.
        ** inversion H17.
           eapply steps_does_not_remove_transactions; eauto.
           simpl. subst ledger'. simpl. left. trivial.
        ** repeat split; trivial. resolve_owner H7.
           simpl. omega.
      * subst time. apply ltb_sound_false in H4.
        contradict H4.
        unfold Δ. omega.
      * inversion H0.
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
      * apply ltb_sound_false in H4. subst time.
        contradict H4.
        unfold Δ. omega.
      * case_if H0.
        ** subst. contradict H10. rewrite helper'; auto.
        ** case_if H13.
      * inversion H0.
    + find_contradiction_del Ev.
Qed.


(* Definition CDS (Alice C : Address) *)
(*            (defaulted_addr : Address) *)
(*            (price FY F : nat) (YL now : Time) *)
(*   := *)
(*   ( *)
(*     And *)
(*       (yearly_check defaulted_addr price FY F 3 (now + 1)) *)
(*       ( *)
(*         And (yearly_check defaulted_addr price FY F 2 (now + 2)) *)
(*             (yearly_check defaulted_addr price FY F 1 (now + 3)) *)
(*       ) *)
(*   ). *)

Proposition CDS_defaulted_Alice_rights_1_year :
  forall s1 s2 s ctr_id dsc_id Alice C ctr defaulted_addr price FY F YL response time,
    consistent_state s1 ->
    ctr = finctr ctr_id dsc_id (CDS Alice C defaulted_addr price FY F YL (m_global_time s)) Alice C C 1 ->
    joins_in_s O ctr s1 s2 s (m_global_time s) ->
    C <> 0 ->
    query (m_gateway s) defaulted_addr (m_global_time s) = Some 0 -> (* B does not default from beginning *)
    (forall t, t >= time ->
              query (m_gateway s) defaulted_addr t = Some response) -> (* consistent oracle *)
    response <> 0 -> (* defaulted_addr response is true *)
    m_global_time s > Δ ->
    (time = m_global_time s + 1 ->  (* defaulted after 1 year *)
     exists tr,
       In tr (m_ledger s2) /\
       tr_ctr_id tr = ctr_id /\
       tr_from tr = C /\
       tr_to tr = Alice /\
       tr_amount tr = price + (2 * FY)). (* Alice rights if B defaults: C pays price + 2 yearly fee *)
Proof.
  intros.
  destruct_joins_in H1.
  - insert_consistent s Ss.
    induction St; subst s0.
    + inversion_event Ev. find_contradiction Ev.
    + ctr_case_analysis ctr ctr0.
      execute_own ctr H14. clear H15. subst time.
      rewrite H3 in H14. simpl in *. clear T H11.
      case_match H14. destruct r.
      case_match H11. destruct r. inversion H15. subst. clear H15.
      case_match H7. destruct r.
      case_match H15. destruct r. inversion H16. subst. clear  H16.
      case_match H7. destruct r.  inversion H16. subst. clear  H16.
      case_if H14.
      case_if H16; subst; unfold Δ in *.
      * unfold Y3 in H14.
        apply ltb_sound_true in H14.
        contradict H14. omega.
      * case_match H11. destruct r.
        case_match H11. destruct r.
        inversion H18. subst. clear H18.
        case_if H16.
        case_if H18.
        ** unfold Y1 in H11.
           apply ltb_sound_true in H11.
           contradict H11. omega.
        ** assert (H'' : (2 * FY = (FY + (FY + 0)))).
           omega. rewrite <- H''.
           eapply yearly_check_default_true_Alice_rights.

        case_if H15.
        case_if H18.  subst.
        case_match H0. destruct r. subst.
        inversion H18. subst. clear H18.
        case_if H16.
        ** case_if H18; subst.
           *** 
           *** 
           subst.

        ** 

        

    + not_or ctr ctr0 H10.
    + not_or ctr ctr0 H10.
    + ctr_case_analysis ctr ctr0.
    + find_contradiction Ev.
  - insert_consistent s Ss.
    induction St; subst s0.
    + inversion_event Ev.
    + ctr_case_analysis ctr ctr0.
    + not_or ctr ctr0 H10.
    + not_or ctr ctr0 H10.
    + ctr_case_analysis ctr ctr0.
    + find_contradiction Ev.
Qed.
