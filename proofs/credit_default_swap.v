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

Definition pay_at_t (t : Time)
           (I O addr : Address)
           (sum : nat) :=
  (At t
      (If addr
          (Scale sum (One USD))
          Zero)
  ).

Definition CDS (Alice C : Address)
           (defaulted_addr : Address)
           (price FY F : nat) (now : Time)
           (Y1 Y2 Y3 : nat)
  :=
  (
    And
      (* first year *)
      (And (Give (Scale F (One USD)))
           (pay_at_t (now + Y1) C Alice defaulted_addr (price + (2 * FY)))
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


Definition is_executed (c : FinContract)
           (state1 state2 : State)
           (time : Time) :=
    step state1 state2 /\
    In c (m_contracts state1) /\
    In (Executed (ctr_id c)) (m_events state2) /\
    time = (m_global_time state1).

Ltac destruct_exec H :=
  let Step := fresh "Step" in
  let InCtr := fresh "InCtr" in
  let InEv := fresh "InEv" in
  let T := fresh "T" in
  destruct H as [Step [inCtr [InEv T]]].

Definition generates_new_ctr_when_executed_at (c c': FinContract)
           (proposed_owner : Address)
           (state1 state2 : State)
           (time : Time) :=
    (* is_executed_at *)
    step state1 state2 /\
    In c (m_contracts state1) /\
    In (Executed (ctr_id c)) (m_events state2) /\
    time = (m_global_time state1) /\
    (* generates new ctr with proposed_owner *)
    ~ In c' (m_contracts state1) /\
    In c' (m_contracts state2) /\
    (ctr_proposed_owner c' = proposed_owner).


Ltac destruct_gen_new_ctr H :=
  let Step := fresh "Step" in
  let InCtr := fresh "InCtr" in
  let InEv := fresh "InEv" in
  let T := fresh "T" in
  let InCtr' := fresh "InCtr" in
  let NInCtr := fresh "NInCtr" in
  let SamePrim := fresh "SamePrim" in
  destruct H as [Step [inCtr [InEv [T [NInCtr [InCtr' SamePrim]]]]]].


Axiom global_time_is_bigger_than_delta:
  forall s,
    m_global_time s > Δ.

Create HintDb cds.
Hint Resolve global_time_is_bigger_than_delta : cds.
Hint Constructors steps : cds.
Hint Constructors step : cds.

Proposition pay_at_t_O_rights:
  forall s1 s2 c t I O addr sum c_id dsc_id response,
    c = finctr c_id dsc_id (pay_at_t t I O addr sum) I O O 1 ->
    is_executed c s1 s2 t ->
    query (m_gateway s1) addr t = Some response ->
    can_join O c ->
    O <> 0 -> 
    response <> 0 ->
    consistent_state s1 ->
    (exists tr,
        In tr (m_ledger s2) /\
        tr_ctr_id tr = (ctr_id c) /\
        tr_from tr = I /\
        tr_to tr = O /\
        tr_amount tr = sum
    ).
Proof.
  intros.
  destruct_exec H0.
  induction Step; subst s2.
  - inversion_event InEv. find_contradiction InEv.
  - ctr_case_analysis c ctr.
    execute_own c H11.
    case_if H11.
    case_if H14; simpl.
    + subst t.
      rewrite H1 in H15.
      destruct response; simpl in *; try contradiction.
      inversion H15. subst.
      eexists.
      split.
      * simpl. left. eauto.
      * repeat split; simpl; trivial.
        resolve_owner H6. omega.
    + subst t. apply ltb_sound_false in H11. contradict H11.
      assert (H' : m_global_time s1 > Δ).
      apply global_time_is_bigger_than_delta. 
      unfold Δ. omega.
  - not_or c ctr H8.
  - not_or c ctr H8.
  - ctr_case_analysis c ctr. inversion_event InEv. find_contradiction InEv.
  - find_contradiction InEv.
Qed.


Lemma helper_1 :
  forall t y d, t > d -> d > 0 -> (t + y + d <? t) = false.
Proof.
  intros.
  case_eq (t + y + d <? t); intros * H'; trivial.
  apply ltb_sound_true in H'.
  omega.
Qed.

Lemma helper_2 :
  forall t y d,  y > d -> (t + y - d <? t) = false.
Proof.
  intros.
  case_eq (t + y - d <? t); intros * H'; trivial.
  apply ltb_sound_true in H'.
  omega.
Qed.

Lemma in_smaller_list :
  forall l x x', In x (rm x' l) -> In x l.
Proof.
  induction l; intros; simpl in *; trivial.
  case_eq (ctr_eq_dec x' a); intros * H'; rewrite H' in H.
  - subst. right. eapply IHl. eauto.
  - contradiction.
Qed.


Proposition CDS_defaulted_in_Y1_Alice_rights:
  forall CDSctr CDSctr_id dsc_id Alice C defaulted_addr
         price B2AliceFee Alice2CFee s1 s2 s3 s4 response now c'
         Y1 Y2 Y3,
    consistent_state s1 ->
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         B2AliceFee Alice2CFee now Y1 Y2 Y3)
                    C Alice Alice 1 ->
    (* execute CDS first; it will generate a few contracts *)
    generates_new_ctr_when_executed_at CDSctr c' Alice s1 s2 now ->
    (* in s1, B did not defaulted *)
    query (m_gateway s1) defaulted_addr (m_global_time s1) = Some 1 ->

    (* several steps later *)
    s2 ~~> s3 ->

    (* execute c' at now + Y1 *)
    can_join Alice c' ->
    is_executed c' s3 s4 (now + Y1) ->
    (ctr_primitive c') = pay_at_t (now + Y1) C Alice defaulted_addr (price + 2 * B2AliceFee) ->
    response <> 0 ->
    (* in s3, B defaults and C has to pay Alice *)
    query (m_gateway s3) defaulted_addr (m_global_time s1 + Y1) = Some 1 ->


    (* technical conditions: a year has more greater than 30 sec. :-) *)
    Y1 > Δ -> Y2 > Δ -> Y3 > Δ -> Y2 - Y1 > Δ -> Y3 - Y2 > Δ ->
    Alice <> 0 ->
    (* conclusion *)
    (exists tr,
        In tr (m_ledger s4) /\
        tr_ctr_id tr = (ctr_id c') /\
        tr_from tr = C /\
        tr_to tr = Alice /\
        tr_amount tr = price + (2 * B2AliceFee)
    ).
Proof.
  intros * C CDS Gen Ss J H Hp R Q HY1 HY2 HY3 HY4 HY5 Al.
  destruct_gen_new_ctr Gen.
  insert_consistent s2 Step.
  insert_consistent s3 Ss.
  induction Step; subst s2.
  - inversion_event InEv.
    apply consistent_impl_exec in inCtr; auto. contradiction.
  - ctr_case_analysis CDSctr ctr.
    execute_own CDSctr H8. subst now.
    rewrite helper_1, helper_2 in H8; try assumption; try unfold Δ; try omega; auto with cds.
    rewrite helper_1, helper_2 in H8; try assumption; try unfold Δ; try omega; auto with cds.
    simpl in *. inversion H8. clear H8. subst.
    repeat rewrite in_app_iff in InCtr0.
    destruct InCtr0 as [In | [In | [In | In]]].
    + apply in_smaller_list in In; try contradiction.
    + eapply pay_at_t_O_rights; eauto. rewrite <- In. simpl. reflexivity.
    + rewrite <- In in R. inversion R.
    + simpl in In. destruct In as [In | In]; try contradiction.
      rewrite <- In in R. inversion R.
  - ctr_case_analysis CDSctr ctr.
    rewrite CDS in H5.  simpl in H5. unfold Top.CDS in H5. inversion H5.
  - ctr_case_analysis CDSctr ctr.
    rewrite CDS in H5.  simpl in H5. unfold Top.CDS in H5. inversion H5.
  - ctr_case_analysis CDSctr ctr.
    execute_own CDSctr H6. subst now.
    rewrite helper_1, helper_2 in H6; try assumption; try unfold Δ; try omega; auto with cds.
    rewrite helper_1, helper_2 in H6; try assumption; try unfold Δ; try omega; auto with cds.
    inversion H6.
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
