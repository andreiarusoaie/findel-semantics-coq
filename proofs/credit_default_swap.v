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

Definition Y1 := 1000.
Definition Y2 := 2000.
Definition Y3 := 3000.

Definition CDS (Alice C : Address)
           (defaulted_addr : Address)
           (price FY F : nat) (now : Time)
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
          (And (At (now + Y1) (Give (Scale F (One USD))))
               (At (now + Y2)
                   (If defaulted_addr
                       (Scale (price + FY) (One USD))
                       Zero)
               )
          )
          (And (At (now + Y2) (Give (Scale F (One USD))))
               (At (now + Y3)
                   (If defaulted_addr
                       (Scale price (One USD))
                       Zero)
               )
          )
      )
  ).

Print generates.
Check executed.
Print CDS.
(* Issuer : = C
   Owner := Alice
 *)
Check finctr.
Proposition CDS_prop:
  forall s1 s2 CDSctr CDSctr_id dsc_id Alice C defaulted_addr price B2AliceFee Alice2CFee defaulted_ctr state1 state2 state3 state4 response,
    consistent_state s1 ->
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         B2AliceFee Alice2CFee (m_global_time state1))
                    C Alice Alice 1->
    s1 ~~> state1 ->
    (* ctr is executed between state1 and state2 *)
    step state1 state2 ->
    In CDSctr (m_contracts state1) ->
    In (Executed (ctr_id CDSctr)) (m_events state2) ->

    (* defaulted_ctr = At (now + 1) ... is generated *)
    ~ In defaulted_ctr (m_contracts state1) ->
    In defaulted_ctr (m_contracts state2) ->
    (ctr_primitive defaulted_ctr = (At ((m_global_time state1) + Y1)
               (If defaulted_addr
                   (Scale (price + (2 * B2AliceFee)) (One USD))
                   Zero)
    )) ->

    (* defaulted_ctr is executed *)
    query (m_gateway state1) defaulted_addr (m_global_time state1) = Some response ->
    response <> 0 ->
    (forall t s, t >= (m_global_time state3) ->
               query (m_gateway s) defaulted_addr t = Some response) -> (* consistent defaulted_addr *)
    state2 ~~> state3 ->
    step state3 state4 ->
    In defaulted_ctr (m_contracts state3) ->
    In (Executed (ctr_id defaulted_ctr)) (m_events state4) ->

    state4 ~~> s2 ->

    m_global_time state1 > Δ ->
    (* conclusion *)
    (exists tr,
        In tr (m_ledger s2) /\
        tr_ctr_id tr = (ctr_id defaulted_ctr) /\
        tr_from tr = C /\
        tr_to tr = Alice /\
        tr_amount tr = price + (2 * B2AliceFee)
    ).
Proof.
  intros.
  insert_consistent state1 Ss.
  apply step_implies_execute_result with (s := state1) in H4; auto.
  destruct H4 as [owner [result H4]].
  rewrite H0 in H4. simpl in H4.
  rewrite H10 in H4; auto.
  case_match H4. destruct r.
  case_match H20. destruct r.
  inversion H21. subst. clear H21.
  case_match H4. destruct r.
  case_match H20. destruct r.
  inversion H21. subst. clear H21.
  case_match H4. destruct r.
  case_match H21. destruct r.
  inversion H22. subst. clear H22.
  case_if H4.
  case_if H22.
  - case_if H23; subst.
    + apply ltb_sound_true in H4. contradict H4.
      unfold Y3, Δ. omega.
    + case_if H19.
      case_if H24; subst.
      * apply ltb_sound_true in H19. contradict H19.
        unfold Y2, Δ. omega.
      * case_match H0. destruct r.
        case_match H25. destruct r.
        inversion H26. subst. clear H26.
        case_if H0.
        case_if H26; subst.
        ** case_if H27; rewrite H19 in H0; inversion H0.
        ** case_if H23.
           case_if H27; subst.
           *** apply ltb_sound_true in H23. contradict H23.
               unfold Y1, Δ. omega.
           *** rewrite H21, H23, H25 in H18.
               inversion H18. subst. clear H18.
               apply ltb_sound_true in H4. contradict H4.
               unfold Y3, Δ. omega.
  - subst.
    case_if H19.
    case_if H23; subst.
    + apply ltb_sound_true in H19. contradict H19.
      unfold Y2, Δ. omega.
    + 

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
