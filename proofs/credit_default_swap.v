Load metaproperties.

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
           (addr : Address)
           (sum : nat) :=
  (At t
      (If addr
          (Scale sum (One USD))
          Zero)
  ).


Definition yearly_check (t t' : Time)
           (addr : Address)
           (price B2AliceFee Alice2CFee i : nat)
  :=
    At t (If addr Zero
             (And (Give (Scale Alice2CFee (One USD)))
                  (pay_at_t t' addr (price + i * B2AliceFee)))).

Definition CDS (Alice C : Address)
           (defaulted_addr : Address)
           (price FY F : nat) (now : Time)
           (Y1 Y2 Y3 : nat)
  :=
  (
    And
      (* first year *)
      (And (Give (Scale F (One USD)))
           (pay_at_t (now + Y1) defaulted_addr (price + (2 * FY)))
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
  destruct H as [Step [InCtr [InEv T]]].

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
    c = finctr c_id dsc_id (pay_at_t t addr sum) I O O 1 ->
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


(* if B defaulted then yearly checks do not change the ledger *)
Proposition yearly_checks_O_rights_not_defaulted:
  forall s1 s2 c t t' I O addr sum c_id dsc_id response a2cfee b2afee i,
    c = finctr c_id dsc_id (yearly_check t t' addr sum a2cfee b2afee i) I O O 1 ->
    is_executed c s1 s2 t ->
    (* B defaults *)
    query (m_gateway s1) addr t = Some response ->
    can_join O c ->
    O <> 0 ->
    response <> 0 ->
    consistent_state s1 ->
    m_ledger s1 = m_ledger s2.
Proof.
  intros * C Exec Q1 J Hy1 R Hc.
  destruct_exec Exec.
  induction Step; subst s2.
  - inversion_event InEv. find_contradiction InEv.
  - ctr_case_analysis c ctr.
    execute_own c H5.
    subst t. simpl.
    case_if H5.
    case_if H9; simpl.
    + rewrite Q1 in H10. simpl in H10.
      destruct response; try contradiction. simpl in H10.
      inversion H10. clear H10. subst. trivial.
    + trivial.
  - not_or c ctr H2.
  - not_or c ctr H2.
  - ctr_case_analysis c ctr. inversion_event InEv. find_contradiction InEv.
  - find_contradiction InEv.
Qed.


Proposition yearly_checks_O_rights_defaulted:
  forall s1 s2 s3 s4 c c' t t' I O addr price c_id dsc_id response a2cfee b2afee i sum,
    c = finctr c_id dsc_id (yearly_check t t' addr price b2afee a2cfee i) I O O 1 ->
    (* execute yearly_checks first; it can generate a new contract *)
    generates_new_ctr_when_executed_at c c' O s1 s2 t ->
    (* B does not default in s1 *)
    query (m_gateway s1) addr (m_global_time s1) = Some 0 ->

    (* several steps later *)
    s2 ~~> s3 ->

    (* execute c' at t', when B defaults *)
    t' > t ->
    t' - Δ > t ->
    can_join O c' ->
    is_executed c' s3 s4 (t') ->
    (ctr_primitive c') = pay_at_t t' addr (price + i * b2afee) ->
    query (m_gateway s3) addr t' = Some response ->
    response <> 0 ->


    (* technical conditions  *)
    O <> 0 ->
    consistent_state s1 ->
    (* conclusion *)
    sum = price + (i * b2afee) -> 
    (exists tr,
        In tr (m_ledger s4) /\
        tr_ctr_id tr = (ctr_id c') /\
        tr_from tr = I /\
        tr_to tr = O /\
        tr_amount tr = sum
    ).
Proof.
  intros * C Gen Q1 R Ss Hy1 Hy2 J Exec Hc Ht Ht' Cs IH.
  destruct_gen_new_ctr Gen.
  insert_consistent s2 Cs.
  insert_consistent s3 Cs.
  induction Step; subst s2.
  - inversion_event InEv.
    apply consistent_impl_exec in inCtr; auto. contradiction.
  - ctr_case_analysis c ctr. clear H8.
    execute_own c H7. simpl in *.
    case_if H7. subst t.
    case_if H10.
    + rewrite Q1 in H11.
      destruct response; try contradiction; simpl in H11.
      case_match H11.
      destruct r. inversion H12. subst. clear H12.
      case_if H9.
      case_if H12; subst.
      * apply ltb_sound_true in H9. contradict H9. omega.
      * rewrite in_app_iff in InCtr0.
        destruct InCtr0 as [I1 | I1].
        ** apply in_smaller_list in I1. contradiction.
        ** simpl in I1. destruct I1 as [I1 | I1]; try contradiction.
           eapply pay_at_t_O_rights; eauto.
           unfold pay_at_t, At.
           rewrite <- I1. eauto.
    + subst. apply ltb_sound_false in H7. contradict H7.
      assert (H' : m_global_time s1 > Δ).
      apply global_time_is_bigger_than_delta.
      unfold Δ. omega.
  - not_or c ctr H4.
  - not_or c ctr H4.
  - ctr_case_analysis c ctr. inversion_event InEv.
     apply consistent_impl_exec in inCtr; auto. contradiction.
  -  apply consistent_impl_exec in inCtr; auto. contradiction.
Qed.



(* Alice's rights if Bob defaults after 1 year:
      C pays to Alice price + 2 * Bob2AliceFee *)
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
    (* B does not default in s1 *)
    query (m_gateway s1) defaulted_addr (m_global_time s1) = Some 1 ->

    (* several steps later *)
    s2 ~~> s3 ->

    (* execute c' at now + Y1, when B defaults *)
    can_join Alice c' ->
    is_executed c' s3 s4 (now + Y1) ->
    (ctr_primitive c') = pay_at_t (now + Y1) defaulted_addr (price + 2 * B2AliceFee) ->
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




(* C's rights if Bob defaults after 1 year:
      Alice pays to C only Alice2CFee *)
Proposition CDS_defaulted_in_Y1_C_rights:
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
    (* B does not default in s1 *)
    query (m_gateway s1) defaulted_addr (m_global_time s1) = Some 1 ->

    (* several steps later *)
    s2 ~~> s3 ->

    (* execute c' at now + Y1, when B defaults *)
    can_join Alice c' ->
    is_executed c' s3 s4 (now + Y1) ->
    (ctr_primitive c') = pay_at_t (now + Y1) defaulted_addr (price + 2 * B2AliceFee) ->
    response <> 0 ->
    (* in s3, B defaults and C has to pay Alice *)
    query (m_gateway s3) defaulted_addr (m_global_time s1 + Y1) = Some 1 ->


    (* technical conditions: a year has more greater than 30 sec. :-) *)
    Y1 > Δ -> Y2 > Δ -> Y3 > Δ -> Y2 - Y1 > Δ -> Y3 - Y2 > Δ ->
    Alice <> 0 ->
    (* conclusion *)
    (exists tr,
        In tr (m_ledger s4) /\
        tr_ctr_id tr = CDSctr_id /\
        tr_from tr = Alice /\
        tr_to tr = C /\
        tr_amount tr = Alice2CFee
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
    eexists. split.
    + eapply steps_does_not_remove_transactions; eauto.
      eapply tran. exact J.
      destruct_exec Hp. eauto.
      simpl. left. eauto.
    + repeat split; trivial. simpl.
      resolve_owner H3. simpl. auto.
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



(* Alice's rights if Bob defaults after 2 years:
      C pays to Alice price + 1 * Bob2AliceFee *)
Print yearly_check.
Proposition CDS_defaulted_in_Y2_Alice_rights:
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
    (* B does not default in s1 *)
    query (m_gateway s1) defaulted_addr (m_global_time s1) = Some 0 ->

    (* several steps later *)
    s2 ~~> s3 ->

    (* execute c' at now + Y1, when B defaults *)
    can_join Alice c' ->
    is_executed c' s3 s4 (now + Y1) ->
    (ctr_primitive c') = yearly_check (now + Y1) (now + Y2) defaulted_addr price B2AliceFee Alice2CFee 2 ->

    response <> 0 ->
    (* in s3, B defaults and C has to pay Alice *)
    query (m_gateway s3) defaulted_addr (now + Y2) = Some 1 ->


    (* technical conditions: a year has more greater than 30 sec. :-) *)
    Y1 > Δ -> Y2 > Δ -> Y3 > Δ -> Y2 - Y1 > Δ -> Y3 - Y2 > Δ ->
    Alice <> 0 ->
    (* conclusion *)
    (exists tr,
        In tr (m_ledger s4) /\
        tr_ctr_id tr = (ctr_id c') /\
        tr_from tr = C /\
        tr_to tr = Alice /\
        tr_amount tr = price + (1 * B2AliceFee)
    ).
Proof.
  intros * C CDS Gen Ss Q1 J H Hp R Q2 HY1 HY2 HY3 HY4 HY5 Al.
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
    + rewrite <- In in Hp. inversion Hp.
    + eapply yearly_checks_O_rights_defaulted. eauto; simpl.
      admit.
    + simpl in In. destruct In as [In | In]; try contradiction.
      unfold yearly_check, pay_at_t, At in Hp.
      rewrite <- In in Hp. simpl in Hp. inversion Hp.
      contradict H10. omega.
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
