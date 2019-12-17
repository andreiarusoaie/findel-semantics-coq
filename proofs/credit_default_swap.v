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
          (* second year *)
          (yearly_check (now + Y1) (now + Y2) defaulted_addr price FY F 1)
          (* third year *)
          (yearly_check (now + Y2) (now + Y3) defaulted_addr price FY F 0)
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
    response <> 0 ->
    O <> 0 -> 
    consistent_state s1 ->
    (exists tr,
        In tr (m_ledger s2) /\
        tr_ctr_id tr = (ctr_id c) /\
        tr_from tr = I /\
        tr_to tr = O /\
        tr_amount tr = sum
    ).
Proof.
  intros * Ctr Exec Q Hr Ho C.
  destruct_exec Exec.
  induction Step; subst s2.
  - inversion_event InEv. find_contradiction InEv.
  - ctr_case_analysis c ctr.
    execute_own c H5.
    case_if H5.
    case_if H9; simpl.
    + subst t.
      rewrite Q in H10.
      destruct response; simpl in *; try contradiction.
      inversion H10. subst.
      eexists.
      split.
      * simpl. left. eauto.
      * repeat split; simpl; trivial.
        resolve_owner H0. omega.
    + subst t. apply ltb_sound_false in H5. contradict H5.
      assert (H' : m_global_time s1 > Δ).
      apply global_time_is_bigger_than_delta. 
      unfold Δ. omega.
  - not_or c ctr H2.
  - not_or c ctr H2.
  - ctr_case_analysis c ctr.
    inversion_event InEv. find_contradiction InEv.
  - find_contradiction InEv.
Qed.

Proposition pay_at_t_not_defaulted:
  forall s1 s2 c t I O addr sum c_id dsc_id,
    c = finctr c_id dsc_id (pay_at_t t addr sum) I O O 1 ->
    is_executed c s1 s2 t ->
    query (m_gateway s1) addr t = Some 0 ->
    O <> 0 -> 
    consistent_state s1 ->
    m_ledger s1 = m_ledger s2.
Proof.
  intros * Ctr Exec Q Ho C.
  destruct_exec Exec.
  induction Step; subst s2.
  - inversion_event InEv. find_contradiction InEv.
  - ctr_case_analysis c ctr.
    execute_own c H5.
    case_if H5.
    case_if H9; simpl.
    + subst t.
      rewrite Q in H10. simpl in *.
      inversion H10. trivial.
    + subst t. apply ltb_sound_false in H5. contradict H5.
      assert (H' : m_global_time s1 > Δ).
      apply global_time_is_bigger_than_delta. 
      unfold Δ. omega.
  - not_or c ctr H2.
  - not_or c ctr H2.
  - ctr_case_analysis c ctr.
    inversion_event InEv. find_contradiction InEv.
  - find_contradiction InEv.
Qed.


(* if defaulted then yearly_checks does not change the ledger *)
Proposition yearly_checks_already_defaulted:
  forall s1 s2 c t t' I O addr sum c_id dsc_id response a2cfee b2afee i,
    c = finctr c_id dsc_id (yearly_check t t' addr sum b2afee a2cfee i) I O O 1 ->
    is_executed c s1 s2 t ->
    (* B defaults *)
    query (m_gateway s1) addr t = Some response ->
    response <> 0 ->
    O <> 0 ->
    consistent_state s1 ->
    m_ledger s1 = m_ledger s2.
Proof.
  intros * C Exec Q1 R Hy1 Hc.
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


Proposition yearly_checks_not_defaulted:
  forall s1 s2 c t t' I O addr sum c_id dsc_id a2cfee b2afee i,
    c = finctr c_id dsc_id (yearly_check t t' addr sum b2afee a2cfee i) I O O 1 ->
    is_executed c s1 s2 t ->
    (* B defaults *)
    query (m_gateway s1) addr t = Some 0 ->
    O <> 0 ->
    consistent_state s1 ->
    t > Δ ->
    t' - Δ > t  -> 
    (exists ctr,
        In ctr (m_contracts s2) /\
        ctr_issuer ctr = I /\
        ctr_owner ctr = O /\
        ctr_primitive ctr = pay_at_t t' addr (sum + i * b2afee)).
Proof.
  intros * C Exec Q1 Hy1 Hc Hy2 Hy3.
  destruct_exec Exec.
  induction Step; subst s2.
  - inversion_event InEv. find_contradiction InEv.
  - ctr_case_analysis c ctr.
    execute_own c H5.
    subst t. simpl.
    case_if H5.
    case_if H9; simpl.
    + subst. rewrite Q1 in H10. simpl in H10.
      case_match H10.
      case_if H8.
      case_if H12.
      * apply ltb_sound_true in H8. contradict H8. omega.
      * destruct r. inversion H13. clear H13. subst.
        inversion H11. clear H11.
        eexists. split.
        apply in_app_iff. right. simpl. left. trivial.
        repeat split; trivial. resolve_owner H0.
    + apply ltb_sound_false in H5. contradict H5. unfold Δ. omega.
  - not_or c ctr H2.
  - not_or c ctr H2.
  - ctr_case_analysis c ctr. inversion_event InEv. find_contradiction InEv.
  - find_contradiction InEv.
Qed.


Proposition yearly_checks_not_defaulted_C_rights:
  forall s1 s2 c t t' I O addr sum c_id dsc_id a2cfee b2afee i,
    c = finctr c_id dsc_id (yearly_check t t' addr sum b2afee a2cfee i) I O O 1 ->
    is_executed c s1 s2 t ->
    (* B defaults *)
    query (m_gateway s1) addr t = Some 0 ->
    O <> 0 ->
    consistent_state s1 ->
    t > Δ ->
    t' - Δ > t  -> 
    (exists tr,
        In tr (m_ledger s2) /\
        tr_ctr_id tr = (ctr_id c) /\
        tr_from tr = O /\
        tr_to tr = I /\
        tr_amount tr = a2cfee).
Proof.
  intros * C Exec Q1 Hy1 Hc Hy2 Hy3.
  destruct_exec Exec.
  induction Step; subst s2.
  - inversion_event InEv. find_contradiction InEv.
  - ctr_case_analysis c ctr.
    execute_own c H5.
    subst t. simpl.
    case_if H5.
    case_if H9; simpl.
    + subst. rewrite Q1 in H10. simpl in H10.
      case_match H10.
      case_if H8.
      case_if H12.
      * destruct r. inversion H13. clear H13. subst.
        inversion H11. clear H11.
        eexists.  simpl. split. left. trivial.
        repeat split; auto.
        simpl. resolve_owner H0.
        simpl. omega.
      * destruct r. inversion H13. clear H13. subst.
        inversion H11. clear H11.
        eexists.  simpl. split. left. trivial.
        repeat split; auto.
        simpl. resolve_owner H0.
        simpl. omega.
    + apply ltb_sound_false in H5. contradict H5. unfold Δ. omega.
  - not_or c ctr H2.
  - not_or c ctr H2.
  - ctr_case_analysis c ctr. inversion_event InEv. find_contradiction InEv.
  - find_contradiction InEv.
Qed.


Lemma h1 :
  forall a b c d,
    a + b - c >= d ->
    a + b + c >= d.
Proof.
  intros.
  omega.
Qed.

Lemma h2 :
  forall a b b' c d,
    a + b - c >= d ->
    b' > b -> 
    a + b' - c >= d.
Proof.
  intros.
  omega.
Qed.
  

(* 
CDS generates three subcontracts:

-> C1 - where Alice can request price + 2 * B2AliceFee from C if B defaults in the first year
-> C2 - where Alice can require price + 1 * B2AliceFee from C if B defaults in the second year
-> C3 - where Alice can require price + 0 * B2AliceFee from C if B defaults in the third year
*) 


(*
Scenario: B defaults in the first year.
Facts proved below:
1. Alice receives price + 2 * B2AliceFee as specified by C1 
2. C does not pay anyhting if Alice joins C2 or C3
3. C receives Alice2CFee from Alice
*)

Proposition CDS_Y1_C1_Alice_is_paid_by_C :
  forall CDSctr c' CDSctr_id dsc_id Alice C defaulted_addr
         price b2afee a2cfee s1 s2 s3 s4 now Y1 Y2 Y3,
    (* the execution of CDS generates 3 new contracts *)
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         b2afee a2cfee now Y1 Y2 Y3)
                    C Alice Alice 1 ->
    is_executed CDSctr s1 s2 now -> 
    query (m_gateway s1) defaulted_addr now = Some 0 ->

    (* new contracts are joined by Alice *)
    ~ In c' (m_contracts s1) ->
    In c' (m_contracts s2) ->
    s2 ~~> s3 ->
    is_executed c' s3 s4 (now + Y1) ->
    (* default after 1 year *)
    query (m_gateway s3) defaulted_addr (now + Y1) = Some 1 ->


    (* details *)
    Alice <> 0 ->
    now > Δ ->
    Y1 > Δ ->
    Y2 > Δ ->
    consistent_state s1 ->

    (* If Alice joins C1, then Alice obtains the money *)
    (ctr_primitive c' = pay_at_t (now + Y1) defaulted_addr (price + (2 * b2afee)) -> 
      exists tr,
        In tr (m_ledger s4) /\
        tr_ctr_id tr = (ctr_id c') /\
        tr_from tr = C /\
        tr_to tr = Alice /\
        tr_amount tr = price + (2 * b2afee)
    ).
Proof.
  intros * CDS Exec1 Q1 NIn InCtr Ss Exec2 Q2 Ho Hn Hy1 Hy2 Cst Prim.
  destruct_exec Exec1.
  insert_consistent s2 Step.
  insert_consistent s3 Ss.
  induction Step; subst s2.
  - inversion_event InEv.
    apply consistent_impl_exec in InCtr0; auto. contradiction.
  - ctr_case_analysis CDSctr ctr. clear H8.
    execute_own CDSctr H7. simpl in *.
    subst now.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    inversion H7. clear H7. subst.
    repeat rewrite in_app_iff in InCtr.
    destruct InCtr as [InCtr | InCtr].
    + apply in_smaller_list in InCtr. contradiction.
    + simpl in InCtr. destruct InCtr as [InCtr | [InCtr | [InCtr | InCtr]]]; try contradiction.
      * resolve_owner H2.
        eapply pay_at_t_O_rights; eauto. unfold pay_at_t, At. eauto.
      * subst c'. simpl in Prim. unfold pay_at_t, At in Prim. inversion Prim.
      * subst c'. simpl in Prim. unfold pay_at_t, At in Prim. inversion Prim.
  - not_or ctr CDSctr H4.
  - not_or ctr CDSctr H4.
  - ctr_case_analysis CDSctr ctr.
    execute_own CDSctr H5. inversion InEv.
    apply consistent_impl_exec in InCtr0; auto. inversion H7; auto.
    find_contradiction InEv.
  - simpl in InCtr. contradiction.
Qed.


(* Even if Alice joins C2 at Y2, the ledger is unchanged  *)
Proposition CDS_Y1_C2_nobody_is_paid:
  forall CDSctr c' CDSctr_id dsc_id Alice C defaulted_addr
         price b2afee a2cfee s1 s2 s3 s4 now Y1 Y2 Y3,
    (* the execution of CDS generates 3 new contracts *)
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         b2afee a2cfee now Y1 Y2 Y3)
                    C Alice Alice 1 ->
    is_executed CDSctr s1 s2 now -> 
    query (m_gateway s1) defaulted_addr now = Some 0 ->

    (* new contracts are joined by Alice *)
    ~ In c' (m_contracts s1) ->
    In c' (m_contracts s2) ->
    s2 ~~> s3 ->
    is_executed c' s3 s4 (now + Y1) ->
    (* default after 1 year *)
    query (m_gateway s3) defaulted_addr (now + Y1) = Some 1 ->

    (* details *)
    Alice <> 0 ->
    now > Δ ->
    Y1 > Δ ->
    Y2 > Δ ->
    Y2 > Y1 ->
    consistent_state s1 ->

    (* If Alice joins C2, the ledger remains unchanged *)
    ( ctr_primitive c' = yearly_check (now + Y1) (now + Y2) defaulted_addr price b2afee a2cfee 1 ->
      m_ledger s3 = m_ledger s4
    ).
Proof.
  intros * CDS Exec1 Q1 NIn InCtr Ss Exec2 Q2 Ho Hn Hy1 Hy2 Hy3 Cst Prim.
  destruct_exec Exec1.
  insert_consistent s2 Step.
  insert_consistent s3 Ss.
  induction Step; subst s2.
  - inversion_event InEv.
    apply consistent_impl_exec in InCtr0; auto. contradiction.
  - ctr_case_analysis CDSctr ctr. clear H8.
    execute_own CDSctr H7. simpl in *.
    subst now.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    inversion H7. clear H7. subst.
    repeat rewrite in_app_iff in InCtr.
    destruct InCtr as [InCtr | InCtr].
    + apply in_smaller_list in InCtr. contradiction.
    + simpl in InCtr. destruct InCtr as [InCtr | [InCtr | [InCtr | InCtr]]]; try contradiction.
      * subst c'. inversion Prim.
      * resolve_owner H2.
        eapply yearly_checks_already_defaulted; eauto.
        unfold yearly_check, At.
        instantiate (2 := b2afee). instantiate (2 := 1).
        exact Exec2.
      * subst c'. inversion Prim.
        contradict H9. omega.
  - not_or ctr CDSctr H4.
  - not_or ctr CDSctr H4.
  - ctr_case_analysis CDSctr ctr.
    execute_own CDSctr H5. inversion InEv.
    apply consistent_impl_exec in InCtr0; auto. inversion H7; auto.
    find_contradiction InEv.
  - simpl in InCtr. contradiction.
Qed.

Proposition CDS_Y1_Alice_is_not_paid_at_Y3:
  forall CDSctr c' CDSctr_id dsc_id Alice C defaulted_addr
         price b2afee a2cfee s1 s2 s3 s4 now Y1 Y2 Y3,
    (* the execution of CDS generates 3 new contracts *)
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         b2afee a2cfee now Y1 Y2 Y3)
                    C Alice Alice 1 ->
    is_executed CDSctr s1 s2 now -> 
    query (m_gateway s1) defaulted_addr now = Some 0 ->

    (* new contracts are joined by Alice *)
    ~ In c' (m_contracts s1) ->
    In c' (m_contracts s2) ->
    s2 ~~> s3 ->
    is_executed c' s3 s4 (now + Y2) ->
    (* default after 1 year *)
    query (m_gateway s3) defaulted_addr (now + Y2) = Some 1 ->

    (* details *)
    Alice <> 0 ->
    now > Δ ->
    Y1 > Δ ->
    Y2 > Δ ->
    Y3 > Y2 ->
    consistent_state s1 ->

    (* If Alice joins C3, the ledger remains unchanged *)
    (ctr_primitive c' = yearly_check (now + Y2) (now + Y3) defaulted_addr price b2afee a2cfee 0 ->
      m_ledger s3 = m_ledger s4
    ).
Proof.
  intros * CDS Exec1 Q1 NIn InCtr Ss Exec2 Q2 Ho Hn Hy1 Hy2 Hy3 Cst Prim.
  destruct_exec Exec1.
  insert_consistent s2 Step.
  insert_consistent s3 Ss.
  induction Step; subst s2.
  - inversion_event InEv.
    apply consistent_impl_exec in InCtr0; auto. contradiction.
  - ctr_case_analysis CDSctr ctr. clear H8.
    execute_own CDSctr H7. simpl in *.
    subst now.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    inversion H7. clear H7. subst.
    repeat rewrite in_app_iff in InCtr.
    destruct InCtr as [InCtr | InCtr].
    + apply in_smaller_list in InCtr. contradiction.
    + simpl in InCtr. destruct InCtr as [InCtr | [InCtr | [InCtr | InCtr]]]; try contradiction.
      * subst c'. inversion Prim.
      * subst c'. inversion Prim.
        contradict H9. omega.
      * resolve_owner H2.
        eapply yearly_checks_already_defaulted; eauto.
        unfold yearly_check, At.
        instantiate (2 := b2afee). instantiate (2 := 0).
        exact Exec2.
  - not_or ctr CDSctr H4.
  - not_or ctr CDSctr H4.
  - ctr_case_analysis CDSctr ctr.
    execute_own CDSctr H5. inversion InEv.
    apply consistent_impl_exec in InCtr0; auto. inversion H7; auto.
    find_contradiction InEv.
  - simpl in InCtr. contradiction.
Qed.


Proposition CDS_Y1_C_gets_paid :
  forall CDSctr CDSctr_id dsc_id Alice C defaulted_addr
         price b2afee a2cfee s1 s2 now Y1 Y2 Y3,
    (* the execution of CDS generates 3 new contracts *)
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         b2afee a2cfee now Y1 Y2 Y3)
                    C Alice Alice 1 ->
    is_executed CDSctr s1 s2 now -> 

    (* details *)
    Alice <> 0 ->
    now > Δ ->
    Y1 > Δ ->
    Y2 > Δ ->
    consistent_state s1 ->

    (* If Alice joins C1, then Alice pays C an yearly fee *)
    (exists tr,
        In tr (m_ledger s2) /\
        tr_ctr_id tr = (ctr_id CDSctr) /\
        tr_from tr = Alice /\
        tr_to tr = C /\
        tr_amount tr = a2cfee
    ).
Proof.
  intros * CDS Exec Ho Hy1 Hy2 Hy3 Cst.
  destruct_exec Exec.
  insert_consistent s2 Step.
  induction Step; subst s2.
  - inversion_event InEv. find_contradiction InEv.
  - ctr_case_analysis CDSctr ctr. clear H7.
    execute_own CDSctr H6. simpl in *.
    subst now.
    rewrite helper_1, helper_2 in H6; unfold Δ; try auto; try omega.
    rewrite helper_1, helper_2 in H6; unfold Δ; try auto; try omega.
    inversion H6. clear H6. subst.
    eexists. split. simpl. left. trivial.
    repeat split; trivial. simpl. resolve_owner H1.
    simpl. auto.
  - not_or ctr CDSctr H3.
  - not_or ctr CDSctr H3.
  - ctr_case_analysis CDSctr ctr.
    inversion_event InEv. find_contradiction InEv.
  - find_contradiction InEv.
Qed.













































(*
Scenario: B defaults in the second year.
Facts proved below:
1. Alice receives price + 1 * B2AliceFee as specified by C2 
2. C does not pay anyhting if Alice joins C1 or C3
3. C receives 2 * Alice2CFee from Alice in two transactions
*)

(* If Alice joins C1, the ledger remains unchanged *)
Proposition CDS_Y2_Alice_is_not_paid_if_joins_C1 :
  forall CDSctr c' CDSctr_id dsc_id Alice C defaulted_addr
         price b2afee a2cfee s1 s2 s3 s4 now Y1 Y2 Y3,
    (* the execution of CDS generates 3 new contracts *)
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         b2afee a2cfee now Y1 Y2 Y3)
                    C Alice Alice 1 ->
    is_executed CDSctr s1 s2 now -> 
    query (m_gateway s1) defaulted_addr now = Some 0 ->

    (* new contracts are joined by Alice *)
    ~ In c' (m_contracts s1) ->
    In c' (m_contracts s2) ->
    s2 ~~> s3 ->
    (forall t, t >= now + Y1 -> is_executed c' s3 s4 t) ->
    (* still not defaulted *)
    query (m_gateway s3) defaulted_addr (now + Y1) = Some 0 ->
    (* default after 2 years *)
    query (m_gateway s3) defaulted_addr (now + Y2) = Some 1 ->


    (* details *)
    Alice <> 0 ->
    now > Δ ->
    Y1 > Δ ->
    Y2 > Δ ->
    consistent_state s1 ->

    (* If Alice joins C1, nothing happens *)
    (ctr_primitive c' = pay_at_t (now + Y1) defaulted_addr (price + (2 * b2afee)) -> 
     m_ledger s3 = m_ledger s4).
Proof.
  intros * CDS Exec1 Q1 NIn InCtr Ss Exec2 Q2 Q3 Ho Hn Hy1 Hy2 Cst Prim.
  destruct_exec Exec1.
  insert_consistent s2 Step.
  insert_consistent s3 Ss.
  induction Step; subst s2.
  - inversion_event InEv.
    apply consistent_impl_exec in InCtr0; auto. contradiction.
  - ctr_case_analysis CDSctr ctr. clear H8.
    execute_own CDSctr H7. simpl in *.
    subst now.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    inversion H7. clear H7. subst.
    repeat rewrite in_app_iff in InCtr.
    destruct InCtr as [InCtr | InCtr].
    + apply in_smaller_list in InCtr. contradiction.
    + simpl in InCtr. destruct InCtr as [InCtr | [InCtr | [InCtr | InCtr]]]; try contradiction.
      * resolve_owner H2.
        eapply pay_at_t_not_defaulted; eauto.
      * subst c'. inversion Prim.
      * subst c'. inversion Prim.
  - not_or ctr CDSctr H4.
  - not_or ctr CDSctr H4.
  - ctr_case_analysis CDSctr ctr.
    execute_own CDSctr H5. inversion InEv.
    apply consistent_impl_exec in InCtr0; auto. inversion H7; auto.
    find_contradiction InEv.
  - simpl in InCtr. contradiction.
Qed.


(*
If Alice joins C2, a new contract is generated, where:
1.  Alice is the owner
2.  C is the issuer
3. the primitive is pat_at_t
4. the value of the contract is price + b2afee
*)
Proposition CDS_Y2_C2:
  forall CDSctr c' CDSctr_id dsc_id Alice C defaulted_addr
         price b2afee a2cfee s1 s2 s3 s4 now Y1 Y2 Y3,
    (* the execution of CDS generates 3 new contracts *)
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         b2afee a2cfee now Y1 Y2 Y3)
                    C Alice Alice 1 ->
    is_executed CDSctr s1 s2 now -> 
    query (m_gateway s1) defaulted_addr now = Some 0 ->

    (* new contracts are joined by Alice *)
    ~ In c' (m_contracts s1) ->
    In c' (m_contracts s2) ->
    s2 ~~> s3 ->
    is_executed c' s3 s4 (now + Y1) ->
    (* still not defaulted *)
    query (m_gateway s3) defaulted_addr (now + Y1) = Some 0 ->
    (* default after 2 years *)
    query (m_gateway s3) defaulted_addr (now + Y2) = Some 1 ->


    (* details *)
    Alice <> 0 ->
    now > Δ ->
    Y1 > Δ ->
    Y2 > Δ ->
    Y2 -Y1 > Δ ->
    consistent_state s1 ->

    (* If Alice joins C2, then a contract is generated *)
    (ctr_primitive c' = yearly_check (now + Y1) (now + Y2)
                                     defaulted_addr price b2afee a2cfee 1  ->
     (exists ctr,
         In ctr (m_contracts s4) /\
         ctr_issuer ctr = C /\
         ctr_owner ctr = Alice /\
         (ctr_primitive ctr = pay_at_t (now + Y2) defaulted_addr (price + 1 * b2afee)))
    ).
Proof.
  intros * CDS Exec1 Q1 NIn InCtr Ss Exec2 Q2 Ho Hn Hy1 Hy2 Hy3 Hy4 Cst Prim.
  destruct_exec Exec1.
  insert_consistent s2 Step.
  insert_consistent s3 Ss.
  induction Step; subst s2.
  - inversion_event InEv.
    apply consistent_impl_exec in InCtr0; auto. contradiction.
  - ctr_case_analysis CDSctr ctr. clear H8.
    execute_own CDSctr H7. simpl in *.
    subst now.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    inversion H7. clear H7. subst.
    repeat rewrite in_app_iff in InCtr.
    destruct InCtr as [InCtr | InCtr].
    + apply in_smaller_list in InCtr. contradiction.
    + simpl in InCtr. destruct InCtr as [InCtr | [InCtr | [InCtr | InCtr]]]; try contradiction.
      * subst c'. inversion Prim.
      * eapply yearly_checks_not_defaulted in Exec2; try destruct Exec2 as [cpay [In [Is [Ow CPrim]]]]; eauto; try omega.
        ** exists cpay. repeat split; eauto.
           assert (H' : price + (b2afee + 0) = price + (1 * b2afee)); try omega.
           rewrite H'. exact CPrim.
        ** resolve_owner H2. unfold yearly_check, At. eauto.
        ** omega. 
      * subst c'. inversion Prim.
        contradict H9. omega.
  - not_or ctr CDSctr H4.
  - not_or ctr CDSctr H4.
  - ctr_case_analysis CDSctr ctr.
    execute_own CDSctr H5. inversion InEv.
    apply consistent_impl_exec in InCtr0; auto. inversion H7; auto.
    find_contradiction InEv.
  - simpl in InCtr. contradiction.
Qed.

Proposition CDS_Y2_C3:
  forall CDSctr c' CDSctr_id dsc_id Alice C defaulted_addr
         price b2afee a2cfee s1 s2 s3 s4 now Y1 Y2 Y3,
    (* the execution of CDS generates 3 new contracts *)
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         b2afee a2cfee now Y1 Y2 Y3)
                    C Alice Alice 1 ->
    is_executed CDSctr s1 s2 now -> 
    query (m_gateway s1) defaulted_addr now = Some 0 ->

    (* new contracts are joined by Alice *)
    ~ In c' (m_contracts s1) ->
    In c' (m_contracts s2) ->
    s2 ~~> s3 ->
    is_executed c' s3 s4 (now + Y2) ->
    (* default after 2 years *)
    query (m_gateway s3) defaulted_addr (now + Y2) = Some 1 ->


    (* details *)
    Alice <> 0 ->
    now > Δ ->
    Y1 > Δ ->
    Y2 > Δ ->
    Y3 - Y2 > Δ ->
    consistent_state s1 ->

    (* If Alice joins C2, then a contract is generated *)
    (ctr_primitive c' = yearly_check (now + Y2) (now + Y3)
                                     defaulted_addr price b2afee a2cfee 1  ->
      m_ledger s3 = m_ledger s4
    ).
Proof.
  intros * CDS Exec1 Q1 NIn InCtr Ss Exec2 Q2 Ho Hn Hy1 Hy2 Hy3 Cst Prim.
  destruct_exec Exec1.
  insert_consistent s2 Step.
  insert_consistent s3 Ss.
  induction Step; subst s2.
  - inversion_event InEv.
    apply consistent_impl_exec in InCtr0; auto. contradiction.
  - ctr_case_analysis CDSctr ctr. clear H8.
    execute_own CDSctr H7. simpl in *.
    subst now.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    inversion H7. clear H7. subst.
    repeat rewrite in_app_iff in InCtr.
    destruct InCtr as [InCtr | InCtr].
    + apply in_smaller_list in InCtr. contradiction.
    + simpl in InCtr. destruct InCtr as [InCtr | [InCtr | [InCtr | InCtr]]]; try contradiction.
      * subst c'. inversion Prim.
      * subst c'. inversion Prim.
        contradict H9. omega.
      * resolve_owner H2.
        eapply yearly_checks_already_defaulted; eauto.
        unfold yearly_check, At.
        instantiate (2 := b2afee). instantiate (2 := 0).
        exact Exec2.
  - not_or ctr CDSctr H4.
  - not_or ctr CDSctr H4.
  - ctr_case_analysis CDSctr ctr.
    execute_own CDSctr H5. inversion InEv.
    apply consistent_impl_exec in InCtr0; auto. inversion H7; auto.
    find_contradiction InEv.
  - simpl in InCtr. contradiction.
Qed.


Proposition CDS_Y2_C_gets_paid :
  forall CDSctr CDSctr_id dsc_id Alice C defaulted_addr
         price c' b2afee a2cfee s1 s2 s3 s4 now Y1 Y2 Y3,
    (* the execution of CDS generates 3 new contracts *)
    CDSctr = finctr CDSctr_id dsc_id
                    (CDS Alice C defaulted_addr price
                         b2afee a2cfee now Y1 Y2 Y3)
                    C Alice Alice 1 ->
    is_executed CDSctr s1 s2 now -> 
    query (m_gateway s1) defaulted_addr now = Some 0 ->

    (* new contracts are joined by Alice *)
    ~ In c' (m_contracts s1) ->
    In c' (m_contracts s2) ->
    s2 ~~> s3 ->
    is_executed c' s3 s4 (now + Y1) ->
    (* still not defaulted *)
    query (m_gateway s3) defaulted_addr (now + Y1) = Some 0 ->
    (* default after 2 years *)
    query (m_gateway s3) defaulted_addr (now + Y2) = Some 1 ->


    (* details *)
    Alice <> 0 ->
    now > Δ ->
    Y1 > Δ ->
    Y2 > Δ ->
    Y2 -Y1 > Δ ->
    consistent_state s1 ->

    (* If Alice joins C2, then she pays a second fee to C *)
    (ctr_primitive c' = yearly_check (now + Y1) (now + Y2)
                                     defaulted_addr price b2afee a2cfee 1  ->
     (exists tr,
         In tr (m_ledger s4) /\
         tr_ctr_id tr = (ctr_id c') /\
         tr_from tr = Alice /\
         tr_to tr = C /\
         tr_amount tr = a2cfee
     )).
Proof.
  intros * CDS Exec1 Q1 NIn InCtr Ss Exec2 Q2 Ho Hn Hy1 Hy2 Hy3 Hy4 Cst Prim.
  destruct_exec Exec1.
  insert_consistent s2 Step.
  insert_consistent s3 Ss.
  induction Step; subst s2.
  - inversion_event InEv.
    apply consistent_impl_exec in InCtr0; auto. contradiction.
  - ctr_case_analysis CDSctr ctr. clear H8.
    execute_own CDSctr H7. simpl in *.
    subst now.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    rewrite helper_1, helper_2 in H7; unfold Δ; try auto; try omega.
    inversion H7. clear H7. subst.
    repeat rewrite in_app_iff in InCtr.
    destruct InCtr as [InCtr | InCtr].
    + apply in_smaller_list in InCtr. contradiction.
    + simpl in InCtr. destruct InCtr as [InCtr | [InCtr | [InCtr | InCtr]]]; try contradiction.
      * subst c'. inversion Prim.
      * resolve_owner H2.
        eapply yearly_checks_not_defaulted_C_rights; eauto. unfold yearly_check, At; try omega.
        assert (H' : (price + (b2afee + 0)) = price + 1 * b2afee); try omega.
        rewrite H'. eauto.
        repeat try omega.
        omega.
      * subst c'. inversion Prim.
        contradict H9. omega.
  - not_or ctr CDSctr H4.
  - not_or ctr CDSctr H4.
  - ctr_case_analysis CDSctr ctr.
    inversion_event InEv.
    apply consistent_impl_exec in InCtr0; auto. contradiction.
  - apply consistent_impl_exec in InCtr0; auto. contradiction. 
Qed.









