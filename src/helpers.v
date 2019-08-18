Load findel.
Require Import Classical.

Lemma n_plus_m_not_less_than_n : forall n m, n + m <? n = false.
Proof.
  unfold Nat.ltb, Nat.leb.
  induction n; intros; simpl; trivial.
Qed.


Definition consistent_ctr_ids (s : State) := 
  forall x y, In x (m_contracts s) ->
              In y (m_contracts s) ->
              ctr_id x = ctr_id y ->
              x = y.


Notation "A → B ⊢ C" := (step A B /\ consistent_ctr_ids A /\
                         ~ In (Executed C) (m_events A) /\
                         In (Executed C) (m_events B))
                          (at level 80).

Notation "A ⇓ B ⊢ C" := (steps A B /\ consistent_ctr_ids A /\
                         ~ In (Executed C) (m_events A) /\
                         In (Executed C) (m_events B))
                          (at level 80).

Notation "# T ∈ L | I | A --> B | V $ C #" := (In T L /\
                                               (tr_ctr_id T = I) /\
                                               (tr_from T = A) /\
                                               (tr_to T = B) /\
                                               (tr_amount T = V) /\
                                               (tr_currency T = C))
                                                (at level 80).
Notation "% C ∈ L | A --> B | P %" := (In C L /\
                                       (ctr_issuer C = A) /\
                                       (ctr_owner C = B) /\
                                       (ctr_primitive C = P))
                                        (at level 80).


Lemma execute_det:
  forall s1 s2 ctr ctr',
    step s1 s2 ->
    consistent_ctr_ids s1 ->
    In ctr (m_contracts s1) ->
    In ctr' (m_contracts s1) ->
    ~ In (Executed (ctr_id ctr)) (m_events s1) ->
    ~ In (Executed (ctr_id ctr')) (m_events s1) ->
    In (Executed (ctr_id ctr)) (m_events s2) ->
    In (Executed (ctr_id ctr')) (m_events s2) ->
    ctr = ctr'.
Proof.
  intros s1 s2 ctr ctr' H.
  revert ctr ctr'.
  induction H; intros; subst s2.
  - unfold append_new_ctr_to_state in H11.
    simpl in H11.
    destruct H11 as [H11 | H11]; try inversion H11; try contradiction.
  - simpl in H12, H13.
    destruct H12 as [H12 | H12]; try contradiction.
    destruct H13 as [H13 | H13]; try contradiction.
    inversion H12. inversion H13. clear H13 H12.
    unfold consistent_ctr_ids in H7.
    apply H7; auto.
    rewrite <- H14, H15. trivial.
  - simpl in H12, H13.
    destruct H12 as [H12 | H12]; try contradiction.
    destruct H13 as [H13 | H13]; try contradiction.
    inversion H12. inversion H13. clear H13 H12.
    unfold consistent_ctr_ids in H7.
    apply H7; auto.
    rewrite <- H14, H15. trivial.
  - simpl in H12, H13.
    destruct H12 as [H12 | H12]; try contradiction.
    destruct H13 as [H13 | H13]; try contradiction.
    inversion H12. inversion H13. clear H13 H12.
    unfold consistent_ctr_ids in H7.
    apply H7; auto.
    rewrite <- H14, H15. trivial.
  - destruct H11 as [H11 | H11].
    inversion H11.
    contradiction.
  - contradiction.
Qed.


Lemma primitive_execution_modifies_ledger:
  forall primitive scale issuer owner balance
         time gateway ctr_id dsc_id next ledger
         balance' ctrs' next' ledger',
    execute primitive scale issuer owner balance
                      time gateway ctr_id dsc_id next ledger
    =
    Some (result balance' ctrs' next' ledger') ->
    exists new_transactions, ledger' = new_transactions ++ ledger.
Proof.
  induction primitive; intros; simpl in H; inversion H; clear H; subst.
  - exists [].  simpl. reflexivity.
  - exists [(transaction next ctr_id0 issuer owner scale c time)].
    trivial.
  - eapply IHprimitive. exact H1.
  - case_eq (query gateway0 a time); intros; rewrite H in H1.
    + eapply IHprimitive. exact H1.
    + inversion H1.
  - eapply IHprimitive in H1; trivial.
  - case_eq (execute primitive1 scale issuer owner balance
           time gateway0 ctr_id0 dsc_id0 next ledger); intros; rewrite H in H1.
    destruct r.
    case_eq ( execute primitive2 scale issuer owner
           res_balance0 time gateway0 ctr_id0 dsc_id0 res_next0
           res_ledger0); intros; rewrite H0 in H1.
    destruct r.
    + inversion H1. subst. clear H1.
      eapply IHprimitive1 in H.
      eapply IHprimitive2 in H0.
      destruct H as (tr1 & H).
      destruct H0 as (tr2 & H0).
      rewrite H in H0.
      exists (tr2 ++ tr1).
      rewrite H0.
      rewrite app_assoc. reflexivity.
    + inversion H1.
    + inversion H1.
  - exists []. simpl. trivial.
  - case_eq (query gateway0 a time); intros; rewrite H in H1.
    case_eq (n =? 0); intros; rewrite H0 in H1.
    eapply IHprimitive2. exact H1.
    eapply IHprimitive1. exact H1.
    inversion H1.
  - case_eq (n0 <? time); intros; rewrite H in H1. inversion H1.
    case_eq (n <? time); intros; rewrite H0 in H1.
    apply IHprimitive in H1. assumption.
    inversion H1. subst.
    exists []. simpl. reflexivity.
Qed.


Fixpoint timebound_in_primitive (primitive : Primitive) :=
  match primitive with
  | Timebound _ _ _ => True
  | Scale _ p => timebound_in_primitive p
  | ScaleObs _ p => timebound_in_primitive p
  | Give p => timebound_in_primitive p
  | And p1 p2 => timebound_in_primitive p1 \/ timebound_in_primitive p2
  | Or p1 p2 => timebound_in_primitive p1 \/ timebound_in_primitive p2
  | If _ p1 p2 => timebound_in_primitive p1 \/ timebound_in_primitive p2
  | _ => False
  end.


Fixpoint or_in_primitive (primitive : Primitive) :=
  match primitive with
  | Or _ _ => True
  | Scale _ p => or_in_primitive p
  | ScaleObs _ p => or_in_primitive p
  | Give p => or_in_primitive p
  | And p1 p2 => or_in_primitive p1 \/ or_in_primitive p2
  | Timebound _ _ p => or_in_primitive p
  | If _ p1 p2 => or_in_primitive p1 \/ or_in_primitive p2
  | _ => False
  end.


Lemma primitive_without_or_timebound_generates_nil:
  forall primitive scale issuer owner balance
         time gateway ctr_id dsc_id next ledger
         balance' ctrs' next' ledger',
    execute primitive scale issuer owner balance
                      time gateway ctr_id dsc_id next ledger
    =
    Some (result balance' ctrs' next' ledger') ->
    ~ timebound_in_primitive primitive ->
    ~ or_in_primitive primitive ->
    ctrs' = [].
Proof.
  induction primitive; intros; simpl in H; inversion H; clear H; subst; try auto.
  - eapply IHprimitive. apply H3.
    unfold not in *. intros. apply H0. simpl. trivial.
    unfold not in *. intros. apply H1. simpl. trivial.
  - case_eq (query gateway0 a time); intros; rewrite H in H3; try inversion H3.
    eapply IHprimitive. exact H3.
    unfold not in *. intros. apply H0. simpl. trivial.
    unfold not in *. intros. apply H1. simpl. trivial.
  - eapply IHprimitive. exact H3.
    unfold not in *. intros. apply H0. simpl. trivial.
    unfold not in *. intros. apply H1. simpl. trivial.
  - case_eq (execute primitive1 scale issuer owner balance time gateway0 ctr_id0 dsc_id0 next ledger); intros; rewrite H in H3; try inversion H3.
    destruct r.
    case_eq (execute primitive2 scale issuer owner res_balance0 time gateway0 ctr_id0
                               dsc_id0 res_next0 res_ledger0); intros; rewrite H2 in H3; try inversion H3.
    destruct r.
    inversion H6.
    rewrite H8.
    eapply IHprimitive1 in H.
    -- subst res_contracts0. simpl in H8.
       eapply IHprimitive2. subst res_contracts1. exact H2.
       clear H2 H6 H4 H3.
       unfold not in *. intros. apply H0. simpl. right. trivial.
       unfold not in *. intros. apply H1. simpl. right. trivial.
    -- unfold not in *. intros. apply H0. simpl. left. trivial.
    -- unfold not in *. intros. apply H1. simpl. left. trivial.
  - contradict H1. simpl. trivial. 
  - case_eq (query gateway0 a time); intros; rewrite H in H3; try inversion H3.
    -- destruct n. simpl in *.
    + eapply IHprimitive2. exact H3.
      unfold not in *. intros. apply H0. right. trivial.
      unfold not in *. intros. apply H1. right. trivial.
    + simpl in H3. 
      eapply IHprimitive1. exact H3.
      unfold not in *. intros. apply H0. left. trivial.
      unfold not in *. intros. apply H1. left. trivial.
  - simpl in H0. contradiction.
Qed.

Lemma primitive_execution_generates_fresh_id:
  forall primitive scale issuer owner balance
         time gateway ctr_id dsc_id next ledger
         balance' ctrs' next' ledger',
    execute primitive scale issuer owner balance
                      time gateway ctr_id dsc_id next ledger
    =
    Some (result balance' ctrs' next' ledger') ->
    next' >= next.
Proof.
  induction primitive; intros *; intros H; intros; simpl in H. inversion H; clear H; subst.
  - omega.
  - inversion H. omega.
  - eapply IHprimitive. exact H.
  - case_eq (query gateway0 a time); intros; rewrite H0 in H.
    eapply IHprimitive. exact H.
    inversion H.
  - eapply IHprimitive. exact H.
  - case_eq (execute primitive1 scale issuer owner balance time
          gateway0 ctr_id0 dsc_id0 next ledger); intros; rewrite H0 in H.
    destruct r.
    case_eq (execute primitive2 scale issuer owner res_balance0
          time gateway0 ctr_id0 dsc_id0 res_next0 res_ledger0); intros; rewrite H1 in H.
    destruct r.
    + inversion H; subst.
      apply IHprimitive2 in H1.
      apply IHprimitive1 in H0.
      omega.
    + inversion H.
    + inversion H.
  - inversion H. omega.
  - case_eq (query gateway0 a time); intros; rewrite H0 in H.
    case_eq (n =? 0); intros; rewrite H1 in H.
    + eapply IHprimitive2. exact H.
    + eapply IHprimitive1. exact H.
    + inversion H.
  - case_eq (n0 <? time); intros; rewrite H0 in H.
    inversion H.
    case_eq (n <? time); intros; rewrite H1 in H.
    eapply IHprimitive. exact H.
    inversion H. subst. omega.
Qed.


Lemma removed_not_in:
  forall ctr ctrs, ~ In ctr (rm ctr ctrs).
Proof.
  induction ctrs; auto.
  unfold not in *; intros.
  apply IHctrs.
  simpl in H.
  case_eq (ctr_eq_dec ctr a); intros; rewrite H0 in H; trivial.
  contradiction.
Qed.  

Lemma removed_or_not:
  forall ctrs c ctr, In c ctrs -> (c = ctr \/ In c (rm ctr ctrs)).
Proof.
  induction ctrs; auto.
  intros.
  assert (H' := removed_not_in); trivial.
  simpl in H.
  destruct H as [H | H].
  - subst a.
    simpl.
    case_eq (ctr_eq_dec ctr c); intros e H.
    -- subst ctr. left. trivial.
    -- contradiction.
  - simpl.
    case_eq (ctr_eq_dec ctr a); intros e He.
    -- apply IHctrs; trivial.
    -- contradiction.
Qed.


Lemma join_same_contract:
  forall ctr owner ctr' s1 s2 ctrs' balance' next' ledger',
    step s1 s2 ->
    In ctr (m_contracts s1) ->
    In ctr' (m_contracts s1) ->
    ~ In (Executed (ctr_id ctr)) (m_events s1) ->
    ~ In (Executed (ctr_id ctr')) (m_events s1) ->
    In (Executed (ctr_id ctr)) (m_events s2) ->
    In (Executed (ctr_id ctr')) (m_events s2) ->
    can_join owner ctr ->
    consistent_ctr_ids s1 ->
    exec_ctr_in_state_with_owner ctr s1 owner =
    Some
      {|
        res_balance := balance';
        res_contracts := ctrs';
        res_next := next';
        res_ledger := ledger' |} ->
    s2 =
    update_state s1 (rm ctr (m_contracts s1) ++ ctrs') balance' next' ledger'
                 (Executed (ctr_id ctr) :: m_events s1) ->
    ctr_owner ctr' <> 0 ->
    ctr = ctr'.
Proof.
  intros.
  eapply execute_det; eauto.
Qed.

Lemma same_owner_joins_same_contract:
  forall ctr owner ctr' s1 s2 ctrs' balance' next' ledger',
    step s1 s2 ->
    In ctr (m_contracts s1) ->
    In ctr' (m_contracts s1) ->
    ~ In (Executed (ctr_id ctr)) (m_events s1) ->
    ~ In (Executed (ctr_id ctr')) (m_events s1) ->
    In (Executed (ctr_id ctr)) (m_events s2) ->
    In (Executed (ctr_id ctr')) (m_events s2) ->
    can_join owner ctr ->
    consistent_ctr_ids s1 ->
    ctr_proposed_owner ctr' = ctr_owner ctr' ->
    exec_ctr_in_state_with_owner ctr s1 owner =
    Some
      {|
        res_balance := balance';
        res_contracts := ctrs';
        res_next := next';
        res_ledger := ledger' |} ->
    s2 =
    update_state s1 (rm ctr (m_contracts s1) ++ ctrs') balance' next' ledger'
                 (Executed (ctr_id ctr) :: m_events s1) ->
    ctr_owner ctr' <> 0 ->
    owner  = ctr_owner ctr'.
Proof.
  intros.
  assert (H': ctr = ctr').
  - eapply join_same_contract; eauto.
  - unfold can_join in H6.
    destruct H6 as [H6 | H6].
    + subst ctr. subst owner. trivial.
    + subst ctr. rewrite H6 in H8. rewrite H8 in H11. contradiction.
Qed.


Lemma consistent_ctr_ids_in_state:
  forall s ctr,
    greater_than_all (ctr_id ctr) (m_contracts s) ->
    ~ In ctr (m_contracts s).
Proof.
  intros s.
  induction (m_contracts s); intros.
  - auto.
  - unfold greater_than_all in H.
    case_eq a; intros.
    + subst a.
      fold greater_than_all in H.
      destruct H as [H H'].
      simpl.
      unfold not.
      intros.
      destruct H0 as [H0 | H0].
      * subst ctr. simpl in H. contradict H. omega.
      * apply IHl in H'. contradiction.
Qed.

    
Lemma rm_other:
  forall l x y, In x (rm y l) -> x <> y.
Proof.
  induction l; intros; simpl in H; auto.
  case_eq (ctr_eq_dec y a); intros; rewrite H0 in H.
  - subst y.
    unfold not. intros. subst a.
    assert (H': ~ In x (rm x l)).
    + apply removed_not_in.
    + apply H'. trivial.
  - contradiction.
Qed.


Lemma primitive_execution_generates_fresh_contracts:
  forall primitive scale issuer owner balance
         time gateway cttr_id dsc_id next ledger
         balance' ctrs' next' ledger',
    execute primitive scale issuer owner balance
                      time gateway cttr_id dsc_id next ledger
    =
    Some (result balance' ctrs' next' ledger') ->
    (forall ctr, In ctr ctrs' -> (ctr_id ctr) > next).
Proof.
  induction primitive; intros; simpl in H; inversion H; clear H; subst; try contradiction.
  - eapply IHprimitive; eauto.
  - case_eq (query gateway0 a time); intros; rewrite H in H2.
    + eapply IHprimitive; eauto.
    + inversion H2.
  - eapply IHprimitive; eauto.
  - case_eq (execute primitive1 scale issuer owner balance
                               time gateway0 cttr_id dsc_id0
                               next ledger); intros; rewrite H in H2.
    + destruct r.
      case_eq (execute primitive2 scale issuer owner res_balance0
                                 time gateway0 cttr_id
                                 dsc_id0 res_next0 res_ledger0);
        intros; rewrite H1 in H2.
      * destruct r. inversion H2. clear H2. subst.
        apply in_app_or in H0.
        destruct H0 as [H0 | H0].
        ** eapply IHprimitive1. exact H. trivial.
        ** eapply IHprimitive2 in H1; eauto.
           apply primitive_execution_generates_fresh_id in H. omega.
      * inversion H2.
    + inversion H2.
  - simpl in H0.
    destruct H0 as [H0 | H0]; try contradiction.
    subst ctr. simpl. omega.
  - case_eq (query gateway0 a time); intros; rewrite H in H2; try inversion H2.
    case_eq n; intros; subst n; simpl in H3.
    + eapply IHprimitive2 in H3. exact H3. trivial.
    + eapply IHprimitive1 in H3. exact H3. trivial.
  - case_eq (n0 <? time); intros; rewrite H in H2; try inversion H2; clear H2.
    case_eq ( n <? time); intros; rewrite H1 in H3; try inversion H3; clear H3.
    + eapply IHprimitive. exact H4. trivial.
    + subst ctrs'. simpl in H0. destruct H0 as [H0 | H0]; try contradiction.
      subst ctr. simpl. omega.
Qed.


Lemma consistent_ids_step :
  forall s s',
    step s s' ->
    consistent_ctr_ids s ->
    consistent_ctr_ids s'.
Proof.
  intros s s' H.
  induction H; unfold consistent_ctr_ids in *; intros.
  - unfold append_new_ctr_to_state in H4.
    rewrite H4 in H6, H7.
    simpl in H6, H7.
    destruct H6 as [H6 | H6]; destruct H7 as [H7 | H7].
    + subst x y. trivial.
    + clear H H0 H2 H4.  subst new_contract x. simpl in H8. exfalso.
      unfold next_id_is_fresh in H3. rewrite H8 in H3.
      apply consistent_ctr_ids_in_state in H3. contradiction.
    + clear H H0 H2 H4.  subst new_contract y. simpl in H8. exfalso.
      unfold next_id_is_fresh in H3. rewrite <- H8 in H3.
      apply consistent_ctr_ids_in_state in H3. contradiction.
    + apply H5; trivial.
  - subst s'. simpl in H8, H9.
    apply in_app_or in H9.
    apply in_app_or in H8.
    destruct H9 as [H9 | H9]; destruct H8 as [H8 | H8]; try case_eq (ctr_eq_dec x y); intros; trivial; try contradiction.
  - subst s'. simpl in H8, H9.
    apply in_app_or in H9.
    apply in_app_or in H8.
    destruct H9 as [H9 | H9]; destruct H8 as [H8 | H8]; try case_eq (ctr_eq_dec x y); intros; trivial; try contradiction.
  - subst s'. simpl in H8, H9.
    apply in_app_or in H9.
    apply in_app_or in H8.
    destruct H9 as [H9 | H9]; destruct H8 as [H8 | H8]; try case_eq (ctr_eq_dec x y); intros; trivial; try contradiction.
  - subst s'. simpl in H6, H7.
    case_eq (ctr_eq_dec x y); intros; subst; trivial; try contradiction.
  - subst s'. simpl in H1, H2. eapply H0; eauto.
Qed.


Lemma consistent_ids_steps :
  forall s s',
    steps s s' ->
    consistent_ctr_ids s ->
    consistent_ctr_ids s'.
Proof.
  intros s s' H.
  induction H; intros.
  - subst. trivial.
  - eapply consistent_ids_step. exact H0. apply IHsteps. trivial.
Qed.


Lemma exec_implies_ctr_exists:
  forall ctr s1 s2,
    step s1 s2 ->
    ~ In (Executed (ctr_id ctr)) (m_events s1) ->
    In (Executed (ctr_id ctr)) (m_events s2) ->
    In ctr (m_contracts s1).
Proof.
  intros ctr s1 s2 H.
  revert ctr.
  induction H; intros.
  - unfold append_new_ctr_to_state in H4.
    subst s2. simpl in *.
    destruct H6 as  [H6 | H6]; try contradiction.
    inversion H6.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0. trivial.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0. trivial.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0. trivial.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    + subst ctr0 s2. simpl in H6.
      destruct H6 as [H6 | H6]; try contradiction.
      inversion H6.
  - subst s2. simpl in *. contradiction.
Qed.


Ltac steps_intro :=
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  intros [H0 [H1 [H2 H3]]].


Ltac step_intro :=
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  intros [H0 [H1 [H2 H3]]].

	
Ltac and_intros :=	
  let Hl := fresh "H" in
	let Hr := fresh "H" in
	intros [Hl Hr]; try and_intros.

Ltac same_ctr c1 c2 s:=
  let H := fresh "H" in
  assert (H : c1 = c2); try eapply execute_det; eauto;
  (subst s; simpl; auto).

Ltac case_analysis H :=
  let H' := fresh "H" in
  match goal with
  | H : match (if ?c then _ else _)  with
        | Some _ => _
        | None => _
        end = _ |- _
    => case_eq c; intros H'; rewrite H' in H; try inversion H; clear H
  end.

Lemma inf_contradiction :
  forall x, ((INF <? x) = true) -> False.
Proof.
  intros.
  unfold Nat.ltb in H.
  rewrite leb_correct_conv in H.
  - inversion H.
  - apply Nat.lt_trans with (m := INF).
    + apply infinite.
    + omega.
Qed.


Ltac same_owner o1 o2 ctr1 ctr2:=
  let H' := fresh "H" in
  assert (H' : o1 = o2);
  try eapply same_owner_joins_same_contract with (ctr := ctr1) (ctr' := ctr2);
  eauto; simpl; auto.

Ltac contradict_hyp H :=
  simpl in H; destruct H as [H | H]; try contradiction; try inversion H.


Ltac case_analysis_2 H :=
  let H' := fresh "H" in 
  match goal with
  | H : match (if ?c then _ else _)  with
        | Some _ => _
        | None => _
        end = _ |- _
    => case_eq c; intros H'; rewrite H' in H; try inversion H; clear H
  end.


Lemma exists_step_in_steps:
  forall s1 s2 ctr,
    In ctr (m_contracts s1) ->
    s1 ⇓ s2 ⊢ (ctr_id ctr) ->
    exists s s',
      (s1 ~~> s) /\ (s → s' ⊢ (ctr_id ctr)) /\ (s' ~~> s2) /\ In ctr (m_contracts s).
Proof.
  intros s1 s2 ctr H'.
  steps_intro.
  induction H; intros.
  - subst s2. contradiction.
  - assert (H'': In (Executed (ctr_id ctr)) (m_events s) \/
                ~ In (Executed (ctr_id ctr)) (m_events s)).
    apply classic.
    destruct H'' as [H'' | H''].
    + eapply IHsteps in H''.
      destruct H'' as [sk [sk' [H1' [H2' [H3' H4']]]]]. 
      exists sk, sk'.
      split; trivial.
      split; trivial.
      split; trivial.
      eapply tran; eauto.
    + exists s, s2.
      split; trivial.
      split.
      * repeat split; trivial.
        eapply consistent_ids_steps; eauto.
      * split.
        ** apply refl. trivial.
        ** eapply exec_implies_ctr_exists; eauto.
Qed.


Lemma gateway_is_consistent:
  forall gtw addr t1 t2 v1 v2,
    query gtw addr t1 = Some v1 ->
    query gtw addr t2 = Some v2 ->
    v1 = v2.
Proof.
  induction gtw; intros; simpl in *. 
  - inversion H.
  - destruct a.
    case_eq (addr =? gtw_addr0); intros H'; rewrite H' in *.
    case_eq (t1 <=? gtw_timestamp0 + FRESHNESS); intro H1'.
    + rewrite H1' in H.
      case_eq (t2 <=? gtw_timestamp0 + FRESHNESS); intros H2';rewrite H2' in H0.
      * inversion H. inversion H0. subst. trivial.
      * inversion H0.
    + rewrite H1' in H. inversion H.
    + eapply IHgtw; eauto.
Qed.


Definition gateway_stays_fresh (s1 s2 : State) :=
  steps s1 s2 ->
  (m_global_time s2) - (m_global_time s1) <= FRESHNESS.


Lemma helper:
  forall a b c,
    a - b <= c ->
    S (b + c) < a ->
    False.
Proof.
  induction a.
  - intros. inversion H0.
  - induction b; intros.
    + simpl in *.
      case_eq c; intros; subst.
      inversion H.
      apply Nat.lt_le_trans with (n := S (S n)) (m := S a) (p := S n) in H0; auto.
      apply lt_S_n in H0.
      omega.
    + simpl in H, H0.
      eapply IHa. exact H.
      apply lt_S_n in H0.
      trivial.
Qed.
    

Lemma query_consistent:
  forall g addr t t' v,
    query g addr t = Some v ->
    t' - t <= FRESHNESS ->
    query (gateway_time_update g (S t)) addr t' = Some v.
Proof.
  induction g; intros; simpl.
  - inversion H.
  - destruct a. simpl in *.
    case_eq (addr =? gtw_addr0); intros.
    + rewrite H1 in H.
      case_eq (t <=? gtw_timestamp0 + FRESHNESS); intros.
      * rewrite H2 in H.
        inversion H.
        subst.
        case_eq (t' <=? S (t + FRESHNESS)); intros; trivial.
        apply leb_complete_conv in H3.
        eapply helper in H3; auto. exfalso. trivial.
      * rewrite H2 in H. inversion H.
    + rewrite H1 in H.
      apply IHg; trivial.
Qed.



Lemma gateway_is_consistent_on_step:
  forall s1 s2 addr v,
    step s1 s2 ->
    gateway_stays_fresh s1 s2 ->
    query (m_gateway s1) addr (m_global_time s1) = Some v ->
    query (m_gateway s2) addr (m_global_time s2) = Some v.
Proof.
  intros.
  induction H; try subst s2; trivial.
  simpl.
  apply query_consistent; trivial.
  simpl.
  unfold FRESHNESS.
  case_eq (m_global_time s1); intros; omega.
Qed.


Lemma time_passing_step :
  forall s s', step s s' -> (m_global_time s) <= (m_global_time s').
Proof.
  intros. induction H; subst s'; try simpl; trivial; try omega.
Qed.

Lemma time_passing_steps :
  forall s s', steps s s' -> (m_global_time s) <= (m_global_time s').
Proof.
  intros.
  induction H.
  - subst s. trivial.
  - apply time_passing_step in H0.
    eapply Nat.le_trans; eauto.
Qed.

Lemma helper_sub :
  forall a b c F, a <= b <= c -> c - a <= F ->  b - a <= F.
Proof.
  induction a; intros b c f [H' H''] H0; try omega.
Qed.


Lemma helper_sub':
  forall a b c f, a <= b <= c -> c - a <= f -> c - b <= f.
Proof.
  induction a; intros b c f [H' H''] H0; try omega.
Qed.


Lemma gateway_stays_fresh_left:
  forall s1 s2 s,
    steps s1 s ->
    step s s2 ->
    gateway_stays_fresh s1 s2 ->
    gateway_stays_fresh s1 s.
Proof.
  intros.
  unfold gateway_stays_fresh in *.
  intros.
  assert (H' : s1 ~~> s2).
  eapply tran; eauto.
  apply H1 in H'.
  apply time_passing_step in H0.
  apply time_passing_steps in H2.
  eapply helper_sub; eauto.
Qed.

Lemma tran_helper :
  forall s2 s s1,
    steps s s2 -> step s1 s -> steps s1 s2.
Proof.
  intros s2 s s1 H.
  revert s1.
  induction H.
  - subst. intros. eapply tran. eapply refl. trivial. trivial.
  - intros. eapply IHsteps in H1.
    eapply tran. exact H1. trivial.
Qed.

Lemma tran_clos :
  forall s2 s s1,
    steps s s2 -> steps s1 s -> steps s1 s2.
Proof.
  intros s2 s s1 H.
  revert s1.
  induction H; intros.
  - subst. assumption.
  - eapply IHsteps in H1.
    eapply tran. exact H1. trivial.
Qed.

Lemma gateway_stays_fresh_left':
  forall s1 s2 s,
    step s1 s ->
    steps s s2 ->
    gateway_stays_fresh s1 s2 ->
    gateway_stays_fresh s s2.
Proof.
  intros.
  unfold gateway_stays_fresh in *.
  intros.
  assert (H' : s1 ~~> s2).
  eapply tran_helper; eauto.
  apply H1 in H'.
  apply time_passing_step in H.
  apply time_passing_steps in H2.
  eapply helper_sub'; eauto.
Qed.

Lemma gateway_stays_fresh_right:
  forall s1 s2 s,
    steps s1 s ->
    step s s2 ->
    gateway_stays_fresh s1 s2 ->
    gateway_stays_fresh s s2.
Proof.
  intros.
  unfold gateway_stays_fresh in *.
  intros.
  assert (H' : s1 ~~> s2).
  eapply tran; eauto.
  apply H1 in H'.
  apply time_passing_step in H0.
  apply time_passing_steps in H.
  eapply helper_sub'; eauto.
Qed.


Lemma gateway_stays_fresh_steps_right:
  forall s1 s2 s,
    steps s1 s ->
    steps s s2 ->
    gateway_stays_fresh s1 s2 ->
    gateway_stays_fresh s s2.
Proof.
  intros s1 s2 s H.
  revert s2.
  induction H; intros.
  - subst; assumption.
  - assert (H' : steps s s0).
    + eapply tran_helper. exact H1. assumption.
    + apply IHsteps in H'; trivial.
      eapply gateway_stays_fresh_left'; eauto.
Qed.


Lemma gateway_stays_fresh_steps_left:
  forall s1 s2 s,
    steps s s2 ->
    steps s1 s ->
    gateway_stays_fresh s1 s2 ->
    gateway_stays_fresh s1 s.
Proof.
  intros s1 s2 s H.
  revert s1.
  induction H; intros.
  - subst; assumption.
  - apply IHsteps in H1; trivial.
    eapply gateway_stays_fresh_left; eauto.
    eapply tran_clos; eauto.
Qed.

  
Lemma gateway_is_consistent_on_steps:
  forall s1 s2 addr v,
    steps s1 s2 ->
    gateway_stays_fresh s1 s2 -> 
    query (m_gateway s1) addr (m_global_time s1)  = Some v ->
    query (m_gateway s2) addr (m_global_time s2)  = Some v.
Proof.
  intros.
  induction H.
  - subst. trivial.
  - eapply gateway_is_consistent_on_step in H2.
    exact H2.
    eapply gateway_stays_fresh_right; eauto.
    apply IHsteps.
    eapply gateway_stays_fresh_left; eauto.
Qed.

Import ListNotations.
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
