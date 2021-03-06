Load findel.

(* Handy tactics *)
Ltac simp_inv_clear H :=
  simpl H; inversion H; clear H.

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


Ltac resolve_owner H :=
  unfold can_join in H; simpl in H;
  destruct H as [H | H]; subst;
  trivial; try contradiction.


Ltac ctr_case_analysis ctr ctr' :=
  case_eq (ctr_eq_dec ctr ctr'); intros; try contradiction; subst ctr'.

Ltac destruct_executed H :=
  let S := fresh "St" in
  let M := fresh "M" in
  let Ev := fresh "Ev" in
  let T := fresh "T" in
  destruct H as [S [M [Ev T]]].

Ltac destruct_deleted := destruct_executed.

Ltac destruct_join H :=
  let s := fresh "s" in
  let s' := fresh "s'" in
  let Ss1 := fresh "Ss" in
  let Ss2 := fresh "Ss" in
  let E := fresh "E" in
  let D := fresh "D" in
  destruct H as [s [s' [Ss1 [Ss2 [E | D]]]]]; try destruct_executed E; try destruct_deleted D.



Ltac destruct_generates H :=
  let res := fresh "res" in
  let Ex := fresh "Exec" in
  let M := fresh "M" in
  destruct H as [res [Ex M]].


Ltac destruct_join_gen H :=
  let s := fresh "s" in
  let s' := fresh "s'" in
  let ctr := fresh "ctr" in
  let genctr := fresh "g_ctr" in
  let Ss1 := fresh "Ss" in
  let Ss2 := fresh "Ss" in
  let St := fresh "St" in
  let E := fresh "E" in
  let D := fresh "D" in
  let G := fresh "G" in
  let N := fresh "J" in
  destruct H as [s [s' [Ss1 [Ss2 [[E | D] [G J]]]]]];
  try destruct_executed E; try destruct_generates G.

Ltac inversion_event Ev :=
  destruct Ev as [Ev | Ev]; try inversion Ev; try contradiction.

Ltac not_or c c' H :=
  ctr_case_analysis c c'; subst c; simpl in H; inversion H.

Ltac inconsistent H I := apply H in I; auto; subst; try contradiction.

Ltac not_executed Cons In :=
  destruct Cons as [_ [_ [_ [Cons _]]]];
  apply Cons in In; destruct In as [In _];
  contradiction.

Ltac execute_own ctr H :=
  subst ctr; unfold exec_ctr_in_state_with_owner in H; simpl in H.

(* Misc *)
Definition executed
           (ctr : FinContract)
           (s s' : State)
           (at_ : Time) :=
    step s s' /\
    In ctr (m_contracts s) /\
    In (Executed (ctr_id ctr)) (m_events s') /\
    at_ = m_global_time s.

Definition deleted
           (ctr : FinContract)
           (s s' : State)
           (at_ : Time) :=
    step s s' /\
    In ctr (m_contracts s) /\
    In (Deleted (ctr_id ctr)) (m_events s') /\
    at_ = m_global_time s.

Definition joins
           (O : Address)
           (ctr : FinContract)
           (s1 s2 : State)
           (at_ : Time) :=
  exists s s', steps s1 s /\ steps s' s2 /\ (executed ctr s s' at_ \/ deleted ctr s s' at_).

Definition joins_in_s
           (O : Address)
           (ctr : FinContract)
           (s1 s2 s : State)
           (at_ : Time) :=
  exists s', steps s1 s /\ steps s' s2 /\ (executed ctr s s' at_ \/ deleted ctr s s' at_).

Ltac destruct_joins_in H :=
  let s := fresh "s" in
  let Ss1 := fresh "Ss" in
  let Ss2 := fresh "Ss" in
  let E := fresh "E" in
  let D := fresh "D" in
  destruct H as [s [Ss1 [Ss2 [E | D]]]]; try destruct_executed E; try destruct_deleted D.


Definition joins_at_s'
           (O : Address)
           (ctr : FinContract)
           (s1 s2 s' : State)
           (at_ : Time) :=
  exists s, steps s1 s /\ steps s' s2 /\ (executed ctr s s' at_ \/ deleted ctr s s' at_).


Definition generates
           (ctr new_ctr : FinContract) (s : State) (I O : Address) :=
  exists result,
    execute (ctr_primitive ctr) (ctr_scale ctr) I O
            (m_balance s) (m_global_time s) (m_gateway s) (ctr_id ctr)
            (ctr_desc_id ctr) (m_fresh_id s) (m_ledger s) = Some result /\
    In new_ctr (res_contracts result).

(* O joins both the ctr and the generated ctr *)
Definition joins_generated
           (O : Address)
           (ctr gen_ctr : FinContract)
           (s1 s2 : State)
           (t_first t_second : Time) :=
  exists s s', steps s1 s /\ steps s' s2 /\
               (executed ctr s s' t_first \/ deleted ctr s s' t_first) /\
               generates ctr gen_ctr s (ctr_issuer ctr) O /\ joins O gen_ctr s' s2 t_second.

(* O joins both the ctr, and I joins the generated ctr *)
Definition joins_generated'
           (O I : Address)
           (ctr gen_ctr : FinContract)
           (s1 s2 : State)
           (t_first t_second : Time) :=
  exists s s', steps s1 s /\ steps s' s2 /\
               (executed ctr s s' t_first \/ deleted ctr s s' t_first) /\
               generates ctr gen_ctr s (ctr_issuer ctr) O /\ joins I gen_ctr s' s2 t_second.


Definition consistent_state (s : State) :=
  (forall ctr, In ctr (m_contracts s) -> m_fresh_id s > ctr_id ctr) /\
  (forall c_id, (In (Executed c_id) (m_events s) \/ In (Deleted c_id) (m_events s)) -> m_fresh_id s > c_id) /\
  (forall ctr ctr', In ctr (m_contracts s) -> In ctr' (m_contracts s) -> (ctr_id ctr = ctr_id ctr') -> ctr = ctr') /\
  (forall ctr, In ctr (m_contracts s) -> (~ In (Executed (ctr_id ctr)) (m_events s) /\ ~ In (Deleted (ctr_id ctr)) (m_events s))) /\
  (forall e, ~ (In (Executed e) (m_events s) /\ In (Deleted e) (m_events s))).


Lemma consistent_impl_exec:
  forall s ctr,
    consistent_state s ->
    In ctr (m_contracts s) ->
    ~ In (Executed (ctr_id ctr)) (m_events s).
Proof.
  intros.
  destruct H as [_ [_ [_ [H _]]]].
  apply H in H0.
  destruct H0 as [H0 _].
  trivial.
Qed.

Lemma consistent_impl_del:
  forall s ctr,
    consistent_state s ->
    In ctr (m_contracts s) ->
    ~ In (Deleted (ctr_id ctr)) (m_events s).
Proof.
  intros.
  destruct H as [_ [_ [_ [H _]]]].
  apply H in H0.
  destruct H0 as [_ H0].
  trivial.
Qed.

Ltac find_contradiction H :=
  match goal with
  | H : In ?ctr _ |- _ =>  apply consistent_impl_exec in H; auto; subst; simpl in *; try contradiction
  end.

Ltac find_contradiction_del H :=
  match goal with
  | H : In ?ctr _ |- _ =>  apply consistent_impl_del in H; auto; subst; simpl in *; try contradiction
  end.


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

Lemma leb_sound_true:
  forall n m,
    n <=? m = true -> n <= m.
Proof.
  induction n.
  - induction m; intros; try omega.
  - intros m.
    case_eq m; intros; subst m; simpl in H0.
    + inversion H0.
    + apply IHn in H0. omega.
Qed.


Lemma leb_sound_false:
  forall n m,
    n <=? m = false -> ~ n <= m.
Proof.
  induction n.
  - induction m; intros; simpl in H; inversion H.
  - intros m.
    case_eq m; intros; subst m; simpl in H0.
    + omega.
    + apply IHn in H0. omega.
Qed.

Lemma ltb_sound_true:
  forall n m,
    n <? m = true -> n < m.
Proof.
  unfold Nat.ltb.
  intros.
  simpl in H.
  case_eq m; intros; subst m.
  - inversion H.
  - apply leb_sound_true in H. omega.
Qed.


Lemma ltb_sound_false:
  forall n m,
    n <? m = false -> ~ n < m.
Proof.
  unfold Nat.ltb.
  intros.
  simpl in H.
  case_eq m; intros; subst m.
  - omega.
  - apply leb_sound_false in H. omega.
Qed.

Lemma propleb_sound_false:
  forall n m,
    ~ n <= m -> n <=? m = false.
Proof.
  induction n.
  - intros. contradict H. omega.
  - induction m; intros.
    + simpl. trivial.
    + simpl. apply IHn.
      unfold not. intros.
      apply H.
      omega.
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
  - destruct t.
    + case_if H1.
      case_if H2.
      * eapply IHP; eauto.
      * exists []. simpl; auto.
    + case_if H1.
      * eapply IHP; eauto.
      * exists []. simpl; auto.
    + case_if H1.
      eapply IHP; eauto.
Qed.

(* execute does not remove transactions from the ledger *)
Theorem execute_does_not_remove_transactions:
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
Theorem step_does_not_remove_transactions:
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
Theorem steps_does_not_remove_transactions:
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

Lemma rm_in:
  forall cs c, In c (rm c cs) -> False.
Proof.
  induction cs; intros; simpl in *; try contradiction.
  case_eq (ctr_eq_dec c a); intros H0 H'; rewrite H' in H; try contradiction.
  - apply IHcs in H. trivial.
  - simpl in H. destruct H as [H | H]; subst; try contradiction.
    eapply IHcs; eauto.
Qed.


Lemma execute_produces_new_id:
  forall P sc I O bal time gtw c_id dsc_id bal' ctrs' next_id' L' next_id L,
    execute P sc I O bal  time gtw c_id dsc_id next_id L = Some (result bal' ctrs' next_id' L') ->
    next_id' >= next_id.
Proof.
  intros P. induction P; intros; simpl in H; inversion H; clear H.
  - omega.
  - omega.
  - eapply IHP; eauto.
  - case_match H1.
    eapply IHP; eauto.
  - eapply IHP; eauto.
  - case_match H1. destruct r.
    case_match H2. destruct r.
    inversion H3. clear H3.
    subst ctrs'.
    apply IHP1 in H.
    apply IHP2 in H0.
    subst. omega.
  - subst. omega.
  - case_match H1.
    case_eq (n =? 0); intros H0; rewrite H0 in H2.
    + eapply IHP2; eauto.
    + eapply IHP1; eauto.
  - destruct t.
      case_if H1.
      case_if H2; try omega; try eapply IHP; eauto.
    + case_if H1; try omega.
      eapply IHP; eauto.
    + case_if H1.
      eapply IHP; eauto.
Qed.

Lemma execute_produces_new_ids:
  forall P sc I O bal time gtw c_id dsc_id bal' ctrs' next_id' L' next_id L,
    execute P sc I O bal  time gtw c_id dsc_id next_id L = Some (result bal' ctrs' next_id' L') ->
    (forall c, In c ctrs' -> next_id' > ctr_id c).
Proof.
  intros P. induction P; intros; simpl in H; inversion H; clear H.
  - subst ctrs'. try contradiction.
  - subst ctrs'. try contradiction.
  - eapply IHP in H2; eauto.
  - case_match H2.
    eapply IHP in H3; eauto.
  - eapply IHP in H2; eauto.
  - case_match H2. destruct r.
    case_match H3. destruct r.
    inversion H4. clear H4. subst.
    rewrite in_app_iff in H0. destruct H0 as [H0 | H0].
    + (* assert (H' : forall c', In c' res_contracts0 -> res_next0 > ctr_id c'). *)
      apply IHP1 with (c := c) in H; auto.
      apply execute_produces_new_id in H1. omega.
    + apply IHP2 with (c := c) in H1; auto. 
  - subst. simpl in H0. destruct H0 as [H0 | H0].
    + subst c. simpl. omega.
    + contradiction.
  - case_match H2.
    case_eq (n =? 0); intros H'; rewrite H' in H3.
    + eapply IHP2 in H3; eauto.
    + eapply IHP1 in H3; eauto.
  - destruct t.
    + case_if H1.
      case_if H2.
      try eapply IHP; eauto.
      subst ctrs'. simpl in H0. destruct H0 as [H0 | H0]; try contradiction.
      subst c. simpl. omega.
    + case_if H2. 
      try eapply IHP; eauto.
      subst ctrs'. simpl in H0. destruct H0 as [H0 | H0]; try contradiction.
      subst c. simpl. omega.
    + case_if H2.
      try eapply IHP; eauto.
Qed.    

Lemma new_contracts_have_fresh_ids:
  forall P sc I O bal time gtw c_id dsc_id bal' ctrs' next_id' L' next_id L,
    execute P sc I O bal  time gtw c_id dsc_id next_id L = Some (result bal' ctrs' next_id' L') ->
    (forall c, In c ctrs' -> ctr_id c > next_id).
Proof.
  induction P; intros; simpl in H; inversion H; clear H; try subst ctrs'; try contradiction.
  - eapply IHP; eauto.
  - case_match H2. eapply IHP; eauto.
  - eapply IHP; eauto.
  - case_match H2. destruct r.
    case_match H3. destruct r.
    inversion H4; subst; clear H4.
    rewrite in_app_iff in H0.
    destruct H0 as [H0 | H0].
    + eapply IHP1 in H; eauto.
    + eapply IHP2 in H1; eauto.
      eapply execute_produces_new_id in H. omega.
  - destruct H0 as [H0 | H0].
    + subst. simpl. omega.
    + contradiction.
  - case_match H2.
    case_if H3.
    + eapply IHP2; eauto.
    + eapply IHP1; eauto.
  - destruct t.
    + case_if H2. case_if H3.
      * eapply IHP; eauto.
      * subst ctrs'. destruct H0 as [H0 | H0]; subst; simpl; try omega.
        contradiction.
    + case_if H2. eapply IHP; eauto.
      subst ctrs'. destruct H0 as [H0 | H0]; subst; simpl; try omega.
      contradiction.
    + case_if H2. eapply IHP; eauto.
Qed.


Lemma new_contracts_ids_are_consistent:
  forall P sc I O bal time gtw c_id dsc_id bal' ctrs' next_id' L' next_id L,
    execute P sc I O bal  time gtw c_id dsc_id next_id L = Some (result bal' ctrs' next_id' L') ->
    (forall c c', In c ctrs' -> In c' ctrs' -> ctr_id c = ctr_id c' -> c = c').
Proof.
  induction P; intros; simpl in H; inversion H; clear H; subst; try contradiction.
  - eapply IHP; eauto.
  - case_match H4. eapply IHP; eauto.
  - eapply IHP; eauto.
  - case_match H4. destruct r.
    case_match H6. destruct r.
    inversion H6. clear H6. subst.
    rewrite in_app_iff in H0, H1.
    destruct H1 as [H1 | H1]; destruct H0 as [H0 | H0].
    + eapply IHP1; eauto.
    + eapply execute_produces_new_ids in H; eauto.
      eapply new_contracts_have_fresh_ids in H3; eauto. omega.
    + eapply execute_produces_new_ids in H; eauto.
      eapply new_contracts_have_fresh_ids in H3; eauto. omega.
    + eapply IHP2; eauto.
  - destruct H1 as [H1 | H1]; destruct H0 as [H0 | H0]; try contradiction.
    subst. auto.
  - case_match H4. case_if H5.
    + eapply IHP2; eauto.
    + eapply IHP1; eauto.
  - destruct t. case_if H4.
    + case_if H5.
      * eapply IHP; eauto.
      * subst ctrs'; destruct H1 as [H1 | H1]; destruct H0 as [H0 | H0]; try contradiction.
        subst. reflexivity.
    + case_if H4.
      * eapply IHP; eauto.
      * subst ctrs'; destruct H1 as [H1 | H1]; destruct H0 as [H0 | H0]; try contradiction.
        subst. reflexivity.
    + case_if H4. eapply IHP; eauto.
Qed.


Lemma incl_rm : forall S x y, x <> y -> In x (rm y S) -> In x S.
Proof.
  induction S.
  - simpl. intros. trivial.
  - intros.
    simpl in H0.
    case_eq (ctr_eq_dec y a); intros He H'; rewrite H' in H0. subst.
    + simpl. right. eapply IHS; eauto.
    + simpl in H0. destruct H0 as [H0 | H0]; subst.
      * simpl. left. reflexivity.
      * simpl. right. eapply IHS; eauto.
Qed.

Lemma step_preserves_consistent_state_1:
  forall s s',
    step s s' ->
    consistent_state s ->
    (forall ctr : FinContract,
        In ctr (m_contracts s') -> m_fresh_id s' > ctr_id ctr).
Proof.
  intros.
  destruct H0 as [H0 [He [H' [T P]]]].
  induction H; subst s'; simpl in *; auto.
  - destruct H1 as [H1 | H1].
    + subst. simpl in *. omega.
    + apply H0 in H1. omega.
  - simpl in H1. rewrite in_app_iff in H1. destruct H1 as [H1 | H1].
    + case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
      * subst ctr0. exfalso. eapply rm_in. exact H1.
      * apply incl_rm in H1; eauto. apply H0 in H1.
        apply execute_produces_new_id in H7.
        omega.
    + eapply execute_produces_new_ids in H7; eauto.
  - simpl in H1. rewrite in_app_iff in H1. destruct H1 as [H1 | H1].
    + case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
      * subst ctr0. exfalso. eapply rm_in. exact H1.
      * apply incl_rm in H1; eauto. apply H0 in H1.
        apply execute_produces_new_id in H7.
        omega.
    + eapply execute_produces_new_ids in H7; eauto.
  - simpl in H1. rewrite in_app_iff in H1. destruct H1 as [H1 | H1].
    + case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
      * subst ctr0. exfalso. eapply rm_in. exact H1.
      * apply incl_rm in H1; eauto. apply H0 in H1.
        apply execute_produces_new_id in H7.
        omega.
    + eapply execute_produces_new_ids in H7; eauto.
  - apply H0.
    case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
      * subst ctr0. exfalso. eapply rm_in. exact H1.
      * apply incl_rm in H1; auto.
Qed.


Lemma step_preserves_consistent_state_2:
  forall s s',
    step s s' ->
    consistent_state s ->
    (forall c_id : Id,
        In (Executed c_id) (m_events s') \/ In (Deleted c_id) (m_events s') ->
        m_fresh_id s' > c_id).
  intros.
  destruct H0 as [H0 [He [H' [T P]]]].
  induction H; subst s'; simpl in *; auto.
  - destruct H1 as [[H1 | H1] | [H1 | H1]]; try inversion H1; assert (H'' : m_fresh_id s > c_id); auto.
  - destruct H1 as [[H1 | H1] | [H1 | H1]]; try inversion H1; subst.
    + apply execute_produces_new_id in H7; apply H0 in H. omega.
    + apply execute_produces_new_id in H7.
      assert (H'' : m_fresh_id s > c_id); auto.
      omega.
    + apply execute_produces_new_id in H7.
      assert (H'' : m_fresh_id s > c_id); auto.
      omega.
  - destruct H1 as [[H1 | H1] | [H1 | H1]]; try inversion H1; subst.
    + apply execute_produces_new_id in H7; apply H0 in H. omega.
    + apply execute_produces_new_id in H7.
      assert (H'' : m_fresh_id s > c_id); auto.
      omega.
    + apply execute_produces_new_id in H7.
      assert (H'' : m_fresh_id s > c_id); auto.
      omega.
  - destruct H1 as [[H1 | H1] | [H1 | H1]]; try inversion H1; subst.
    + apply execute_produces_new_id in H7; apply H0 in H. omega.
    + apply execute_produces_new_id in H7.
      assert (H'' : m_fresh_id s > c_id); auto.
      omega.
    + apply execute_produces_new_id in H7.
      assert (H'' : m_fresh_id s > c_id); auto.
      omega.
  - apply H0 in H. 
    destruct H1 as [[H1 | H1] | [H1 | H1]]; try inversion H1; subst; auto.
Qed.


Ltac case_eq_dec_ctr c1 c2 c :=
  case_eq (ctr_eq_dec c1 c); intros; try contradiction;
  case_eq (ctr_eq_dec c2 c); intros; try contradiction;
  subst c1 c2; trivial.

Lemma step_preserves_consistent_state_3:
  forall s s',
    step s s' ->
    consistent_state s ->
    forall ctr ctr' : FinContract,
       In ctr (m_contracts s') ->
       In ctr' (m_contracts s') ->
       ctr_id ctr = ctr_id ctr' -> ctr = ctr'.
Proof.
  intros.
  destruct H0 as [H0 [He [H' [T P]]]].
  induction H; subst s'; simpl in *.
  - destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2]; try subst; trivial.
    + simpl in *. apply H0 in H2. omega.
    + simpl in *. apply H0 in H1. omega.
    + apply H'; auto.
  - rewrite in_app_iff in H1, H2.
    destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
    + case_eq (ctr_eq_dec ctr ctr0); intros Hi.
      * subst. apply rm_in in H1. contradiction.
      * case_eq (ctr_eq_dec ctr' ctr0); intros Hi'.
        ** subst. apply rm_in in H2. contradiction.
        ** intros _ _. apply incl_rm in H1; trivial. apply incl_rm in H2; trivial. apply H'; auto.
    + case_eq (ctr_eq_dec ctr ctr0); intros Hi.
      * subst. apply rm_in in H1. contradiction.
      * apply incl_rm in H1; auto. assert (H9' := H9); auto. eapply new_contracts_have_fresh_ids in H9'; eauto. apply H0 in H1. omega.
    + case_eq (ctr_eq_dec ctr' ctr0); intros Hi.
      * subst. apply rm_in in H2. contradiction.
      * apply incl_rm in H2; auto. assert (H9' := H9); auto. eapply new_contracts_have_fresh_ids in H9'; eauto. apply H0 in H2. omega.
    + eapply new_contracts_ids_are_consistent; eauto.
  - rewrite in_app_iff in H1, H2.
    destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
    + case_eq (ctr_eq_dec ctr ctr0); intros Hi.
      * subst. apply rm_in in H1. contradiction.
      * case_eq (ctr_eq_dec ctr' ctr0); intros Hi'.
        ** subst. apply rm_in in H2. contradiction.
        ** intros _ _. apply incl_rm in H1; trivial. apply incl_rm in H2; trivial. apply H'; auto.
    + case_eq (ctr_eq_dec ctr ctr0); intros Hi.
      * subst. apply rm_in in H1. contradiction.
      * apply incl_rm in H1; auto. assert (H9' := H9); auto. eapply new_contracts_have_fresh_ids in H9'; eauto. apply H0 in H1. omega.
    + case_eq (ctr_eq_dec ctr' ctr0); intros Hi.
      * subst. apply rm_in in H2. contradiction.
      * apply incl_rm in H2; auto. assert (H9' := H9); auto. eapply new_contracts_have_fresh_ids in H9'; eauto. apply H0 in H2. omega.
    + eapply new_contracts_ids_are_consistent; eauto.
  - rewrite in_app_iff in H1, H2.
    destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
    + case_eq (ctr_eq_dec ctr ctr0); intros Hi.
      * subst. apply rm_in in H1. contradiction.
      * case_eq (ctr_eq_dec ctr' ctr0); intros Hi'.
        ** subst. apply rm_in in H2. contradiction.
        ** intros _ _. apply incl_rm in H1; trivial. apply incl_rm in H2; trivial. apply H'; auto.
    + case_eq (ctr_eq_dec ctr ctr0); intros Hi.
      * subst. apply rm_in in H1. contradiction.
      * apply incl_rm in H1; auto. assert (H9' := H9); auto. eapply new_contracts_have_fresh_ids in H9'; eauto. apply H0 in H1. omega.
    + case_eq (ctr_eq_dec ctr' ctr0); intros Hi.
      * subst. apply rm_in in H2. contradiction.
      * apply incl_rm in H2; auto. assert (H9' := H9); auto. eapply new_contracts_have_fresh_ids in H9'; eauto. apply H0 in H2. omega.
    + eapply new_contracts_ids_are_consistent; eauto.
  - case_eq (ctr_eq_dec ctr ctr0); intros Hi.
    + subst. apply rm_in in H1. contradiction.
    + eapply incl_rm in H1; eauto.
      case_eq (ctr_eq_dec ctr' ctr0); intro Hi'.
      * subst. apply rm_in in H2. contradiction.
      * apply incl_rm in H2; eauto.
  - eapply H' in H1; eauto.
Qed.


Ltac contradict_unfold :=
  let He := fresh "H" in
  unfold not; split; intros He; destruct He as [He | He]; try inversion He.


Lemma execute_produces_new_contracts:
  forall P sc I O bal time gtw c_id
         dsc_id bal' ctrs' next_id' L' next_id L,
    execute P sc I O bal  time gtw c_id dsc_id next_id L =
    Some (result bal' ctrs' next_id' L') ->
    next_id > c_id ->
    forall ctr', In ctr' ctrs' -> (ctr_id ctr') <> c_id.
Proof.
  intros P.
  induction P; intros* H; intros; simpl in H; inversion H; clear H.
  - subst. contradiction.
  - subst. contradiction.
  - eapply IHP; eauto.
  - case_match H2.
    eapply IHP; eauto.
  - eapply IHP; eauto.
  - case_match H2.
    destruct r.
    case_match H3.
    destruct r.
    inversion H5. clear H5. subst ctrs'.
    simpl in H1.
    apply in_app_iff in H1.
    destruct H1 as [H1 | H1].
    + eapply IHP1; eauto.
    + eapply IHP2; eauto.
      apply execute_produces_new_id in H.
      apply execute_produces_new_id in H2.
      subst. omega.
  - subst ctrs'. simpl in *.
    destruct H1 as [H1 | H1]; auto.
    subst. simpl. omega.
  - case_match H3.
    case_if H4.
    + eapply IHP2; eauto.
    + eapply IHP1; eauto.
  - destruct t.
    + case_if H3.
      case_if H4.
      * eapply IHP; eauto.
      * subst ctrs'. simpl in H1. destruct H1 as [H1 | H1]; try contradiction.
        subst. simpl. omega.
    + case_if H3.
      * eapply IHP; eauto.
      * subst ctrs'. simpl in H1. destruct H1 as [H1 | H1]; try contradiction.
        subst. simpl. omega.
    + case_if H3. 
      * eapply IHP; eauto.
Qed.


Lemma step_preserves_consistent_state_4:
  forall s s',
    step s s' ->
    consistent_state s ->
    (forall ctr,
        In ctr (m_contracts s') ->
        (~ In (Executed (ctr_id ctr)) (m_events s') /\
         ~ In (Deleted (ctr_id ctr)) (m_events s'))).
Proof.
  intros.
  destruct H0 as [H' [He [H0 [T P]]]].
  induction H; subst s'; simpl in *.
  - contradict_unfold.
    destruct H1 as [H1 | H1].
    + subst ctr new_contract. simpl in *.
      assert (Hf: m_fresh_id s > m_fresh_id s).
      apply He; left. trivial.
      omega.
    + apply T in H1. destruct H1 as [H1 _]. contradiction.
    + destruct H1 as [H1 | H1].
      ++ subst ctr new_contract. simpl in *.
         assert (Hf: m_fresh_id s > m_fresh_id s).
         apply He; right. trivial.
         omega.
      ++ apply T in H1. destruct H1 as [_ H1]. contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0.
    unfold not; split; intros.
    + destruct H9 as [H9 | H9]; try contradiction.
      apply in_app_iff in H1.
      destruct H1 as [H1 | H1].
      ++ eapply rm_in. exact H1.
      ++ unfold exec_ctr_in_state_with_owner in H7.
         apply execute_produces_new_contracts with (ctr' := ctr) in H7; try contradiction.
         apply H'; auto.
         trivial.
    + destruct H9 as [H9 | H9]; try inversion H9.
      apply T in H.
      destruct H as [_ H]; try contradiction.
    + rewrite in_app_iff in H1. destruct H1 as [H1 | H1].
      * eapply incl_rm in H1; eauto.
        split; unfold not; intro C; destruct C as [C | C].
        ** inversion C. apply H0 in H10; auto.
        ** apply T in H1. destruct H1 as [H1 H1']. contradiction.
        ** inversion C.
        ** apply T in H1. destruct H1 as [H1 H1']. contradiction.
      * split.
        ** unfold not. intros [E1 | E2].
           *** inversion E1.
               assert (H7' := H7); auto.
               eapply new_contracts_have_fresh_ids in H7'; eauto.
               unfold  next_id_is_fresh in H3.
               apply H' in H. omega.
           *** eapply new_contracts_have_fresh_ids in H7; eauto.
               assert (C : m_fresh_id s > ctr_id ctr).
               apply He. left. trivial.
               omega.
        ** unfold not. intros [E1 | E2].
           *** inversion E1.
           *** eapply new_contracts_have_fresh_ids in H7; eauto.
               assert (C : m_fresh_id s > ctr_id ctr).
               apply He. right. trivial.
               omega.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0.
    unfold not; split; intros.
    + destruct H9 as [ | H9].
      apply in_app_iff in H1.
      destruct H1 as [H1 | H1].
      ++ eapply rm_in. exact H1.
      ++ unfold exec_prim_ctr_in_state_with_owner in H7.
         apply execute_produces_new_contracts with (ctr' := ctr) in H7; try contradiction.
         apply H'; auto.
         trivial.
      ++  unfold exec_prim_ctr_in_state_with_owner in H7.
          apply execute_produces_new_contracts with (ctr' := ctr) in H7; try contradiction.
    + destruct H9 as [H9 | H9]; try inversion H9.
      apply T in H.
      destruct H as [_ H]; try contradiction.
    + rewrite in_app_iff in H1. destruct H1 as [H1 | H1].
      * eapply incl_rm in H1; eauto.
        split; unfold not; intro C; destruct C as [C | C].
        ** inversion C. apply H0 in H10; auto.
        ** apply T in H1. destruct H1 as [H1 H1']. contradiction.
        ** inversion C.
        ** apply T in H1. destruct H1 as [H1 H1']. contradiction.
      * split.
        ** unfold not. intros [E1 | E2].
           *** inversion E1.
               assert (H7' := H7); auto.
               eapply new_contracts_have_fresh_ids in H7'; eauto.
               unfold  next_id_is_fresh in H3.
               apply H' in H. omega.
           *** eapply new_contracts_have_fresh_ids in H7; eauto.
               assert (C : m_fresh_id s > ctr_id ctr).
               apply He. left. trivial.
               omega.
        ** unfold not. intros [E1 | E2].
           *** inversion E1.
           *** eapply new_contracts_have_fresh_ids in H7; eauto.
               assert (C : m_fresh_id s > ctr_id ctr).
               apply He. right. trivial.
               omega.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0.
    unfold not; split; intros.
    + destruct H9 as [ | H9].
      apply in_app_iff in H1.
      destruct H1 as [H1 | H1].
      ++ eapply rm_in. exact H1.
      ++ unfold exec_prim_ctr_in_state_with_owner in H7.
         apply execute_produces_new_contracts with (ctr' := ctr) in H7; try contradiction.
         apply H'; auto.
         trivial.
      ++  unfold exec_prim_ctr_in_state_with_owner in H7.
          apply execute_produces_new_contracts with (ctr' := ctr) in H7; try contradiction.
    + destruct H9 as [H9 | H9]; try inversion H9.
      apply T in H.
      destruct H as [_ H]; try contradiction.
    + rewrite in_app_iff in H1. destruct H1 as [H1 | H1].
      * eapply incl_rm in H1; eauto.
        split; unfold not; intro C; destruct C as [C | C].
        ** inversion C. apply H0 in H10; auto.
        ** apply T in H1. destruct H1 as [H1 H1']. contradiction.
        ** inversion C.
        ** apply T in H1. destruct H1 as [H1 H1']. contradiction.
      * split.
        ** unfold not. intros [E1 | E2].
           *** inversion E1.
               assert (H7' := H7); auto.
               eapply new_contracts_have_fresh_ids in H7'; eauto.
               unfold  next_id_is_fresh in H3.
               apply H' in H. omega.
           *** eapply new_contracts_have_fresh_ids in H7; eauto.
               assert (C : m_fresh_id s > ctr_id ctr).
               apply He. left. trivial.
               omega.
        ** unfold not. intros [E1 | E2].
           *** inversion E1.
           *** eapply new_contracts_have_fresh_ids in H7; eauto.
               assert (C : m_fresh_id s > ctr_id ctr).
               apply He. right. trivial.
               omega.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst ctr0.
    split; unfold not; intros; eapply rm_in; eauto.
    + eapply incl_rm in H1; eauto.
      split.
      * unfold not. intros [E1 | E2]; try inversion E1.
        apply T in E2; auto.
      * unfold not. intros [E1 | E2].
        ** inversion E1.
           apply H0 in H8; auto.
        ** apply T in E2; auto.
  - apply T; auto.
Qed.


Lemma step_preserves_consistent_state_5:
  forall s s',
    step s s' ->
    consistent_state s ->
    (forall e : Id,
        ~ (In (Executed e) (m_events s') /\ In (Deleted e) (m_events s'))).
Proof.
  intros.
  destruct H0 as [H' [He [H0 [T P]]]].
  induction H; subst s'; simpl in *; auto; unfold not; intros C.
  - destruct C as [[C | C'] [D | D']];
      try inversion C; try inversion D.
    unfold not in P. eapply P; eauto.
  - destruct C as [[C | C'] [D | D']];
      try inversion C; try inversion D.
    + apply T in H.
      destruct H as [_ H].
      subst. contradiction.
    + unfold not in P. eapply P; eauto.
  - destruct C as [[C | C'] [D | D']];
      try inversion C; try inversion D.
    + apply T in H.
      destruct H as [_ H].
      subst. contradiction.
    + unfold not in P. eapply P; eauto.
  - destruct C as [[C | C'] [D | D']];
      try inversion C; try inversion D.
    + apply T in H.
      destruct H as [_ H].
      subst. contradiction.
    + unfold not in P. eapply P; eauto.
  - destruct C as [[C | C'] [D | D']];
      try inversion C; try inversion D.
    + apply T in H.
      destruct H as [H _].
      subst. contradiction.
    + unfold not in P. eapply P; eauto.
Qed.


Theorem step_preserves_consistent_state:
  forall s s',
    step s s' ->
    consistent_state s ->
    consistent_state s'.
Proof.
  intros.
  unfold consistent_state.
  split.
  - eapply step_preserves_consistent_state_1; eauto.
  - split.
    + eapply step_preserves_consistent_state_2; eauto.
    + split.
      ++ eapply step_preserves_consistent_state_3; eauto.
      ++ split.
         ** eapply step_preserves_consistent_state_4; eauto.
         ** eapply step_preserves_consistent_state_5; eauto.
Qed.


Theorem steps_preserves_consistent_state:
  forall s s',
    steps s s' ->
    consistent_state s ->
    consistent_state s'.
Proof.
  intros.
  induction H; subst; auto.
  eapply step_preserves_consistent_state; eauto.
Qed.


Ltac insert_consistent s H :=
  let H' := fresh "H" in
  match goal with
  | H : steps _ s |- _ => 
    assert (H' : consistent_state s);
    try eapply steps_preserves_consistent_state; eauto
  | H : step _ s |- _ =>
    assert (H' : consistent_state s);
    try eapply step_preserves_consistent_state;eauto
  end.


Theorem events_consistent_step:
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
    + simpl. right. unfold not. intros [E1 | E2].
      * inversion E1. destruct H0 as [_ [_ [H' [_ _]]]].
        apply H' in  H10; auto.
      * destruct H0 as [_ [_ [_ [H' _]]]].
        apply H' in E2; trivial.
  - case_eq (ctr_eq_dec c ctr); intros.
    + subst. simpl. left. left. trivial.
    + simpl. right. unfold not. intros [E1 | E2].
      * inversion E1. destruct H0 as [_ [_ [H' [_ _]]]].
        apply H' in  H10; auto.
      * destruct H0 as [_ [_ [_ [H' _]]]].
        apply H' in E2; trivial.
  - case_eq (ctr_eq_dec c ctr); intros.
    + subst. simpl. left. left. trivial.
    + simpl. right. unfold not. intros [E1 | E2].
      * inversion E1. destruct H0 as [_ [_ [H' [_ _]]]].
        apply H' in  H10; auto.
      * destruct H0 as [_ [_ [_ [H' _]]]].
        apply H' in E2; trivial.
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



(* Metaproperties about contract execution *)

Lemma rm_other : forall cs c c',
    c <> c' ->
    In c cs ->
    In c (rm c' cs).
Proof.
  induction cs; auto; simpl in *.
  intros c c' D [H | H]; subst.
  - case_eq (ctr_eq_dec c' c); intros.
    + subst. contradiction.
    + simpl. left. reflexivity.
  - case_eq (ctr_eq_dec c' a); intros.
    + subst. apply IHcs; auto.
    + simpl. right. eapply IHcs; auto.
Qed.
      
  

Theorem step_effect_over_contract:
  forall ctr s s',
    step s s' ->
    In ctr (m_contracts s) ->
    (In ctr (m_contracts s') \/
     In (Executed (ctr_id ctr)) (m_events s') \/
     In (Deleted (ctr_id ctr)) (m_events s')).
Proof.
  intros *.
  intros H H'.
  induction H; subst s'; simpl; auto.
  - case_eq (ctr_eq_dec ctr0 ctr); intros.
    + subst ctr0. right. left. left. trivial.
    + left. rewrite in_app_iff. left. apply rm_other; auto.
  - case_eq (ctr_eq_dec ctr0 ctr); intros.
    + subst. right. left. simpl. left. trivial.
    + left. rewrite in_app_iff. left. apply rm_other; auto.
  - case_eq (ctr_eq_dec ctr0 ctr); intros.
    + subst. right. left. simpl. left. trivial.
    + left. rewrite in_app_iff. left. apply rm_other; auto.
  - case_eq (ctr_eq_dec ctr0 ctr); intros.
    + subst. right. right. simpl. left. trivial.
    + left. apply rm_other; auto.
Qed.


Theorem steps_effect_over_contract:
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

Lemma tick_not_applied:
  forall s s' ctr,
    step s s' ->
    In ctr (m_contracts s) ->
    In (Executed (ctr_id ctr)) (m_events s') ->
    consistent_state s ->
    m_global_time s = m_global_time s'.
Proof.
  intros.
  induction H; subst s'; trivial.
  simpl in *.
  unfold consistent_state in *.
  destruct H2 as [H2 H2'].
  apply H2' in H0.
  destruct H0 as [H0 _]; try contradiction.
Qed.


Theorem step_executes_only_one_contract:
  forall ctr ctr' s s',
    step s s' ->
    consistent_state s ->
    In ctr (m_contracts s) ->
    In ctr' (m_contracts s) ->
    In (Executed (ctr_id ctr)) (m_events s') ->
    In (Executed (ctr_id ctr')) (m_events s') ->
    ctr = ctr'.
Proof.
 intros *. intros H. induction H; intros; subst s'; unfold consistent_state in *.
 - destruct H5 as [O [A [H' [T P]]]].
   simpl in H8, H9.
   destruct H8 as [H8 | H8]; try inversion H8.
   destruct H9 as [H9 | H9]; try inversion H9.
   apply T in H8; auto; try contradiction.
 - simpl in H10, H11.
   destruct H10 as [H10 | H10]; try inversion H10.
   destruct H7 as  [O [A [H' [T P]]]].
   destruct H11 as [H11 | H11]; try inversion H11.
   + rewrite H7 in H12. apply H'; auto.
   + apply T in H9. destruct H9 as [H9 _]; contradiction.
   + destruct H7 as  [O [A [H' [T P]]]].
     destruct H11 as [H11 | H11]; try inversion H11.
     * apply T in H8.
       destruct H8 as [H8 _]; contradiction.
     * apply T in H8.
       destruct H8 as [H8 _]; contradiction.
 - simpl in H10, H11.
   destruct H10 as [H10 | H10]; try inversion H10.
   destruct H7 as [O [A [H' [T P]]]].
   destruct H11 as [H11 | H11]; try inversion H11.
   + rewrite H7 in H12. apply H'; auto.
   + apply T in H9. destruct H9 as [H9 _]; contradiction.
   + destruct H7 as [O [A [H' [T P]]]].
     destruct H11 as [H11 | H11]; try inversion H11.
     * apply T in H8.
       destruct H8 as [H8 _]; contradiction.
     * apply T in H8.
       destruct H8 as [H8 _]; contradiction.
 - simpl in H10, H11.
   destruct H10 as [H10 | H10]; try inversion H10.
   destruct H7 as [O [A [H' [T P]]]].
   destruct H11 as [H11 | H11]; try inversion H11.
   + rewrite H7 in H12. apply H'; auto.
   + apply T in H9. destruct H9 as [H9 _]; contradiction.
   + destruct H7 as [O [A [H' [T P]]]].
     destruct H11 as [H11 | H11]; try inversion H11.
     * apply T in H8.
       destruct H8 as [H8 _]; contradiction.
     * apply T in H8.
       destruct H8 as [H8 _]; contradiction.
 - simpl in H8, H9.
   destruct H8 as [H8 | H8]; try inversion H8.
   destruct H9 as [H9 | H9]; try inversion H9.
   destruct H5 as [O [A [H' [T P]]]].
   apply T in H8; auto; try contradiction.
 - simpl in H3, H4.
   destruct H0 as [O [A [H' [T P]]]].
   apply T in H3; auto; try contradiction.
Qed.


Theorem step_implies_execute_result:
  forall ctr s s',
    step s s' ->
    consistent_state s ->
    In ctr (m_contracts s) ->
    In (Executed (ctr_id ctr)) (m_events s') ->
    exists owner result,
      execute (ctr_primitive ctr)
              (ctr_scale ctr)
              (ctr_issuer ctr)
              owner
              (m_balance s)
              (m_global_time s)
              (m_gateway s)
              (ctr_id ctr)
              (ctr_desc_id ctr)
              (m_fresh_id s)
              (m_ledger s) =
      Some result.
Proof.
  intros ctr s s' H.
  revert ctr.
  induction H; intros; subst s'; simpl in *.
  - destruct H7 as [H7 | H7].
    inversion H7.
    apply H5 in H6.
    destruct H6 as [H6 _].
    contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst.
    unfold exec_ctr_in_state_with_owner in H5.
    unfold can_join in H0.
    destruct H0 as [H0 | H0].
    + eexists. eexists. subst. exact H5.
    + exists owner. eexists; eauto.
    + destruct H9  as [H9 | H9].
      * inversion H9. apply H7 in H11; auto. subst. contradiction.
      * apply H7 in H9; auto. contradiction.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst. rewrite H2. simpl. eexists; eexists; eauto.
    + destruct H9  as [H9 | H9].
      * inversion H9. apply H7 in H11; auto. subst. contradiction.
      * apply H7 in H9; auto. contradiction. Unshelve. auto.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    subst. rewrite H2. simpl. eexists. eexists. eauto.
    + destruct H9  as [H9 | H9].
      * inversion H9. apply H7 in H11; auto. subst. contradiction.
      * apply H7 in H9; auto. contradiction. Unshelve. auto.
  - case_eq (ctr_eq_dec ctr ctr0); intros; try contradiction.
    destruct H7 as [H7 | H7]; try inversion H7.
    apply H5 in H.
    destruct H as [H _].
    subst. contradiction.
    destruct H7  as [H7 | H7].
    * inversion H7.
    * apply H5 in H7; auto. contradiction.
  - destruct H0 as [_ [_ [_[H0 _]]]].
    apply H0 in H1.
    destruct H1 as [H1 _].
    subst. contradiction.
Qed.


Theorem step_does_not_remove_events:
  forall s s' e,
    step s s' ->
    In e (m_events s) ->
    In e (m_events s').
Proof.
  intros * H.
  revert e.
  induction H; intros; subst s'; simpl; try right; trivial.
Qed.


Theorem steps_does_not_remove_events:
  forall s s' e,
    steps s s' ->
    In e (m_events s) ->
    In e (m_events s').
Proof.
  intros.
  induction H; subst; auto.
  eapply step_does_not_remove_events; eauto.
Qed.


Theorem time_passes_one_step_at_a_time:
forall s s' n,
  step s s' ->
  m_global_time s' >= S n ->
  m_global_time s >= n.
Proof.
  intros. induction H; subst s'; simpl in *; try omega.
Qed.

Theorem time_passes_one_step_at_a_time':
forall s s' n,
  step s s' ->
  m_global_time s' = S n ->
  m_global_time s = n \/ m_global_time s = S n.
Proof.
  intros. induction H; subst s'; simpl in *; try omega.
Qed.

Theorem time_inc:
forall s s',
  step s s' ->
  m_global_time s <= m_global_time s'.
Proof.
  intros. induction H; subst s'; simpl; try omega.
Qed.

Theorem time_inc_steps:
forall s s',
  steps s s' ->
  m_global_time s <= m_global_time s'.
Proof.
  intros.
  induction H.
  - subst s2; omega.
  - apply time_inc in H0. omega.
Qed.

Theorem no_tick_if_event_generated:
forall s s' t,
  step s s' ->
  (exists e, In e (m_events s') /\ ~ In e (m_events s)) ->
  m_global_time s' >= t ->
  m_global_time s >= t.
Proof.
  intros. destruct H0 as [e [I NI]].
  induction H; subst s'; simpl in *; auto. contradiction.
Qed.

Theorem no_tick_if_event_generated':
forall s s' t,
  step s s' ->
  (exists e, In e (m_events s') /\ ~ In e (m_events s)) ->
  m_global_time s' = t ->
  m_global_time s = t.
Proof.
  intros. destruct H0 as [e [I NI]].
  induction H; subst s'; simpl in *; auto. contradiction.
Qed.

Lemma exists_step_in_steps:
  forall s1 s2 ctr,
    steps s1 s2 ->
    consistent_state s1 ->
    In ctr (m_contracts s1) ->
    ~ In (Executed (ctr_id ctr)) (m_events s1) ->
    In (Executed (ctr_id ctr)) (m_events s2) ->
    exists s s',
      steps s1 s /\
      step s s' /\
      steps s' s2 /\
      ~ In (Executed (ctr_id ctr)) (m_events s) /\
      In ctr (m_contracts s) /\
      In (Executed (ctr_id ctr)) (m_events s').
Proof.
  intros *.
  intros H.
  revert ctr.
  induction H; intros.
  - subst s2. contradiction.
  - assert (H' := H).
    apply steps_effect_over_contract with (ctr := ctr) in H; auto.
    destruct H as [H | [H | H]].
    + exists s, s2.
      repeat split; trivial.
      apply refl. trivial.
      apply steps_preserves_consistent_state in H'; trivial.
      destruct H' as [_ [_ [_ [H' _]]]].
      apply H' in H.
      destruct H as [H _].
      trivial.
    + apply IHsteps in H; auto.
      destruct H as [sk [sk' [Ss [S [Ss' [H'' [h1 h2]]]]]]].
      exists sk, sk'.
      repeat split; trivial.
      eapply tran; eauto.
    + eapply step_does_not_remove_events in H; eauto.
      eapply steps_preserves_consistent_state in H'; trivial.
      eapply step_preserves_consistent_state in H'; eauto.
      destruct H' as [_ [_ [_ [_ H']]]].
      exfalso.
      eapply H'; eauto.
Qed.


(* Utils *)
Lemma same_contract :
  forall c c' s,
    consistent_state s ->
    In c' (m_contracts s) ->
    In c (m_contracts s) ->
    (Executed (ctr_id c') = Executed (ctr_id c) \/
     In (Executed (ctr_id c)) (m_events s)) ->
    c' = c.
Proof.
  intros.
  case_eq (ctr_eq_dec c c'); intros; auto.
  destruct H2 as [H2 | H2].
  - inversion H2. inconsistent H H5.
  - inconsistent H  H2.
Qed.

Lemma same_contract_del :
  forall c c' s,
    consistent_state s ->
    In c' (m_contracts s) ->
    In c (m_contracts s) ->
    (Deleted (ctr_id c') = Deleted (ctr_id c) \/
     In (Deleted (ctr_id c)) (m_events s)) ->
    c' = c.
Proof.
  intros.
  case_eq (ctr_eq_dec c c'); intros; auto.
  destruct H2 as [H2 | H2].
  - inversion H2. inconsistent H H5.
  - inconsistent H H2.
Qed.

Ltac same_ctr H := simpl in H; apply same_contract in H; auto.
Ltac same_ctr_del H := simpl in H; apply same_contract_del in H; auto.
Ltac not_or' ctr H := subst ctr; simpl in H; inversion H.


Ltac resolve_impossible_delete Ev :=
  simpl; [ try inversion_event Ev; try find_contradiction_del Ev |
           try inversion_event Ev; try find_contradiction_del Ev |
           try inversion_event Ev; try find_contradiction_del Ev |
           try inversion_event Ev; try find_contradiction_del Ev |
           auto |
           try inversion_event Ev; try find_contradiction_del Ev ].
