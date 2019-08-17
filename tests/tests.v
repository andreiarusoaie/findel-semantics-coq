Load helpers.

(* firl = fixed interest rate loan *)

Definition firl_description (t : Time) :=
  (And
     (Before t (Or (Give (One USD)) (Give (One EUR))))
     (After (t +2) (Scale 2 (One EUR)))
  ).

Definition Alice := 101.
Definition Bob   := 102.
Print execute.
Definition default_scale := 1.
Definition default_time := 1.
Definition fresh_id := 10.
Definition default_ctr_id := 0.
Definition default_desc_id := 0.
Definition default_ledger : list Transaction := [].
Definition default_gateway : list Gateway := [].
Definition emptybal : Address -> Currency -> Z :=
  fun (a : Address) (c : Currency) => Z_of_nat 0.
Definition alice_bal_usd :=
  update emptybal Alice USD 100.
Definition alice_bal_eur :=
  update alice_bal_usd Alice EUR 50.
Definition bob_bal_usd :=
  update alice_bal_eur Bob USD 20.
Definition bob_bal_eur :=
  update bob_bal_usd Bob EUR 30.
Definition some_balance := bob_bal_eur.

Eval compute in some_balance Bob USD.

Definition default_exec (p : Primitive) :=
  (execute
     p
     default_scale
     Alice
     Bob
     some_balance
     3
     default_gateway
     default_ctr_id 
     default_desc_id
     fresh_id
     default_ledger).


Definition result_ := default_exec (firl_description 3).
Print result_.
Eval compute in result_.
Check result_.
Check (match result_ with
                 | None => []
                 | Some v => res_contracts v
       end).

Eval compute in (match result_ with
                 | None => emptybal
                 | Some v => res_balance v
                 end) Bob USD.

Eval compute in (match result_ with
                 | None => []
                 | Some v => res_contracts v
       end).

Lemma gsdfg : forall r, result_ = r.
  intros. unfold result_.
  unfold firl_description, default_exec.
  simpl.
  case_eq (INF <? default_time); intros.
  - admit.
  - simpl.
  

Definition balance_of (r : option Result) (a : Address) (c : Currency) :=
  (match r with
   | None => emptybal
   | Some v => res_balance v
   end) a c.
Check balance_of.
Check result_.
Check (balance_of result_ Alice USD).

Eval compute in (balance_of result_) Alice USD.
Eval compute in (balance_of result_ Alice EUR).
Eval compute in (balance_of result_ Bob USD).
Eval compute in (balance_of result_ Bob EUR).

Eval compute in
    (match result_ with
    | None => emptybal
    | Some v => res_balance v
    end) Bob USD.
Eval compute in
    (match exe with
    | None => emptybal
    | Some v => res_balance v
    end) Alice EUR.
Eval compute in
    (match exe with
    | None => emptybal
    | Some v => res_balance v
    end) Alice EUR.

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
