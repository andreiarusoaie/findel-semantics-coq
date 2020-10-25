Load findel.

Definition Alice := 101.
Definition Bob   := 102.
Definition default_scale := 1.
Definition now := 1234.
Definition time (z : nat) := z.
Definition fresh_id := 10.
Definition default_ctr_id := 0.
Definition default_desc_id := 0.
Definition default_ledger : list Transaction := [].
Definition default_gateway : list Gateway := [].
Definition g1 : Gateway := (gateway 1000 0 (now + 100)).
Definition g2 : Gateway := (gateway 1001 1 (now + 1000)).
Definition g3_expired : Gateway := (gateway 1002 1 0).
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
Definition default_balance := bob_bal_eur.

Eval compute in default_balance Bob USD.
Eval compute in default_balance Bob EUR.
Eval compute in default_balance Alice USD.
Eval compute in default_balance Alice EUR.

Definition exec (p : Primitive) (t : Time) (gtw : list Gateway) :=
  (execute 
     p
     default_scale
     Alice
     Bob
     default_balance
     t
     gtw
     default_ctr_id
     default_desc_id
     fresh_id
     default_ledger).

Definition default_exec (p : Primitive) := exec p now default_gateway.
Definition default_exec_at (p : Primitive) (t : Time) := exec p t default_gateway.
Definition default_exec_gtw (p : Primitive) (g : list Gateway) := exec p now g.

(*  Helpers for extraction *)
Definition balance_after_exec (p : Primitive)
           (party : Address) (c : Currency) :=
  match default_exec p with
  | None => None
  | Some res => match res with
                  result bal _ _ _ => Some (bal party c)
                end
  end.
Definition balance_after_exec_at
           (p : Primitive) (t : Time)
           (party : Address) (c : Currency) :=
  match default_exec_at p t with
  | None => None
  | Some res => match res with
                  result bal _ _ _ => Some (bal party c)
                end
  end.
Definition balance_after_exec_gtw
           (p : Primitive) (gtw : list Gateway)
           (party : Address) (c : Currency) :=
  match default_exec_gtw p gtw with
  | None => None
  | Some res => match res with
                  result bal _ _ _ => Some (bal party c)
                end
  end.




(* Tests *)

(* Test  #0 *)
Definition T0_zero := Zero.
(* the contract executes, the balance does not change *)
Compute default_balance Bob USD.
Compute balance_after_exec T0_zero Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec T0_zero Alice USD.


(* Test  #1 *)
Definition T1_one := One USD.
(* the contract executes, Alice pays 1 USD to Bob *)
Compute default_balance Bob USD.
Compute balance_after_exec T1_one Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec T1_one Alice USD.


(* Test #2 *)
Definition T2_simple_currency_exchange :=
  (And
     (Give (Scale 11 (One USD)))
     (Scale 10 (One EUR))
  ).
(* Alice pays 10 EUR to Bob, Bob pays 11 USD to Alice *)
Compute default_balance Bob USD.
Compute balance_after_exec T2_simple_currency_exchange Bob USD.
Compute default_balance Bob EUR.
Compute balance_after_exec T2_simple_currency_exchange Bob EUR.
Compute default_balance Alice USD.
Compute balance_after_exec T2_simple_currency_exchange Alice USD.
Compute default_balance Alice EUR.
Compute balance_after_exec T2_simple_currency_exchange Alice EUR.


(* Test #3 *)
Definition T3_zcb := (At (now + 60) (Scale 10 (One USD))).
(* current time: before now + t, no changes *)
Compute default_balance Bob USD.
Compute balance_after_exec_at T3_zcb now Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_at T3_zcb now Alice USD.

(* current time: at now + t, Alice pays 10 USD to Bob *)
Compute default_balance Bob USD.
Compute balance_after_exec_at T3_zcb (now + 60) Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_at T3_zcb (now + 60) Alice USD.

(* current time: after (now + t) + Δ + 1, contract deleted *)
Compute default_balance Bob USD.
Compute balance_after_exec_at T3_zcb (now + 60 + Δ + 1) Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_at T3_zcb (now + 60 + Δ + 1) Alice USD.


(* Test #4 *)
Definition T4_bond_with_2_coupons :=
  (And
     (And
        (At (now + 60) (One USD))
        (At (now + 120) (One EUR))
     )
     (At (now + 180) (Scale 5 (One USD)))
  ).
(* current time: before now + 60, three new contracts generated *)
Compute default_balance Bob USD.
Compute balance_after_exec_at T4_bond_with_2_coupons now Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_at T4_bond_with_2_coupons now Alice USD.
Compute default_balance Bob EUR.
Compute balance_after_exec_at T4_bond_with_2_coupons now Bob EUR.
Compute default_balance Alice EUR.
Compute balance_after_exec_at T4_bond_with_2_coupons now Alice EUR.
Compute
  match default_exec_at T4_bond_with_2_coupons now with
  | None => None
  | Some (result _ A _ _) => Some A
  end.
(* current time: at now + 60, Alice pays 1 USD to Bob; two new contracts are generated *)
Compute default_balance Bob USD.
Compute balance_after_exec_at T4_bond_with_2_coupons (now + 60) Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_at T4_bond_with_2_coupons (now + 60) Alice USD.
Compute default_exec_at T4_bond_with_2_coupons (now + 60).
Compute
  match default_exec_at T4_bond_with_2_coupons (now + 60) with
  | None => None
  | Some (result _ A _ _) => Some A
  end.
(* current time: at (now + 60) + Δ + 1, the sequence fails to execute, no changes *)
Compute default_exec_at T4_bond_with_2_coupons (now + 60 + Δ + 1).


(* Test #5 *)
Definition T5_european_option :=
  (At (now + 60) (Or (One USD) (One EUR))).
(* current time: before now + 60, balance does not change, a new contract is generated *)
Compute default_balance Bob USD.
Compute balance_after_exec_at T5_european_option now Bob USD.
Compute default_balance Bob EUR.
Compute balance_after_exec_at T5_european_option now Bob EUR.
Compute default_balance Alice USD.
Compute balance_after_exec_at T5_european_option now Alice USD.
Compute default_balance Alice EUR.
Compute balance_after_exec_at T5_european_option now Alice EUR.
Compute
  match default_exec_at T5_european_option now with
  | None => None
  | Some (result _ A _ _) => Some A
  end.
(* current time: at now + 60, balance does not change, new option contract is generated *)
Compute default_balance Bob USD.
Compute balance_after_exec_at T5_european_option (now + 60) Bob USD.
Compute default_balance Bob EUR.
Compute balance_after_exec_at T5_european_option (now + 60) Bob EUR.
Compute default_balance Alice USD.
Compute balance_after_exec_at T5_european_option (now + 60) Alice USD.
Compute default_balance Alice EUR.
Compute balance_after_exec_at T5_european_option (now + 60) Alice EUR.
Compute
  match default_exec_at T5_european_option (now + 60) with
  | None => None
  | Some (result _ A _ _) => Some A
  end.


(* Test #6 *)
Definition T6_boolean_gateway (g : Gateway) :=
  (If (gtw_addr g) (One USD) (One EUR)).
(* gateway g1 status: false, Alice pays 1 EUR to Bob *)
Compute default_balance Bob EUR.
Compute balance_after_exec_gtw (T6_boolean_gateway g1) [g1] Bob EUR.
Compute default_balance Alice EUR.
Compute balance_after_exec_gtw (T6_boolean_gateway g1) [g1] Alice EUR.
(* gateway g2 status: true, Alice pays 1 USD to Bob *)
Compute default_balance Bob USD.
Compute balance_after_exec_gtw (T6_boolean_gateway g2) [g2] Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_gtw (T6_boolean_gateway g2) [g2] Alice USD.
(* gateway g3 status: gateway value is not fresh, contract deleted *)
Compute
  match default_exec_gtw (T6_boolean_gateway g3_expired) [g3_expired] with
  | None => None
  | Some (result _ A _ _) => Some A
  end.


(* Test #7 *)
Definition T7_numeric_gateway :=
  (ScaleObs (gtw_addr g2) (One USD)).
(* gateway g2 status: true, Alice pays 1 USD to Bob *)
Compute default_balance Bob USD.
Compute balance_after_exec_gtw T7_numeric_gateway [g2] Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_gtw (T6_boolean_gateway g2) [g2] Alice USD.
(* gateway g3 status: gateway value is not fresh, contract deleted *)
Compute
  match default_exec_gtw T7_numeric_gateway [g3_expired] with
  | None => None
  | Some (result _ A _ _) => Some A
  end.


(* Test #8 *)
Definition T8_complex_scale_obs (g g' : Gateway) :=
  (Scale 10
         (And
            (ScaleObs (gtw_addr g) (Give (Or
                                            (Scale 5 (One USD))
                                            (ScaleObs (gtw_addr g) (Scale 10 (One EUR)))
                                         )
                                   )
            )
            (If (gtw_addr g')
                Zero
                (And
                   (Scale 3 (One USD))
                   (Give (Scale 7 (One EUR)))
                )
            )
         )
  ).
(* gateways (g1, g1) status: (false, false)
ScaleObs fails, If-else is executed: 
  1) Alice pays 30 USD to Bob
  2) Bob pays 70 EUR to Alice
 *)
Compute default_balance Bob EUR.
Compute balance_after_exec_gtw (T8_complex_scale_obs g1 g1) [g1;g2] Bob EUR.
Compute default_balance Alice EUR.
Compute balance_after_exec_gtw (T8_complex_scale_obs g1 g1) [g1;g2] Alice EUR.
Compute default_balance Bob USD.
Compute balance_after_exec_gtw (T8_complex_scale_obs g1 g1) [g1;g2] Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_gtw (T8_complex_scale_obs g1 g1) [g1;g2] Alice USD.

(* gateways (g1, g2) status: (false, true) 
ScaleObs fails, If-true is executed: balance does not change
 *)
Compute default_balance Bob EUR.
Compute balance_after_exec_gtw (T8_complex_scale_obs g1 g2) [g1;g2] Bob EUR.
Compute default_balance Alice EUR.
Compute balance_after_exec_gtw (T8_complex_scale_obs g1 g2) [g1;g2] Alice EUR.
Compute default_balance Bob USD.
Compute balance_after_exec_gtw (T8_complex_scale_obs g1 g2) [g1;g2] Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_gtw (T8_complex_scale_obs g1 g2) [g1;g2] Alice USD.
(* gateways (g2, g1) status: (true, false) 
ScaleObs succeeds, If-false is executed: 
  1) Alice pays 30 USD to Bob
  2) Bob pays 70 EUR to Alice
  3) an option contract for Alice is generated
 *)
Compute default_balance Bob EUR.
Compute balance_after_exec_gtw (T8_complex_scale_obs g2 g1) [g1;g2] Bob EUR.
Compute default_balance Alice EUR.
Compute balance_after_exec_gtw (T8_complex_scale_obs g2 g1) [g1;g2] Alice EUR.
Compute default_balance Bob USD.
Compute balance_after_exec_gtw (T8_complex_scale_obs g2 g1) [g1;g2] Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_gtw (T8_complex_scale_obs g2 g1) [g1;g2] Alice USD.
Compute
  match default_exec_gtw (T8_complex_scale_obs g2 g1) [g1;g2] with
  | None => None
  | Some (result _ A _ _) => Some A
  end.
(* gateways (g2, g2) status: (true, true) 
ScaleObs succeeds, If-true is executed: 
  1) an option contract for Alice is generated
 *)
Compute default_balance Bob EUR.
Compute balance_after_exec_gtw (T8_complex_scale_obs g2 g2) [g1;g2] Bob EUR.
Compute default_balance Alice EUR.
Compute balance_after_exec_gtw (T8_complex_scale_obs g2 g2) [g1;g2] Alice EUR.
Compute default_balance Bob USD.
Compute balance_after_exec_gtw (T8_complex_scale_obs g2 g2) [g1;g2] Bob USD.
Compute default_balance Alice USD.
Compute balance_after_exec_gtw (T8_complex_scale_obs g2 g2) [g1;g2] Alice USD.
Compute
  match default_exec_gtw (T8_complex_scale_obs g2 g2) [g1;g2] with
  | None => None
  | Some (result _ A _ _) => Some A
  end.


(* Test #9 *)
Definition T9_timebound (g : Gateway) (t0 t1 : nat) :=
  (Timebound (interval t0 t1)
             (ScaleObs (gtw_addr g)
                       (Give (Or
                                (Scale 5 (One USD))
                                (Scale 10 (One EUR))
                             )
                       )

             )
  ).
(* current time: before now, the contract is available for execution in the future *)
Compute
  match exec (T9_timebound g1 now (now + 60)) (pred now) [g1;g2] with
  | None => None
  | Some (result _ A _ _) => Some A
  end.
(* current time: now
   gateway g1 status: scale 1
   the option contract is generated, with Bob as issuer, Alice as p_owner, and scale 0
*)
Compute
  match exec (T9_timebound g1 now (now + 60)) now [g1;g2] with
  | None => None
  | Some (result _ A _ _) => Some A
  end.
(* current time: now
   gateway g2 status: scale 1
   the timebound contract is executed
   an option contract is generated, with Bob as issuer, Alice as proposed owner, and scale 1
*)
Compute
  match exec (T9_timebound g2 now (now + 60)) now [g1;g2] with
  | None => None
  | Some (result _ A _ _) => Some A
  end.
(* current time: now
   gateway g3_expired status: expired
   no contract is generated
 *)
Compute
  match exec (T9_timebound g3_expired now (now + 60)) now [g1;g2;g3_expired] with
  | None => None
  | Some (result _ A _ _) => Some A
  end.
