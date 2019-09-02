Load findel.

Definition Alice := 101.
Definition Bob   := 102.
Definition default_scale := 1.
Definition now := 1.
Definition time (z : nat) := z.
Definition fresh_id := 10.
Definition default_ctr_id := 0.
Definition default_desc_id := 0.
Definition default_ledger : list Transaction := [].
Definition default_gateway : list Gateway := [].
Definition g1 : Gateway := (gateway 1000 0 100).
Definition g2 : Gateway := (gateway 1001 1 1000).
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

Definition default_exec (p : Primitive) :=
  (execute
     p
     default_scale
     Alice
     Bob
     default_balance
     now
     default_gateway
     default_ctr_id
     default_desc_id
     fresh_id
     default_ledger).

Definition default_exec_gtw (p : Primitive) (g : list Gateway) :=
  (execute
     p
     default_scale
     Alice
     Bob
     default_balance
     now
     g
     default_ctr_id
     default_desc_id
     fresh_id
     default_ledger).


Definition T1_one := One USD.
Definition T2_simple_currency_exchange :=
  (And
     (Give (Scale 11 (One USD)))
     (Scale 10 (One EUR))
  ).
Definition T3_zcb := (At (now + 1) (Scale 10 (One USD))).
Definition T4_bond_with_2_coupons :=
  (And
     (And
        (At (now + 1) (One USD))
        (At (now + 2) (One EUR))
     )
     (At (now + 3) (Scale 5 (One USD)))
  ).
Definition T5_european_option :=
  (At (now + 1) (Or (One USD) (One EUR))).
Definition T6_boolean_gateway (g : Gateway) :=
  (If (gtw_addr g) (One USD) (One EUR)).
Definition T7_numeric_gateway :=
  (ScaleObs (gtw_addr g2) (One USD)).
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
Definition T9_timebound (g : Gateway) (t0 t1 : nat) :=
  (Timebound t0 t1
             (ScaleObs (gtw_addr g)
                       (Give (Or
                                (Scale 5 (One USD))
                                (Scale 10 (One EUR))
                             )
                       )

             )
  ).


Eval compute in default_exec T1_one.
Eval compute in
    (match default_exec T1_one with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob USD
                   end
     end
    ).
Eval compute in
    (match default_exec T1_one with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice USD
                   end
     end
    ).



Eval compute in default_exec T2_simple_currency_exchange.
Eval compute in
    (match default_exec T2_simple_currency_exchange with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob USD
                   end
     end
    ).
Eval compute in
    (match default_exec T2_simple_currency_exchange with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice USD
                   end
     end
    ).
Eval compute in
    (match default_exec T2_simple_currency_exchange with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob EUR
                   end
     end
    ).
Eval compute in
    (match default_exec T2_simple_currency_exchange with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice EUR
                   end
     end
    ).


Eval compute in default_exec T3_zcb.
Eval compute in
    (match default_exec T3_zcb with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob USD
                   end
     end
    ).
Eval compute in
    (match default_exec T3_zcb with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice USD
                   end
     end
    ).


Eval compute in default_exec T5_european_option.
Eval compute in
    (match default_exec T5_european_option with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob USD
                   end
     end
    ).
Eval compute in
    (match default_exec T5_european_option with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice USD
                   end
     end
    ).
Eval compute in
    (match default_exec T5_european_option with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob EUR
                   end
     end
    ).
Eval compute in
    (match default_exec T5_european_option with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice EUR
                   end
     end
    ).
Eval compute in
    (match default_exec T5_european_option with
     | None => []
     | Some res => match res with
                     result _ c _ _ => c
                   end
     end
    ).


Eval compute in (default_exec_gtw (T6_boolean_gateway g1) [g1]).
Eval compute in
    (match (default_exec_gtw (T6_boolean_gateway g1) [g1]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob EUR
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw (T6_boolean_gateway g1) [g1]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice EUR
                   end
     end
    ).
Eval compute in (default_exec_gtw (T6_boolean_gateway g2) [g2]).
Eval compute in
    (match (default_exec_gtw (T6_boolean_gateway g2) [g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob USD
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw (T6_boolean_gateway g2) [g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice USD
                   end
     end
    ).

Eval compute in (default_exec_gtw T7_numeric_gateway [g2]).
Eval compute in
    (match (default_exec_gtw T7_numeric_gateway [g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob USD
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw T7_numeric_gateway [g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice USD
                   end
     end
    ).


Eval compute in (default_exec_gtw (T8_complex_scale_obs g1 g2) [g1; g2]).
Eval compute in
    (match (default_exec_gtw  (T8_complex_scale_obs g1 g2) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob USD
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw  (T8_complex_scale_obs g1 g2) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice USD
                   end
     end
    ).
Eval compute in (default_exec_gtw (T8_complex_scale_obs g2 g1) [g1; g2]).
Eval compute in
    (match (default_exec_gtw  (T8_complex_scale_obs g2 g1) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob USD
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw  (T8_complex_scale_obs g2 g1) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice USD
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw  (T8_complex_scale_obs g1 g2) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob EUR
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw  (T8_complex_scale_obs g1 g2) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice EUR
                   end
     end
    ).
Eval compute in (default_exec_gtw (T8_complex_scale_obs g2 g1) [g1; g2]).
Eval compute in
    (match (default_exec_gtw  (T8_complex_scale_obs g2 g1) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob EUR
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw  (T8_complex_scale_obs g2 g1) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice EUR
                   end
     end
    ).



Eval compute in (default_exec_gtw (T9_timebound g1 0 10) [g1; g2]).
Eval compute in
    (match (default_exec_gtw (T9_timebound g1 0 10) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob EUR
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw (T9_timebound g1 0 10) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice EUR
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw (T9_timebound g1 0 10) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob EUR
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw (T9_timebound g1 0 10) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice EUR
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw (T9_timebound g2 0 10) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob EUR
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw (T9_timebound g1 0 10) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice EUR
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw (T9_timebound g1 0 10) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Bob EUR
                   end
     end
    ).
Eval compute in
    (match (default_exec_gtw (T9_timebound g1 0 10) [g1; g2]) with
     | None => 0%Z
     | Some res => match res with
                     result bal _ _ _ => bal Alice EUR
                   end
     end
    ).
