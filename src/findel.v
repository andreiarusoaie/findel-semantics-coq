Require Import String.
Require Import ZArith.
Require Import List.
Require Import Omega.
Import ListNotations.
Scheme Equality for list.


Definition Δ := 30.
Parameter INF : nat.
Axiom infinite : forall n, n < INF.
Definition FRESHNESS := 2.


Inductive Currency :=
| USD  : Currency
| EUR  : Currency
| GBP  : Currency
| JPY  : Currency
| CNY  : Currency
| SGD  : Currency
| NONE : Currency.
Definition beq_currency (c c' : Currency) :=
  match c, c' with
  | USD , USD  => true
  | EUR , EUR  => true
  | GBP , GBP  => true
  | JPY , JPY  => true
  | CNY , CNY  => true
  | SGD , SGD  => true
  | NONE, NONE => true
  | _, _ => false
  end.


Definition Address := nat. (* convention: 0 stands for 0x0 *)
Definition Time := nat.

Definition Balance := Address -> Currency -> Z.
Definition update (balance : Balance) (a : Address)
           (c : Currency) (amount : Z): Balance :=
  fun (x : Address) (y : Currency) =>
    if (andb (Nat.eqb x a) (beq_currency c y))
    then amount
    else (balance x y).


Inductive Primitive :=
(* basic primitives *)
| Zero      :                                      Primitive
| One       : Currency ->                          Primitive
(* composite primitives *)
| Scale     : nat -> Primitive ->                  Primitive 
| ScaleObs  : Address -> Primitive ->              Primitive
| Give      : Primitive ->                         Primitive
| And       : Primitive -> Primitive ->            Primitive
| Or        : Primitive -> Primitive ->            Primitive
| If        : Address -> Primitive -> Primitive -> Primitive
| Timebound : nat -> nat -> Primitive ->           Primitive.

Definition At (t : nat) (p : Primitive) := Timebound (t - Δ) (t + Δ) p.
Definition Before (t : nat) (p : Primitive) := Timebound 0 t p.
Definition After (t : nat) (p : Primitive) := Timebound t INF p.
Definition Sell (n : nat) (c : Currency) (p : Primitive)
  := And (Give (Scale n (One c))) p.


Record Gateway :=
  gateway {
      gtw_addr : Address;
      gtw_value : nat;
      gtw_timestamp : nat
    }.
Definition refresh (g : Gateway) (v' : nat) : Gateway :=
  match g with
  | gateway a v f => gateway a v' 0
  end.
Definition update_fresh (g : Gateway) (t : Time) : Gateway :=
  match g with
  | gateway a v f => gateway a v t
  end.
Fixpoint gateway_time_update
         (g : list Gateway) (t : Time) : list Gateway :=
  match g with
  | gtw :: rest =>
    (update_fresh gtw t) :: (gateway_time_update rest t)
  | [] => []
  end.
Fixpoint query(gateway : list Gateway)(a : Address)(now : Time) :=
  match gateway with
  | (gateway addr val timestamp) :: rest =>
    if (beq_nat a addr)
    then if (leb now (timestamp + FRESHNESS))
         then Some val
         else None
    else query rest a now
  | [] => None
  end.



Definition Id := nat.
Record Transaction :=
  transaction {
      tr_id : Id;
      tr_ctr_id : nat;
      tr_from: Address;
      tr_to : Address;
      tr_amount : nat;
      tr_currency : Currency;
      tr_timestamp : Time 
    }.
Record FinContract :=
  finctr {
      ctr_id : Id;
      ctr_desc_id : Id;
      ctr_primitive : Primitive;
      ctr_issuer : Address;
      ctr_owner : Address;
      ctr_proposed_owner : Address;
      ctr_scale : nat;
    }.
Record Result :=
  result {
      res_balance : Balance;
      res_contracts : list FinContract;
      res_next : Id;
      res_ledger : list Transaction
    }.


(** * Executing primitives recursively

The execute\_primitive function executes a primitive recursively.
The function outputs a tuple consisting of:
 1. The balance of the participants after the execution;
 2. The list of contracts (when Or or Timebound are executed) that need to be issued when executing the current primitive;
 3. The next available global identifier;
 4. The updated ledger with transactions operated when executing the current primitive.

The second component of the tuple is not empty in two situations: either Or is the current primitive to be executed; or Timebound t0 t1 is the current primitive and the current time is less than t0.
If all subcontracts result in chaging the balance of the parties, then

*) 
Fixpoint execute
         (P:Primitive) (scale:nat) (I O : Address)
         (balance : Balance) (time : Time) (gtw : list Gateway)
         (ctr_id : Id) (dsc_id : Id)  (nextId : nat)
         (ledger : list Transaction) : option Result :=
  match P with
  | Zero => Some (result balance [] nextId ledger)
  | One currency =>
    (*    if (Nat.leb 0 (balance I currency - scale)) *)
    (*then*)
    Some (result
            (update (update balance I currency ((balance I currency) - (Z_of_nat scale)))
                    O currency ((balance O currency) + (Z_of_nat scale)))
            [] (S nextId)
            ((transaction nextId ctr_id I O scale currency time) :: ledger)
         )
  (*    else None *)
  | Scale k c =>
    (execute c (scale * k) I O balance time gtw ctr_id dsc_id nextId ledger)
  | ScaleObs addr c =>
    match (query gtw addr time) with
    | None => None
    | Some k =>
      (execute c (scale * k) I O balance time gtw ctr_id dsc_id nextId ledger)
    end
  | Give c =>
    (execute c scale O I balance time gtw ctr_id dsc_id nextId ledger)
  | And c1 c2 =>
    match (execute c1 scale I O balance time gtw ctr_id dsc_id nextId ledger) with
    | None => None
    | Some (result bal1 Is1 nextId1 ledger') =>
      match (execute c2 scale I O bal1 time gtw ctr_id dsc_id nextId1 ledger') with
      | None => None
      | Some (result bal2 Is2 nextId2 ledger'') =>
        Some (result bal2 (Is1 ++ Is2) nextId2 ledger'')
      end
    end
  | If addr c1 c2 =>
    match (query gtw addr time) with
    | None => None
    | Some v =>
      if beq_nat v 0
      then (execute c2 scale I O balance time gtw ctr_id dsc_id nextId ledger)
      else (execute c1 scale I O balance time gtw ctr_id dsc_id nextId ledger)
    end
  | Timebound t0 t1 p =>
    if (t1 <? time)
    then None
    else
      if (t0 <? time)
      then (execute p scale I O balance time gtw ctr_id dsc_id nextId ledger)
      else Some (result balance
                        [(finctr (S nextId) dsc_id (Timebound t0 t1 p) I O O scale)] (S (S nextId)) ledger)
  | Or c1 c2 =>
    Some (result balance
                 [(finctr (S nextId) dsc_id (Or c1 c2) I O O scale)] (S (S nextId)) ledger)
  end.


Record ContractDescription :=
  description {
      dsc_id : Id;
      dsc_prim : Primitive;
      dsc_scale : nat;
      dsc_gateway_of : list Gateway;
      dsc_valid_from : Time;
      dsc_valid_until : Time;
    }.

Definition ContractDescriptions := nat -> ContractDescription.



Inductive Event :=
| IssuedFor : Address -> Id -> Event
| Executed : Id -> Event
| Deleted : Id -> Event.

(** * The State

The State includes the list of issued contracts, the list of contract descriptions, a balance that stores the amount of tokens for each account owner, and the current time. Additionally we use a natural number as identifier for contract instances.

*) 

Record State :=
  state {
      m_contracts : list FinContract;
      m_descriptions : ContractDescriptions;
      m_balance : Balance;
      m_global_time : Time;
      m_gateway : list Gateway;
      m_fresh_id : Id;
      m_ledger : list Transaction;
      m_events : list Event
    }.


(** * The step relation

The semantics of the Findel contracts is given by the {\tt step} relation. In addition, we use a helper function called {\tt execute\_primitive}, which is used to recursively execute a contract. The function receives as input a primitive, a number representig the scale, the addresses of the issuer and the owner, their corresponding balance, the current timestamp, the external gateway, and the [begin, end] interval which represent the time boundaries when this contract can be executed. The function returns a pair consisting of the balance after the execution and a list of contracts to be issued.

1. If the primitive is {\tt Zero}, then return the current balance and list of contracts.
2. If the current primitive is {\tt One}, then the function updates the balance of the participants by transferring {\tt scale * 1} units of currency from the issuer to the owner.



*)

(** * Execution model

A Findel contract has the following execution model~\cite{findel}:

1. The first party issues a contract having itself as the issue, the owner and somebody else as a proposedOwner. In our semantics, the list of the issued contracts is kept by first component of the State (i.e., list FinContract);

2. Anyone can try to join the contract, but only the proposed owner can actually join it. Once an issued contract is joined, it's execution starts immediately.

3. The execution of a contract -- more precisely, the execution of its corresponding primitive -- either has an effect on the balance of the participants, or it issues new contracts. In the Coq semantics, we use the function {\tt execute\_primitive} to execute a primitive.

*)

Axiom ctr_eq_dec : forall c c' : FinContract, {c = c'} + {c <> c}.

Fixpoint rm (c : FinContract) (l : list FinContract) :=
  match l with
  | [] => []
  | (c' :: l) => if ctr_eq_dec c c'
                 then (rm c l)
                 else c' :: (rm c l)
  end.


Fixpoint greater_than_all (id : nat) (ctrs : list FinContract) :=
  match ctrs with
  | [] => True
  | (finctr f_id _ _ _ _ _ _ ) :: ctrs' => id > f_id /\ greater_than_all id ctrs'
  end.


Definition is_or  (primitive: Primitive):=
  match primitive with
  | Or _ _  => True
  | _ => False
  end.

Definition is_timebound  (primitive: Primitive):=
  match primitive with
  | Timebound _ _ _ => True
  | _ => False
  end.


Definition consistent_description(dsc : ContractDescription) :=
      dsc_valid_from dsc <= dsc_valid_until dsc.


Definition between_time_limits (ctr : FinContract) (state : State) :=
  dsc_valid_from ((m_descriptions state) (ctr_desc_id ctr)) <=
  (m_global_time state) <=
  dsc_valid_until ((m_descriptions state) (ctr_desc_id ctr)).

Definition can_join (owner : Address)(ctr : FinContract) :=
  (owner = ctr_proposed_owner ctr \/ ctr_proposed_owner ctr = 0).


Definition next_id_is_fresh (state : State) :=
  (greater_than_all (m_fresh_id state) (m_contracts state)).
      

Definition exec_ctr_in_state_with_owner
           (ctr : FinContract) (state : State) (owner : Address) :=
  execute (ctr_primitive ctr)
                    (ctr_scale ctr)
                    (ctr_issuer ctr)
                    owner
                    (m_balance state)
                    (m_global_time state)
                    (m_gateway state)
                    (ctr_id ctr)
                    (ctr_desc_id ctr)
                    (m_fresh_id state)
                    (m_ledger state).


Definition exec_prim_ctr_in_state_with_owner
           (p : Primitive) (ctr : FinContract) (state : State) (owner : Address) :=
  execute p
                    (ctr_scale ctr)
                    (ctr_issuer ctr)
                    owner
                    (m_balance state)
                    (m_global_time state)
                    (m_gateway state)
                    (ctr_id ctr)
                    (ctr_desc_id ctr)
                    (m_fresh_id state)
                    (m_ledger state).


Definition append_new_ctr_to_state (ctr : FinContract) (state1 : State) :=
  state (ctr :: m_contracts state1)
        (m_descriptions state1)
        (m_balance state1)
        (m_global_time state1)
        (m_gateway state1)
        (S (m_fresh_id state1))
        (m_ledger state1)
        (IssuedFor (ctr_proposed_owner ctr) (ctr_id ctr) :: (m_events state1)).


Definition update_state
           (st:State)
           (ctrs : list FinContract)
           (balance : Balance)
           (next : Id)
           (ledger : list Transaction)
           (events : list Event) :=
  state ctrs (m_descriptions st) balance (m_global_time st) (m_gateway st) next ledger events.

Inductive step (state1 state2 : State) : Prop  :=
(* Issue a new contract: create a new Findel contract with the same issuer and owner. The issued contract is based on a contract description and it is now ready to be joined by the proposed owner. *)
| issue :
    forall desc_id issuer proposed_owner dsc new_contract,
      dsc = (m_descriptions state1) desc_id ->
      dsc_valid_from dsc <= m_global_time state1 <= dsc_valid_until dsc ->
      new_contract = finctr (m_fresh_id state1)
                            (dsc_id dsc) 
                            (dsc_prim dsc)
                            issuer
                            issuer
                            proposed_owner
                            (dsc_scale dsc) ->
      consistent_description dsc ->
      next_id_is_fresh state1 ->
      state2 = append_new_ctr_to_state new_contract state1 ->
      step state1 state2
(* Join a contract: an owner can join a contract only if it is the proposed owner. When a contract is joined its execution starts immediately. *)
| join :
    forall owner ctr balance' ctrs' next' ledger',
      In ctr (m_contracts state1) ->
      can_join owner ctr ->
      next_id_is_fresh state1 ->
      ~ is_or (ctr_primitive ctr) ->
      (between_time_limits ctr state1) ->
      ~ In (Executed (ctr_id ctr)) (m_events state1) ->
      exec_ctr_in_state_with_owner ctr state1 owner =
      Some (result balance' ctrs' next' ledger') ->
      state2 = update_state state1
                            ((rm ctr (m_contracts state1)) ++ ctrs')
                            balance'
                            next'
                            ledger'
                            (Executed (ctr_id ctr) :: m_events state1) ->
      step state1 state2
(* Join an Or contract: choose first *)
| or_first :
    forall owner c1 c2 ctr balance' ctrs' next' ledger',
      In ctr (m_contracts state1) ->
      can_join owner ctr ->
      next_id_is_fresh state1 ->
      ctr_primitive ctr = Or c1 c2 ->
      (between_time_limits ctr state1) ->
      ~ In (Executed (ctr_id ctr)) (m_events state1) ->
      exec_prim_ctr_in_state_with_owner c1 ctr state1 owner =
      Some (result balance' ctrs' next' ledger') ->
      state2 = update_state state1
                            ((rm ctr (m_contracts state1)) ++ ctrs')
                            balance'
                            next'
                            ledger'
                            (Executed (ctr_id ctr) :: m_events state1) ->
      step state1 state2
(* Join an Or contract: choose second *)
| or_second :
    forall owner c1 c2 ctr balance' ctrs' next' ledger',
      In ctr (m_contracts state1) ->
      can_join owner ctr ->
      next_id_is_fresh state1 ->
      ctr_primitive ctr = Or c1 c2 ->
      (between_time_limits ctr state1) ->
      ~ In (Executed (ctr_id ctr)) (m_events state1) ->
      exec_prim_ctr_in_state_with_owner c2 ctr state1 owner =
      Some (result balance' ctrs' next' ledger') ->
      state2 = update_state state1
                            ((rm ctr (m_contracts state1)) ++ ctrs')
                            balance'
                            next'
                            ledger'
                            (Executed (ctr_id ctr) :: m_events state1) ->
      step state1 state2

(* Failed contract: the execution of the contract fails when the gateway does not provide data (either it is offline or data is not fresh) or when the time is not in the time bounds; in both cases the contract is removed, the rest of the state does not change. *)
| failed :
    forall owner ctr,
      In ctr (m_contracts state1) ->
      can_join owner ctr ->
      next_id_is_fresh state1 ->
      (between_time_limits ctr state1) ->
      exec_ctr_in_state_with_owner ctr state1 owner = None ->
      state2 = update_state state1
                            (rm ctr (m_contracts state1))
                            (m_balance state1) 
                            (m_fresh_id state1)
                            (m_ledger state1)
                            (Deleted (ctr_id ctr) :: m_events state1) ->
      step state1 state2
(* Tick: the time is incremented, the gateway freshness counter inccreases as well. *)
| tick : state2 = state (m_contracts state1)
                        (m_descriptions state1)
                        (m_balance state1)
                        (S (m_global_time state1))
                        (gateway_time_update (m_gateway state1) (S (m_global_time state1)))
                        (m_fresh_id state1)
                        (m_ledger state1)
                        (m_events state1) ->
         step state1 state2.


Inductive steps (s1 s2 : State) : Prop :=
| refl : s1 = s2 -> steps s1 s2
| tran : forall s, steps s1 s -> step s s2 -> steps s1 s2. 

Notation "A ~~> B" := (steps A B) (at level 90).
