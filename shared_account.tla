--------------------------- MODULE shared_account ---------------------------
EXTENDS Integers, Naturals
CONSTANTS OpeningBalance, AccountHolders

ASSUME OpeningBalance > 0
ASSUME AccountHolders /= {}

(*--algorithm shared_account
variables
  opening_balance \in 1..OpeningBalance,
  balance = opening_balance;

define
  AccountBalanceInvariant == balance >= 0
end define;

process account_holder \in AccountHolders
variable tx_amount \in 1..balance
begin
  SpendMoney:
    while TRUE do
      await balance >= tx_amount;
      balance := balance - tx_amount;
    end while;
end process;

process paycheck = "paycheck"
begin
  GetPaid:
    balance := OpeningBalance;
    goto GetPaid;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES opening_balance, balance, pc

(* define statement *)
AccountBalanceInvariant == balance >= 0

VARIABLE tx_amount

vars == << opening_balance, balance, pc, tx_amount >>

ProcSet == (AccountHolders) \cup {"paycheck"}

Init == (* Global variables *)
        /\ opening_balance \in 1..OpeningBalance
        /\ balance = opening_balance
        (* Process account_holder *)
        /\ tx_amount \in [AccountHolders -> 1..balance]
        /\ pc = [self \in ProcSet |-> CASE self \in AccountHolders -> "SpendMoney"
                                        [] self = "paycheck" -> "GetPaid"]

SpendMoney(self) == /\ pc[self] = "SpendMoney"
                    /\ balance >= tx_amount[self]
                    /\ balance' = balance - tx_amount[self]
                    /\ pc' = [pc EXCEPT ![self] = "SpendMoney"]
                    /\ UNCHANGED << opening_balance, tx_amount >>

account_holder(self) == SpendMoney(self)

GetPaid == /\ pc["paycheck"] = "GetPaid"
           /\ balance' = OpeningBalance
           /\ pc' = [pc EXCEPT !["paycheck"] = "GetPaid"]
           /\ UNCHANGED << opening_balance, tx_amount >>

paycheck == GetPaid

Next == paycheck
           \/ (\E self \in AccountHolders: account_holder(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
    

=============================================================================
\* Modification History
\* Last modified Sun Apr 07 09:48:17 CDT 2019 by jeremy
\* Created Sun Apr 07 08:27:56 CDT 2019 by jeremy
