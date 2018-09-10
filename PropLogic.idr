||| Propositional Logic
module PropLogic

import Data.Booleans

%access public export

||| Valuation mapping from PROP to {0,1}
||| @prop any proposition from the set of all valid propositions
valuation : (prop: Boolean) -> Nat
valuation F = 0
valuation T = 1

testValuation1 : (valuation (T /\ T)) = 1
testValuation1 = Refl
testValuation2 : (valuation (~T)) = 0
testValuation2 = Refl
