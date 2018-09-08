||| Propositional Logic
module PropLogic

import Data.Booleans

%access public export

||| Valuation mapping from PROP to {0,1}
valuation : (prop: Boolean) -> Nat
valuation False = 0
valuation True = 1

testValuation1 : (valuation (True /\ True)) = 1
testValuation1 = Refl
testValuation2 : (valuation (-True)) = 0
testValuation2 = Refl
