||| Propositional Logic
module PropLogic

%access public export

namespace Booleans
  ||| Boolean data type
  data Bool = True | False

  ||| Logical connective conjunction (and)
  conjunction : (b1 : Bool) -> (b2 : Bool) -> Bool
  conjunction True b2 = b2
  conjunction False b2 = False

  infixl 4 /\
  (/\) : Bool -> Bool -> Bool
  (/\) = conjunction

  testConjunction1 : (conjunction True True) = True
  testConjunction1 = Refl
  testConjunction2 : (conjunction False True) = False
  testConjunction2 = Refl
  testConjunction3 : (conjunction True False) = False
  testConjunction3 = Refl
  testConjunction4 : (conjunction False False) = False
  testConjunction4 = Refl
  testConjunction5 : (True /\ True) = True
  testConjunction5 = Refl

  ||| Logical connective disjunction (or)
  disjunction : (b1 : Bool) -> (b2 : Bool) -> Bool
  disjunction True b2 = True
  disjunction False b2 = b2

  infixl 4 \/
  (\/) : Bool -> Bool -> Bool
  (\/) = disjunction

  testDisjunction1 : (disjunction True True) = True
  testDisjunction1 = Refl
  testDisjunction2 : (disjunction False True) = True
  testDisjunction2 = Refl
  testDisjunction3 : (disjunction True False) = True
  testDisjunction3 = Refl
  testDisjunction4 : (disjunction False False) = False
  testDisjunction4 = Refl
  testDisjunction5 : (False \/ False \/ True) = True
  testDisjunction5 = Refl

  ||| Logical connective negation (not)
  negation : (b : Bool) -> Bool
  negation True = False
  negation False = True

  prefix 5 -
  (-) : Bool -> Bool
  (-) = negation

  testNegation1 : (negation True) = False
  testNegation1 = Refl
  testNegation2 : (negation False) = True
  testNegation2 = Refl
  testNegation3 : (-True) = False
  testNegation3 = Refl

  ||| Logical connective implication (if...,then...)
  implication : (b1 : Bool) -> (b2 : Bool) -> Bool
  implication True b2 = b2
  implication False b2 = True

  infix 4 +>
  (+>) : Bool -> Bool -> Bool
  (+>) = implication

  testImplication1 : (implication True True) = True
  testImplication1 = Refl
  testImplication2 : (implication False True) = True
  testImplication2 = Refl
  testImplication3 : (implication True False) = False
  testImplication3 = Refl
  testImplication4 : (implication False False) = True
  testImplication4 = Refl
  testImplication5 : (True +> False) = False
  testImplication5 = Refl

  ||| Logical connective equivalence (iff)
  equivalence : (b1 : Bool) -> (b2 : Bool) -> Bool
  equivalence True b2 = b2
  equivalence False b2 = negation b2

  infix 4 <>
  (<>) : Bool -> Bool -> Bool
  (<>) = equivalence

  testEquivalence1 : (equivalence True True) = True
  testEquivalence1 = Refl
  testEquivalence2 : (equivalence False True) = False
  testEquivalence2 = Refl
  testEquivalence3 : (equivalence True False) = False
  testEquivalence3 = Refl
  testEquivalence4 : (equivalence False False) = True
  testEquivalence4 = Refl
  testEquivalence5 : (False <> False) = True
  testEquivalence5 = Refl
