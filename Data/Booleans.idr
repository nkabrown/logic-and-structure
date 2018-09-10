||| Boolean data type
module Booleans

%access public export

data Boolean = F | T

||| Logical connective conjunction (and)
conjunction : (b1 : Boolean) -> (b2 : Boolean) -> Boolean
conjunction T b2 = b2
conjunction F b2 = F

infixl 4 /\
(/\) : Boolean -> Boolean -> Boolean
(/\) = conjunction

testConjunction1 : (conjunction T T) = T
testConjunction1 = Refl
testConjunction2 : (conjunction F T) = F
testConjunction2 = Refl
testConjunction3 : (conjunction T F) = F
testConjunction3 = Refl
testConjunction4 : (conjunction F F) = F
testConjunction4 = Refl
testConjunction5 : (T /\ T) = T
testConjunction5 = Refl

||| Logical connective disjunction (or)
disjunction : (b1 : Boolean) -> (b2 : Boolean) -> Boolean
disjunction T b2 = T
disjunction F b2 = b2

infixl 4 \/
(\/) : Boolean -> Boolean -> Boolean
(\/) = disjunction

testDisjunction1 : (disjunction T T) = T
testDisjunction1 = Refl
testDisjunction2 : (disjunction F T) = T
testDisjunction2 = Refl
testDisjunction3 : (disjunction T F) = T
testDisjunction3 = Refl
testDisjunction4 : (disjunction F F) = F
testDisjunction4 = Refl
testDisjunction5 : (F \/ F \/ T) = T
testDisjunction5 = Refl

||| Logical connective negation (not)
negation : (b : Boolean) -> Boolean
negation T = F
negation F = T

syntax "~" [b] = negation b

testNegation1 : (negation T) = F
testNegation1 = Refl
testNegation2 : (negation F) = T
testNegation2 = Refl

||| Logical connective implication (if...,then...)
implication : (b1 : Boolean) -> (b2 : Boolean) -> Boolean
implication T b2 = b2
implication F b2 = T

infix 4 +>
(+>) : Boolean -> Boolean -> Boolean
(+>) = implication

testImplication1 : (implication T T) = T
testImplication1 = Refl
testImplication2 : (implication F T) = T
testImplication2 = Refl
testImplication3 : (implication T F) = F
testImplication3 = Refl
testImplication4 : (implication F F) = T
testImplication4 = Refl
testImplication5 : (T +> F) = F
testImplication5 = Refl

||| Logical connective equivalence (iff)
equivalence : (b1 : Boolean) -> (b2 : Boolean) -> Boolean
equivalence T b2 = b2
equivalence F b2 = negation b2

infix 4 <>
(<>) : Boolean -> Boolean -> Boolean
(<>) = equivalence

testEquivalence1 : (equivalence T T) = T
testEquivalence1 = Refl
testEquivalence2 : (equivalence F T) = F
testEquivalence2 = Refl
testEquivalence3 : (equivalence T F) = F
testEquivalence3 = Refl
testEquivalence4 : (equivalence F F) = T
testEquivalence4 = Refl
testEquivalence5 : (F <> F) = T
testEquivalence5 = Refl
