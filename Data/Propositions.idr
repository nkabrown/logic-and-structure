||| Proposition data type
module Propositions

import Data.Booleans

%access public export

||| Inductively define set of all propositions (PROP)
data Prop = AtomicExp Boolean
          | AndExp Prop Prop
          | OrExp Prop Prop
          | NegExp Prop
          | IfExp Prop Prop
          | IffExp Prop Prop

||| Formation sequence of PROP
eval : Prop -> Boolean
eval (AtomicExp b)  = b
eval (AndExp e1 e2) = conjunction (eval e1) (eval e2)
eval (OrExp e1 e2)  = disjunction (eval e1) (eval e2)
eval (NegExp e)     = negation (eval e)
eval (IfExp e1 e2)  = implication (eval e1) (eval e2)
eval (IffExp e1 e2) = equivalence (eval e1) (eval e2)

Truth : Prop
Truth = AtomicExp T

Falsity : Prop
Falsity = AtomicExp F

infixl 4 /\
(/\) : Prop -> Prop -> Prop
(/\) e1 e2 = AndExp e1 e2

infixl 4 \/
(\/) : Prop -> Prop -> Prop
(\/) e1 e2 = OrExp e1 e2 

infix 4 +>
(+>) : Prop -> Prop -> Prop
(+>) e1 e2 = IfExp e1 e2

infix 4 <>
(<>) : Prop -> Prop -> Prop
(<>) e1 e2 = IffExp e1 e2

neg : Prop -> Prop
neg = NegExp
