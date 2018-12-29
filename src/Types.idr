module Types

import public Builtins
import public Prelude.Cast
import public Prelude.Basics
import public Prelude.Either
import public Prelude.Nat
import public Prelude.Bool
import public Prelude.List
import public Prelude.Functor
import public Prelude.Foldable
import public Prelude.Interfaces

%access public export

-- Types

ProposerId : Type
ProposerId = Integer

ProposerWeight : Type
ProposerWeight = Integer

ProposerPriority : Type
ProposerPriority = Integer

-- Helpers

fst3 : (a, b, c) -> a
fst3 (a, _, _) = a

snd3 : (a, b, c) -> b
snd3 (_, b, _) = b

thd3 : (a, b, c) -> c
thd3 (_, _, c) = c

count : (n : Integer) -> (l : List Integer) -> Nat
count n [] = 0
count n (x :: xs) = (if n == x then 1 else 0) + count n xs

natToInteger : Nat -> Integer
natToInteger Z = 0
natToInteger (S k) = 1 + natToInteger k

minusInt : Integer -> Integer -> Integer
minusInt x y = x - y

plusInt : Integer -> Integer -> Integer
plusInt x y = x + y

divInt : Integer -> Integer -> Integer
divInt = ?divInt

data GTEI : (n : Int) -> (m : Int) -> Type where
  GTEImpl : (n >= m = True) -> GTEI n m

addCommutative : (x, y : Integer) -> x + y = y + x
addCommutative x y = really_believe_me x y

gteTransitive : {n : Int} -> {m : Int} -> {p: Int} -> (n >= m = True) -> (p >= n = True) -> (p >= m = True)
gteTransitive ngtem pgten = really_believe_me ngtem pgten

excludedMiddle : p `Either` Not p
excludedMiddle {p} = really_believe_me p

excludedBool : (b : Bool) -> (b = True) `Either` (b = False)
excludedBool True   = Left Refl
excludedBool False  = Right Refl

ifEq : (a : ty) -> (b : ty) -> (cond = True) -> ((if cond then a else b) = a)
ifEq a b prf = rewrite prf in Refl

ifNeq : (a : ty) -> (b : ty) -> (cond = False) -> ((if cond then a else b) = b)
ifNeq a b prf = rewrite prf in Refl
