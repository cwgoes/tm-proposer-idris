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

-- Arithmetic laws.

congSubEq : (a, b, c : Integer) -> (a + b = c) -> (b = c - a)
congSubEq a b c prf = really_believe_me a b c prf

plusComm : (a, b : Integer) -> a + b = b + a
plusComm a b = really_believe_me a b

plusMinus : (a, b, c : Integer) -> a - b + c = a + c - b
plusMinus a b c = really_believe_me a b c

plusNeg : (a, b : Integer) -> a + (-b) = a - b
plusNeg a b = really_believe_me a b

plusMinus2Helper : (a, b, c, d : Integer) -> (((a + c) - (c + d)) - (b + d)) - (a - b) = -2 * d
plusMinus2Helper a b c d = really_believe_me a b c d

plusMinus2Helper' : (a, b, c, d : Integer) -> ((a + c) - ((b + d) - (c + d))) - (a - b) = 2 * c
plusMinus2Helper' a b c d = really_believe_me a b c d

multComm : (a, b : Integer) -> a * b = b * a
multComm a b = really_believe_me a b

multDivComm : (a, b, c : Integer) -> (a * b) `div` c = a * (b `div` c)
multDivComm a b c = really_believe_me a b c

negDistr : (a, b : Integer) -> -(a + b) = -a + -b
negDistr a b = really_believe_me a b

negSubDistr : (a, b : Integer) -> -(a - b) = b - a
negSubDistr a b = really_believe_me a b

plusAssocElim : (a, b, c : Integer) -> a - b - c + b = a - c
plusAssocElim a b c = really_believe_me a b c

mulByOne : (n : Integer) -> n * 1 = n
mulByOne n = really_believe_me n

multPlusDistr : (a, b, c : Integer) -> (a + b) * c = (a * c) + (b * c)
multPlusDistr a b c = really_believe_me a b c

divPlusDistr : (a, b, c : Integer) -> (a + b) `div` c = a `div` c + b `div` c
divPlusDistr a b c = really_believe_me a b c

divSubDistr : (a, b, c : Integer) -> (a - b) `div` c = a `div` c - b `div` c
divSubDistr a b c = really_believe_me a b c

divEq : (a : Integer) -> a `div` a = 1
divEq a = really_believe_me a

divEqNeg : (a : Integer) -> -a `div` a = -1
divEqNeg a = really_believe_me a

plusMinusSimpl : (a : Integer, b : Integer) -> a + (-b) = a - b
plusMinusSimpl a b = really_believe_me a b

multSubDistr : (a, b, c : Integer) -> a * (b - c) = (a * b) - (a * c)
multSubDistr a b c = really_believe_me a b c

multDivCancels : (a, b : Integer) -> (a * b) `div` b = a
multDivCancels a b = really_believe_me a b 

multZeroZero : (a : Integer) -> (a * 0) = 0
multZeroZero a = really_believe_me a

addZeroZero : 0 + 0 = 0
addZeroZero = really_believe_me 0

subZeroZero : 0 - 0 = 0
subZeroZero = really_believe_me 0

minusCancels : (a, b, c : Integer) -> a - (b - c) = a + c - b
minusCancels a b c = really_believe_me a b c

addSubCancels : (a, b : Integer) -> (a + b - b) = a
addSubCancels a b = really_believe_me a b

addSubCancels' : (a, b : Integer) -> (a - b + b) = a
addSubCancels' a b = really_believe_me a b

addSubSingle : (a : Integer) -> (a - a) = 0
addSubSingle a = really_believe_me a

congPlus : {a : Integer} -> {b : Integer} -> {c : Integer} -> a <= b = True -> a + c <= b + c = True
congPlus {a} {b} {c} prf = really_believe_me a b c prf

congPlus' : {a : Integer} -> {b : Integer} -> {c : Integer} -> a >= b = True -> a + c >= b + c = True
congPlus' {a} {b} {c} prf = really_believe_me a b c prf

congDiv : {a : Integer} -> {b : Integer} -> {c : Integer} -> a <= b = True -> a `div` c <= b `div` c = True
congDiv {a} {b} {c} prf = really_believe_me a b c prf

congDiv' : {a : Integer} -> {b : Integer} -> {c : Integer} -> a >= b = True -> a `div` c >= b `div` c = True
congDiv' {a} {b} {c} prf = really_believe_me a b c prf

congNegSwap : {a : Integer} -> {b : Integer} -> {c : Integer} -> (a - b) <= c = True -> (b - a) >= -c = True
congNegSwap {a} {b} {c} prf = really_believe_me a b c prf

splitAbs : {a : Integer} -> {b : Integer} -> {c: Integer} -> abs (a - b) <= c = True -> (a - b <= c = True, b - a <= c = True)
splitAbs {a} {b} {c} prf = really_believe_me a b c prf

addCommutative : (x, y : Integer) -> x + y = y + x
addCommutative x y = really_believe_me x y

excludedMiddle : p `Either` Not p
excludedMiddle {p} = really_believe_me p

excludedBool : (b : Bool) -> (b = True) `Either` (b = False)
excludedBool True   = Left Refl
excludedBool False  = Right Refl

ifEq : (a : ty) -> (b : ty) -> (cond = True) -> ((if cond then a else b) = a)
ifEq a b prf = rewrite prf in Refl

ifNeq : (a : ty) -> (b : ty) -> (cond = False) -> ((if cond then a else b) = b)
ifNeq a b prf = rewrite prf in Refl
