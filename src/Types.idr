module Types

import public Builtins
import public Prelude.Nat
import public Prelude.Bool
import public Prelude.List
import public Prelude.Functor
import public Prelude.Foldable
import public Prelude.Interfaces

%access public export

-- Types

ProposerId : Type
ProposerId = Int

ProposerWeight : Type
ProposerWeight = Int

ProposerPriority : Type
ProposerPriority = Int

-- Helpers

fst : (a, b) -> a
fst (a, _) = a

snd : (a, b) -> b
snd (_, b) = b

fst3 : (a, b, c) -> a
fst3 (a, _, _) = a

snd3 : (a, b, c) -> b
snd3 (_, b, _) = b

thd3 : (a, b, c) -> c
thd3 (_, _, c) = c

data GTEInt : (n : Int) -> (m : Int) -> Type where
  GTEImpl : (n >= m = True) -> GTEInt n m

ifEq : (a : ty) -> (b : ty) -> (cond = True) -> ((if cond then a else b) = a)
ifEq a b prf = rewrite prf in Refl
