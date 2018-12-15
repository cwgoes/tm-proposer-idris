module Types

import public Builtins
import public Prelude.Nat
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

ElectionState : Type
ElectionState = List (ProposerId, ProposerWeight, ProposerPriority)

-- Helpers

fst3 : (a, b, c) -> a
fst3 (a, _, _) = a

snd3 : (a, b, c) -> b
snd3 (_, b, _) = b

thd3 : (a, b, c) -> c
thd3 (_, _, c) = c

totalWeight : ElectionState -> Int
totalWeight s = sum (map snd3 s)
