module Main

import Types

%access public export

namespace TwoValidator

  ElectionState : Type
  ElectionState = ((ProposerId, ProposerWeight, ProposerPriority), (ProposerId, ProposerWeight, ProposerPriority))

  incrementElect : ElectionState -> (ElectionState, ProposerId)
  incrementElect ((aId, aWeight, aPriority), (bId, bWeight, bPriority)) =
    let newPriorityA = aPriority + aWeight
        newPriorityB = bPriority + bWeight
        totalWeight  = aWeight + bWeight
    in if newPriorityA >= newPriorityB then
         (((aId, aWeight, newPriorityA - totalWeight), (bId, bWeight, newPriorityB)), aId)
       else
         (((aId, aWeight, newPriorityA), (bId, bWeight, newPriorityB - totalWeight)), bId)

  incrementElectMany : (n : Nat) -> (s : ElectionState) -> (ElectionState, List ProposerId)
  incrementElectMany Z      state = (state, [])
  incrementElectMany (S k)  state =
    let (newState, result)    = incrementElect state
        (finalState, results) = incrementElectMany k newState
    in (finalState, result :: results)

  diffPositive : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB : ProposerPriority) -> (prf : (pA + wA) >= (pB + wB) = True) -> snd (incrementElect ((idA, wA, pA), (idB, wB, pB))) = idA
  diffPositive idA idB wA wB pA pB prf =
    rewrite (ifEq
      (((idA, wA, (pA + wA) - (wA + wB)), (idB, wB, (pB + wB))), idA)
      (((idA, wA, (pA + wA)), (idB, wB, (pB + wB) - (wA + wB))), idB)
      prf) in
    Refl

{- TODO n-validator case -}

{-

namespace ManyValidator

  incrementElect : ElectionState -> (ElectionState, ProposerId)
  incrementElect state =
    let updated = map (\(index, weight, priority) => (index, weight, priority + weight)) state
        sorted      = updated -- TODO
        proposer    = head { ok = sortedNonEmpty } sorted
    in (alterPriority (totalWeight state) proposer :: tail { ok = sortedNonEmpty } sorted, fst3 proposer)

    where
      sortedNonEmpty : NonEmpty sorted
      sortedNonEmpty = ?sortedNonEmpty

      alterPriority : Int -> (ProposerId, ProposerWeight, ProposerPriority) -> (ProposerId, ProposerWeight, ProposerPriority)
      alterPriority diff (id, weight, priority) = (id, weight, priority - diff)

  incrementElectMany : (n : Nat) -> (s : ElectionState) -> (ElectionState, List ProposerId)
  incrementElectMany Z      state = (state, [])
  incrementElectMany (S n)  state =
    let (newState, result)    = incrementElect state
        (finalState, results) = incrementElectMany n newState
    in (finalState, result :: results)

-}
