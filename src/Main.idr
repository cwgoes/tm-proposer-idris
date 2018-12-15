module Main

import Types

%access public export

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
