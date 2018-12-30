module Main

import Types

%access public export

namespace TwoValidator

  ElectionState : Type
  ElectionState = ((ProposerId, ProposerWeight, ProposerPriority), (ProposerId, ProposerWeight, ProposerPriority))

  diffPriority : ElectionState -> ProposerPriority
  diffPriority ((_, _, a), (_, _, b)) = a - b

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
    (pA : ProposerPriority) -> (pB : ProposerPriority) -> (prf : (pA + wA) >= (pB + wB) = True) ->
    ((incrementElect ((idA, wA, pA), (idB, wB, pB))) = (((idA, wA, (pA + wA) - (wA + wB)), (idB, wB, (pB + wB))), idA))
  diffPositive idA idB wA wB pA pB prf =
    rewrite (ifEq
      (((idA, wA, (pA + wA) - (wA + wB)), (idB, wB, (pB + wB))), idA)
      (((idA, wA, (pA + wA)), (idB, wB, (pB + wB) - (wA + wB))), idB)
      prf) in
    Refl

  diffNegative : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> (prf : (pA + wA) >= (pB + wB) = False) ->
    ((incrementElect ((idA, wA, pA), (idB, wB, pB))) = (((idA, wA, (pA + wA)), (idB, wB, (pB + wB) - (wA + wB))), idB))
  diffNegative idA idB wA wB pA pB prf =
    rewrite (ifNeq
      (((idA, wA, (pA + wA) - (wA + wB)), (idB, wB, (pB + wB))), idA)
      (((idA, wA, (pA + wA)), (idB, wB, (pB + wB) - (wA + wB))), idB)
      prf) in
    Refl

  EqEither : (a : t) -> (b : t) -> (c : t) -> Type
  EqEither a b c = (a = b) `Either` (a = c)

  resultEither : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> EqEither (incrementElect ((idA, wA, pA), (idB, wB, pB)))
    (((idA, wA, (pA + wA) - (wA + wB)), (idB, wB, (pB + wB))), idA) (((idA, wA, (pA + wA)), (idB, wB, (pB + wB) - (wA + wB))), idB)
  resultEither idA idB wA wB pA pB =
    case excludedBool ((pA + wA) >= (pB + wB)) of
      Left prf  => Left $ diffPositive idA idB wA wB pA pB prf
      Right prf => Right $ diffNegative idA idB wA wB pA pB prf

  diffChange : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) ->
    (diffPriority (fst (incrementElect ((idA, wA, pA), (idB, wB, pB)))) = 2 * wB, snd (incrementElect ((idA, wA, pA), (idB, wB, pB))) = idA) `Either`
    (diffPriority (fst (incrementElect ((idA, wA, pA), (idB, wB, pB)))) = -2 * wA, snd (incrementElect ((idA, wA, pA), (idB, wB, pB))) = idB)
  diffChange = ?diffChange

  -- Prove: exact change in diff (2 * pA | 2 * pB)

  totalDiff : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> (n: Nat) ->
    (ns ** (n = fst ns + snd ns,
      fst ns = count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))),
      snd ns = count idB (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB))))
      --diffPriority (fst (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))) = (2 * wB * fst ns) - (2 * wA * snd ns)
      ))
  totalDiff idA idB wA wB pA pB n = ?totalDiff

  -- Prove: total diff over n calls, total diff = 2 wB nA - 2 wA nB

  diffDiff : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> (abs (pA - pB) <= (2*wA + 2*wB) = True)
    -> (abs (diffPriority (fst (incrementElect ((idA, wA, pA), (idB, wB, pB))))) <= (2*wA + 2*wB) = True)
  diffDiff = ?diffDiff

  -- Prove: maximum bound on diff in incrementElectMany calls by induction

  diffDiffMany : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> (n : Nat) -> (abs (pA - pB) <= (2*wA + 2*wB) = True)
    -> (abs (diffPriority (fst (incrementElectMany n ((idA, wA, pA), (idB, wB, pB))))) <= (2*wA + 2*wB) = True)
  diffDiffMany = ?diffDiffMany

  final : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> (n : Nat) -> -- TODO: initial inductive case
    ((natToInteger $ count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB))))) >= ((natToInteger n * wA `div` (wB + wA)) `minusInt` 1) = True,
     (natToInteger $ count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB))))) <= ((natToInteger n * wA `div` (wB + wA)) `plusInt` 1) = True)
  final = ?final

  reduceInequality : (wA, wB : ProposerWeight) -> (nA, nB, n : Integer) ->
    (nA + nB = n) ->
    ((((wB * nA) - (wA * nB)) <= (wA + wB)) = True) ->
    (nA >= n * (wA `div` (wB + wA)) - 1 = True,
     nA <= n * (wA `div` (wB + wA)) + 1 = True)
  reduceInequality wA wB nA nB n neq lteq =
    ?reduceInequality

    where stepOne : (((wB * nA) - (wA * (n - nA))) <= (wA + wB)) = True
          stepOne =
            rewrite (sym (congSubEq nA nB n neq)) in
            lteq

          stepTwo : (((nA * wB) - ((wA * n) - (wA * nA))) <= (wA + wB)) = True
          stepTwo =
            rewrite multComm nA wB in
            rewrite sym (multSubDistr wA n nA) in
            stepOne

          stepThree : (((nA * wB) + (nA * wA) - (wA * n)) <= (wA + wB)) = True
          stepThree =
            rewrite multComm nA wA in
            rewrite (sym (minusCancels (nA * wB) (wA * n) (wA * nA))) in
            stepTwo

          stepFour : (((wB + wA) * nA - (wA * n)) <= (wA + wB)) = True
          stepFour =
            rewrite (multPlusDistr wB wA nA) in
            rewrite multComm wA nA in
            rewrite multComm wB nA in
            stepThree

          stepFive : (((wB + wA) * nA + (wA * n) - (wA * n)) <= (wA + wB) + (wA * n)) = True
          stepFive =
            rewrite (sym (plusMinus ((wB + wA) * nA) (wA * n) (wA * n))) in
            congPlus stepFour

          stepSix : (((wB + wA) * nA) <= (wA + wB) + (wA * n)) = True
          stepSix =
            rewrite (sym (addSubCancels ((wB + wA) * nA) (wA * n))) in
            stepFive

          stepSeven : (((wA + wB) * nA) <= (wA + wB) + (wA * n)) = True
          stepSeven = replace {P = \x => x * nA <= (wA + wB) + (wA * n) = True} (plusComm wB wA) stepSix

          stepEight : ((nA * (wA + wB)) <= (wA + wB) + (wA * n)) = True
          stepEight = rewrite multComm nA (wA + wB) in stepSeven

          stepNine : ((nA * (wA + wB) `div` (wA + wB)) <= ((wA + wB) + (wA * n)) `div` (wA + wB)) = True
          stepNine = congDiv stepEight

          stepTen : nA <= (((wA + wB) + (wA * n)) `div` (wA + wB)) = True
          stepTen = rewrite (sym (multDivCancels nA (wA + wB))) in stepNine

          stepEleven : nA <= (n * (wA `div` (wA + wB))) + 1 = True
          stepEleven =
            rewrite plusComm (n * (wA `div` (wA + wB))) 1 in
            rewrite (sym (multDivComm n wA (wA + wB))) in
            rewrite multComm n wA in
            rewrite (sym (divEq (wA + wB))) in
            rewrite (sym (divPlusDistr (wA + wB) (wA * n) (wA + wB))) in
            stepTen

  -- Then: abs (2 * wB * nA) - (2 * wA * nB) <= 2*wA + 2*wB
  -- wB * nA - wA * nB <= wA + wB
  -- wB * nA - wA * (n - nA) <= wA + wB
  -- wB * (nA / n) - wA * (1 - nA/n) <= wA + wB / n
  -- (wB + wA) (nA / n) <= (wA + wB) / n + wA
  -- nA / n <= 1 / n + (wA / (wB + wA))
  -- and similarly, nB / n <= 1 / n + (wB / (wB + wA))
  -- thus (n - nA) / n <= 1 / n + (wB / (wB + wA))
  -- nA / n - 1 >= - (1 / n + (wB / (wB + wA)))
  -- nA / n >= 1 - 1/n - (wB / (wB + wA))
  -- 1 - 1/n - (wB / (wB + wA)) <= nA / n <= 1 / n + (wA / (wB + wA))
  -- (wA / (wB + wA)) - 1/n <= nA / n <= (wA / (wB + wA)) + 1/n
  -- QED

{- TODO n-validator case, preferably just via an equivalence proof from the 2-validator case. -}
