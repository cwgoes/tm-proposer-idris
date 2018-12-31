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
      snd ns = count idB (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))),
      diffPriority (fst (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))) = (2 * wB * natToInteger (fst ns)) - (2 * wA * natToInteger (snd ns))
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

  fairlyProportional : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> (n : Nat) -> -- TODO: initial inductive case
    ((natToInteger $ count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB))))) >= ((natToInteger n * (wA `div` (wA + wB))) - 1) = True,
     (natToInteger $ count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB))))) <= ((natToInteger n * (wA `div` (wA + wB))) + 1) = True)
  fairlyProportional = ?fairlyProportional

  reduceHelper : (wA, wB : ProposerWeight) -> (nA, n : Integer) ->
    ((((wB * nA) - (wA * (n - nA))) <= (wA + wB)) = True) ->
    nA <= (n * (wA `div` (wA + wB))) + 1 = True
  reduceHelper wA wB nA n lemma1 =
    lemma11
    where
      lemma2 : (((nA * wB) - ((wA * n) - (wA * nA))) <= (wA + wB)) = True
      lemma2 =
        rewrite multComm nA wB in
        rewrite sym (multSubDistr wA n nA) in
        lemma1

      lemma3 : (((nA * wB) + (nA * wA) - (wA * n)) <= (wA + wB)) = True
      lemma3 =
        rewrite multComm nA wA in
        rewrite (sym (minusCancels (nA * wB) (wA * n) (wA * nA))) in
        lemma2

      lemma4 : (((wB + wA) * nA - (wA * n)) <= (wA + wB)) = True
      lemma4 =
        rewrite (multPlusDistr wB wA nA) in
        rewrite multComm wA nA in
        rewrite multComm wB nA in
        lemma3

      lemma5 : (((wB + wA) * nA + (wA * n) - (wA * n)) <= (wA + wB) + (wA * n)) = True
      lemma5 =
        rewrite (sym (plusMinus ((wB + wA) * nA) (wA * n) (wA * n))) in
        congPlus lemma4

      lemma6 : (((wB + wA) * nA) <= (wA + wB) + (wA * n)) = True
      lemma6 =
        rewrite (sym (addSubCancels ((wB + wA) * nA) (wA * n))) in
        lemma5

      lemma7 : (((wA + wB) * nA) <= (wA + wB) + (wA * n)) = True
      lemma7 = replace {P = \x => x * nA <= (wA + wB) + (wA * n) = True} (plusComm wB wA) lemma6

      lemma8 : ((nA * (wA + wB)) <= (wA + wB) + (wA * n)) = True
      lemma8 = rewrite multComm nA (wA + wB) in lemma7

      lemma9 : ((nA * (wA + wB) `div` (wA + wB)) <= ((wA + wB) + (wA * n)) `div` (wA + wB)) = True
      lemma9 = congDiv lemma8

      lemma10 : nA <= (((wA + wB) + (wA * n)) `div` (wA + wB)) = True
      lemma10 = rewrite (sym (multDivCancels nA (wA + wB))) in lemma9

      lemma11 : nA <= (n * (wA `div` (wA + wB))) + 1 = True
      lemma11 =
        rewrite plusComm (n * (wA `div` (wA + wB))) 1 in
        rewrite (sym (multDivComm n wA (wA + wB))) in
        rewrite multComm n wA in
        rewrite (sym (divEq (wA + wB))) in
        rewrite (sym (divPlusDistr (wA + wB) (wA * n) (wA + wB))) in
        lemma10

  reduceInequality : (wA, wB : ProposerWeight) -> (nA, nB, n : Integer) ->
    (nA + nB = n) ->
    ((abs ((wB * nA) - (wA * nB)) <= (wA + wB)) = True) ->
    (nA >= (n * (wA `div` (wA + wB))) - 1 = True,
     nA <= (n * (wA `div` (wA + wB))) + 1 = True)
  reduceInequality wA wB nA nB n neq abslt =
    (first, second)

    where lteqA : ((wB * nA) - (wA * nB)) <= (wA + wB) = True
          lteqA = fst (splitAbs abslt)

          lteqB : ((wA * nB) - (wB * nA)) <= (wA + wB) = True
          lteqB = snd (splitAbs abslt)

          initialForA : (((wB * nA) - (wA * (n - nA))) <= (wA + wB)) = True
          initialForA =
            rewrite (sym (congSubEq nA nB n neq)) in
            lteqA

          initialForB : (((wA * nB) - (wB * (n - nB))) <= (wB + wA)) = True
          initialForB =
            rewrite plusComm wB wA in
            rewrite (sym (congSubEq nB nA n (rewrite plusComm nB nA in neq))) in
            lteqB

          finalForB : nB <= (n * (wB `div` (wB + wA))) + 1 = True
          finalForB = reduceHelper wB wA nB n initialForB

          lemma1 : n - nA <= (n * (wB `div` (wB + wA))) + 1 = True
          lemma1 = rewrite (sym (congSubEq nA nB n neq)) in finalForB

          lemma2 : nA - n >= -((n * (wB `div` (wB + wA))) + 1) = True
          lemma2 = congNegSwap lemma1

          lemma3 : nA >= -((n * (wB `div` (wB + wA))) + 1) + n = True
          lemma3 = rewrite (sym (addSubCancels' nA n)) in congPlus' lemma2

          lemma4 : nA >= -((n * ((wB + wA - wA) `div` (wB + wA))) + 1) + n = True
          lemma4 = rewrite addSubCancels wB wA in lemma3

          lemma5 : nA >= -((n * ((wB + wA) `div` (wB + wA) - (wA `div` (wB + wA)))) + 1) + n = True
          lemma5 = rewrite (sym (divSubDistr (wB + wA) wA (wB + wA))) in lemma4

          lemma6 : nA >= -((n * (1 - (wA `div` (wB + wA)))) + 1) + n = True
          lemma6 = replace {P = \x => nA >= -((n * (x - (wA `div` (wB + wA)))) + 1) + n = True} (divEq (wB + wA)) lemma5

          lemma7 : nA >= -(n * (1 - (wA `div` (wB + wA)))) + (-1) + n = True
          lemma7 =
            rewrite (sym (negDistr (n * (1 - (wA `div` (wB + wA)))) 1)) in lemma6

          lemma8 : nA >= -((n * 1) - (n * (wA `div` (wB + wA)))) + (-1) + n = True
          lemma8 =
            rewrite (sym (multSubDistr n 1 (wA `div` (wB + wA)))) in
            lemma7

          lemma9 : nA >= -(n - (n * (wA `div` (wB + wA)))) + (-1) + n = True
          lemma9 = replace {P = \x => nA >= -(x - (n * (wA `div` (wB + wA)))) + (-1) + n = True} (mulByOne n) lemma8

          lemma10 : nA >= (n * (wA `div` (wB + wA))) - n - 1 + n = True
          lemma10 =
            rewrite (sym (plusNeg ((n * (wA `div` (wB + wA))) - n) 1)) in
            rewrite (sym (negSubDistr n (n * (wA `div` (wB + wA))))) in lemma9

          lemma11 : nA >= (n * (wA `div` (wB + wA))) - 1 = True
          lemma11 = rewrite (sym (plusAssocElim (n * (wA `div` (wB + wA))) n 1)) in lemma10

          first : nA >= (n * (wA `div` (wA + wB))) - 1 = True
          first = rewrite (plusComm wA wB) in lemma11

          second : nA <= (n * (wA `div` (wA + wB))) + 1 = True
          second = reduceHelper wA wB nA n initialForA

{- TODO n-validator case, preferably just via an equivalence proof from the 2-validator case. -}
