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
    let (previousState, results) = incrementElectMany k state
        (newState, result) = incrementElect previousState
    in (newState, result :: results)

  incrementElectManyApplies : (n : Nat) -> (s : ElectionState) ->
    (fst (incrementElectMany (S n) s) =
    fst (incrementElect (fst (incrementElectMany n s))))
  incrementElectManyApplies n s = ?incrementElectManyApplies

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
    (diffPriority (fst (incrementElect ((idA, wA, pA), (idB, wB, pB)))) - diffPriority ((idA, wA, pA), (idB, wB, pB)) = -2 * wB, snd (incrementElect ((idA, wA, pA), (idB, wB, pB))) = idA) `Either`
    (diffPriority (fst (incrementElect ((idA, wA, pA), (idB, wB, pB)))) - diffPriority ((idA, wA, pA), (idB, wB, pB)) = 2 * wA, snd (incrementElect ((idA, wA, pA), (idB, wB, pB))) = idB)
  diffChange idA idB wA wB pA pB = case resultEither idA idB wA wB pA pB of
    Left prf  => rewrite prf in Left (rewrite (sym (plusMinus2Helper pA pB wA wB)) in Refl, Refl)
    Right prf => rewrite prf in Right (rewrite (sym (plusMinus2Helper' pA pB wA wB)) in Refl, Refl)

  -- Prove the total change in priority difference over n calls of incrementElect.
  totalDiff : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> (n: Nat) ->
    (ns ** (n = fst ns + snd ns,
      fst ns = count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))),
      snd ns = count idB (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))),
      diffPriority (fst (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))) - diffPriority ((idA, wA, pA), (idB, wB, pB)) = (2 * wA * natToInteger (snd ns)) - (2 * wB * natToInteger (fst ns))
      ))
  totalDiff idA idB wA wB pA pB Z = ((0, 0) ** (Refl, Refl, Refl,
    replace {P = \x => diffPriority (fst (incrementElectMany 0 ((idA, wA, pA), (idB, wB, pB)))) - diffPriority ((idA, wA, pA), (idB, wB, pB)) = x}
      (sym zeroEqwAwB) diffEqZero))
    where
      zeroEqwAwB : (2 * wA * 0) - (2 * wB * 0) = 0
      zeroEqwAwB =
        rewrite multZeroZero (2 * wA) in
        rewrite multZeroZero (2 * wB) in
        Refl

      diffEqZero : diffPriority (fst (incrementElectMany 0 ((idA, wA, pA), (idB, wB, pB)))) - diffPriority ((idA, wA, pA), (idB, wB, pB)) = 0
      diffEqZero =
        rewrite (addSubSingle (pA - pB)) in
        Refl
  totalDiff idA idB wA wB pA pB (S k) =
    let ((idA', wA', pA'), (idB', wB', pB')) = previousState
        ((nA, nB) ** (eq, cA, cB, diffEq)) = previous in
    case diffChange idA' idB' wA' wB' pA' pB' of
      Left prfA => (
        ((nA + 1, nB)) **
        (rewrite plusCommutative (nA + 1) nB in rewrite plusCommutative nA 1 in rewrite eq in rewrite plusCommutative nA nB in rewrite plusSuccRightSucc nB nA in Refl,
         ?totalDiffLeft3,
         ?totalDiffLeft2,
         ?totalDiffLeft
        ))
      Right prfB => (
        ((nA, nB + 1)) **
        (rewrite plusCommutative nA (nB + 1) in rewrite plusCommutative nB 1 in rewrite eq in rewrite plusCommutative nA nB in Refl,
          ?totalDiffRight3,
          ?totalDiffRight2,
          ?totalDiffRight
        ))
    where
      previousState : ElectionState
      previousState = fst (incrementElectMany k ((idA, wA, pA), (idB, wB, pB)))

      previous : (ns ** (k = fst ns + snd ns,
        fst ns = count idA (snd (incrementElectMany k ((idA, wA, pA), (idB, wB, pB)))),
        snd ns = count idB (snd (incrementElectMany k ((idA, wA, pA), (idB, wB, pB)))),
        diffPriority (fst (incrementElectMany k ((idA, wA, pA), (idB, wB, pB)))) - diffPriority ((idA, wA, pA), (idB, wB, pB)) = (2 * wA * natToInteger (snd ns)) - (2 * wB * natToInteger (fst ns))
          ))
      previous = totalDiff idA idB wA wB pA pB k

  -- Prove: total diff over n calls, total diff = 2 wB nA - 2 wA nB

  diffDiff : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> (abs (pA - pB) <= (2*wA + 2*wB) = True)
    -> (abs (diffPriority (fst (incrementElect ((idA, wA, pA), (idB, wB, pB))))) <= (2*wA + 2*wB) = True)
  diffDiff idA idB wA wB pA pB prf =
    case excludedBool ((pA + wA) >= (pB + wB)) of
      Left prf' =>
        rewrite leftCase prf' in
        rewrite leftFinal in
        Refl
      Right prf' =>
        rewrite rightCase prf' in
        rewrite rightFinal in
        Refl

  where
    helper1 : ((pA + wA) >= (pB + wB)) = True -> (pA - pB) >= (wB - wA) = True
    helper1 = ?helper1

    leftCase : ((pA + wA) >= (pB + wB) = True) -> diffPriority (fst (incrementElect ((idA, wA, pA), (idB, wB, pB)))) = (pA - pB - 2 * wB)
    leftCase = ?leftCase

    -- abs (x - y) <= z
    -- >> -z < x - y < z

    -- >> want to prove : -2 wA < (pA - pB) < 2 wA + 4 wB
    -- can prove upper bound by abs
    -- lower bound: have: pA - pB >= wB - wA >> pA - pB >= -wA

    leftLowerBound : (pA - pB - 2 * wB) >= -(2 * wA + 2 * wB) = True
    leftLowerBound = ?leftLowerBound

    leftUpperBound : (pA - pB - 2 * wB) <= (2 * wA + 2 * wB) = True
    leftUpperBound = ?leftUpperBound

    leftFinal : abs (pA - pB - 2 * wB) <= (2 * wA + 2 * wB) = True
    leftFinal = joinAbs (leftLowerBound, leftUpperBound)

    rightCase : ((pA + wA) >= (pB + wB) = False) -> diffPriority (fst (incrementElect ((idA, wA, pA), (idB, wB, pB)))) = (pA - pB + 2 * wA)
    rightCase = ?rightCase

    rightLowerBound : (pA - pB + 2 * wA) >= -(2 * wA + 2 * wB) = True
    rightLowerBound = ?rightLowerBound

    rightUpperBound : (pA - pB + 2 * wA) <= (2 * wA + 2 * wB) = True
    rightUpperBound = ?rightUpperBound

    rightFinal : abs (pA - pB + 2 * wA) <= (2 * wA + 2 * wB) = True
    rightFinal = joinAbs (rightLowerBound, rightUpperBound)

    helper2 : ((pA + wA) >= (pB + wB)) = True -> (pA - pB) < (wA - wB) = True
    helper2 = ?helper2

  -- Prove: maximum bound on diff in incrementElectMany calls by induction

  diffDiffMany : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> (n : Nat) -> (abs (pA - pB) <= (2*wA + 2*wB) = True)
    -> (abs (diffPriority (fst (incrementElectMany n ((idA, wA, pA), (idB, wB, pB))))) <= (2*wA + 2*wB) = True)
  diffDiffMany idA idB wA wB pA pB Z prf = prf
  diffDiffMany idA idB wA wB pA pB (S k) prf =
    rewrite applies in
    rewrite step in
    Refl
    where
      state : ElectionState
      state = ((idA, wA, pA), (idB, wB, pB))

      kstate : ElectionState
      kstate = (fst (incrementElectMany k state))

      inductive : (abs (diffPriority kstate)) <= (2*wA + 2*wB) = True
      inductive = diffDiffMany idA idB wA wB pA pB k prf

      wAConserved : {s : ElectionState, n : Nat} -> snd3 (fst (fst (incrementElectMany n s))) = snd3 (fst s)
      wAConserved = ?wAConserved

      wBConserved : {s : ElectionState, n : Nat} -> snd3 (snd (fst (incrementElectMany n s))) = snd3 (snd s)
      wBConserved = ?wBConserved

      inductive' : (abs (diffPriority kstate)) <= (2 * (snd3 (fst kstate)) + 2 * (snd3 (snd kstate))) = True
      inductive' = ?inductive'
      --inductive' = rewrite (sym (wAConserved {n=k})) in rewrite (sym wBConserved {n=k}) in rewrite inductive in Refl

      applies : fst (incrementElectMany (S k) state) = fst (incrementElect kstate)
      applies = incrementElectManyApplies k state

      step : (abs (diffPriority (fst (incrementElect kstate))) <= (2*wA + 2*wB) = True)
      step = ?step --let ((idA', wA', pA'), (idB', wB', pB')) = kstate in diffDiff idA' idB' wA' wB' pA' pB' ?todo

  -- This function just simplifies the inequality to an upper bound on nA.
  reduceHelper : (wA, wB : ProposerWeight) -> (nA, n : Integer) ->
    ((((wB * nA) - (wA * (n - nA))) <= (wA + wB)) = True) ->
    nA <= (n * (wA `div` (wA + wB))) + 1 = True
  reduceHelper wA wB nA n lemma1 =
    lemma11
    where
      -- Progressively simplify / rearrange to solve for nA.
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

    where
      -- Split out the first part of the bound on priority difference.
      lteqA : ((wB * nA) - (wA * nB)) <= (wA + wB) = True
      lteqA = fst (splitAbs abslt)

      -- Split out the second part of the bound on priority difference.
      lteqB : ((wA * nB) - (wB * nA)) <= (wA + wB) = True
      lteqB = snd (splitAbs abslt)

      -- Turn into an inequality on nA.
      initialForA : (((wB * nA) - (wA * (n - nA))) <= (wA + wB)) = True
      initialForA =
        rewrite (sym (congSubEq nA nB n neq)) in
        lteqA

      -- Turn into an inequality on nB.
      initialForB : (((wA * nB) - (wB * (n - nB))) <= (wB + wA)) = True
      initialForB =
        rewrite plusComm wB wA in
        rewrite (sym (congSubEq nB nA n (rewrite plusComm nB nA in neq))) in
        lteqB

      -- Solve for the upper bound on nB.
      finalForB : nB <= (n * (wB `div` (wB + wA))) + 1 = True
      finalForB = reduceHelper wB wA nB n initialForB

      -- This sequence of lemmas just transforms the upper bound on nB into a lower bound on nA.
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

      -- Isolate the final lower bound on nA.
      first : nA >= (n * (wA `div` (wA + wB))) - 1 = True
      first = rewrite (plusComm wA wB) in lemma11

      -- Solve for the final upper bound on nA.
      second : nA <= (n * (wA `div` (wA + wB))) + 1 = True
      second = reduceHelper wA wB nA n initialForA

  fairlyProportional : (idA : ProposerId) -> (idB : ProposerId) -> (wA : ProposerWeight) -> (wB : ProposerWeight) ->
    (pA : ProposerPriority) -> (pB: ProposerPriority) -> (n : Nat) -> -- TODO: initial inductive case
    ((natToInteger $ count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB))))) >= ((natToInteger n * (wA `div` (wA + wB))) - 1) = True,
     (natToInteger $ count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB))))) <= ((natToInteger n * (wA `div` (wA + wB))) + 1) = True)
  fairlyProportional = ?fairlyProportional

{- TODO n-validator case, preferably just via an equivalence proof from the 2-validator case. -}
