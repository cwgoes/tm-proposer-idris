### Summary

Formal verification of fairness of the [Tendermint](https://github.com/tendermint/tendermint) proposer election algorithm in the proof assistant [Idris](https://idris-lang.org).

In particular, the Idris source in this repository proves that maximally strict bounds on stake-proportionality of proposer election hold over an epoch of any length with no power changes by inhabiting the following type:

```idris
fairlyProportional :
  (idA : ProposerId) -> (idB : ProposerId) ->
  (wA : ProposerWeight) -> (wB : ProposerWeight) ->
  (pA : ProposerPriority) -> (pB: ProposerPriority) ->
  (n : Nat) ->
  (wA >= 0 = True) -> (wB >= 0 = True) ->
  (abs(pA - pB) <= (wA + wB) = True) ->
  ((count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))))
      >= ((n * (wA / (wA + wB))) - 1) = True,
   (count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))))
      <= ((n * (wA / (wA + wB))) + 1) = True)
```

where `incrementElectMany` repeats the proposer-election function and returns the list of elected proposers.

In English, this proof could be read as "a validator, in a sequence of proposer elections where no other power
changes take place, proposes no fewer blocks than the total blocks in the epoch multiplied by its fraction of stake
less one, and proposes no more blocks than the total blocks in the epoch multiplied by its fraction of stake plus one".

As epochs can be as short as one block (for which one proposer must be chosen), this is the strictest possible fairness criterion.

The requisite initial bound on the difference in proposer priority is the reason for [this pull request](https://github.com/tendermint/tendermint/pull/3049).

### Caveats

- You must trust that the type theory used by Idris ([paper](https://pdfs.semanticscholar.org/1407/220ca09070233dca256433430d29e5321dc2.pdf)) is sound.
- At present, this proof only covers the two-validator case - a reduction from the n-validator case is planned.
- This fairness criterion only holds over epochs with no validator power (weight) changes.
- The Idris standard library does not implement proofs of standard field laws for arithmetic operations over integers, so these are [assumed to hold](src/Types.idr).
  In practice standard library proofs wouldn't be helpful anyways since the actual implementation is in Golang, not Idris.
- This constitutes a proof of algorithmic correctness, which is not the same thing as implementational correctness - the Golang
  code could have incorrect optimizations, integer overflow/underflow, etc.

### Usage

To check that the verified properties hold, run:

```bash
make check
```

To open up a REPL and play around with proof components, run:

```bash
make
```

Or to read the logic yourself, open [Main.idr](src/Main.idr).
