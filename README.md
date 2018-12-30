### Summary

Formal verification of fairness of the [Tendermint](https://github.com/tendermint/tendermint) proposer election algorithm in the proof assistant [Idris](https://idris-lang.org).

In particular, the Idris source in this repository proves that maximally strict bounds on stake-proportionality of proposer election hold over an epoch of any length with no power changes by inhabiting the following type:

```idris
fairlyProportional : (idA : ProposerId) -> (idB : ProposerId) ->
  (wA : ProposerWeight) -> (wB : ProposerWeight) ->
  (pA : ProposerPriority) -> (pB: ProposerPriority) -> (n : Nat) -> (abs (pA - pB) <= (wA + wB)) ->
  ((natToInteger $ count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))))
    >= ((natToInteger n * (wA `div` (wA + wB))) - 1) = True,
   (natToInteger $ count idA (snd (incrementElectMany n ((idA, wA, pA), (idB, wB, pB)))))
    <= ((natToInteger n * (wA `div` (wA + wB))) + 1) = True)
```

where `incrementElectMany` repeats the proposer-election function and returns the list of elected proposers.

In English, this proof could be read as "a validator, in a sequence of proposer elections where no other power
changes take place, proposes no fewer blocks than the total blocks in the epoch multiplied by its fraction of stake
less one, and proposes no more blocks than the total blocks in the epoch multiplied by its fraction of stake plus one".

As epochs can be as short as one block, this is the strictest possible fairness criterion.

The requisite initial bound on the difference in proposer priority is the reason for [this pull request](https://github.com/tendermint/tendermint/pull/3049).

### Caveats

- You must trust that the type theory used by Idris ([paper](https://pdfs.semanticscholar.org/1407/220ca09070233dca256433430d29e5321dc2.pdf)) is sound.
- At present, this proof only covers the two-validator case - a reduction from the n-validator case is planned.
- The Idris standard library does not implement proofs of standard field laws for arithmetic operations over integers, so these are [assumed to hold](src/Types.idr).
  In practice standard library proofs wouldn't be helpful anyways since the actual implementation is in Golang, not Idris.

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
