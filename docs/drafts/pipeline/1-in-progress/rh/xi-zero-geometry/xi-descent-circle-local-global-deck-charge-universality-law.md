# Xi-descent circle local/global deck-charge universality law

## Status

Formalized in Lean and wired into the RHTower umbrella. Kept in progress until global exhaustion
and final audit complete.

## Lean sources

- `GaloisForLFunctions.RHTower.UPlaneWindingCircle`
- `GaloisForLFunctions.RHTower.DeckChargeCalculus`
- `GaloisForLFunctions.RHTower.CarrierDeckCharge`

## Conjecture

For every zero-avoiding circle and every dyadic rung, the descended Xi loop charge is the sum of
the local additive charges of exactly the enclosed zeros. Applying the canonical deck character
turns this sum into the product of the enclosed local carrier charges.

Thus arbitrary-circle global monodromy is an exact finite multiplicative Euler law over the local
Xi-descent divisor, not merely the reduction of an unnamed total order.

## Corpus gap

The circle theorem constructs the exact enclosed zero census and identifies loop charge with the
residue class of total order. Generic deck-charge calculus proves additive and multiplicative
finite-family laws. No theorem specializes those laws back to the unconditional Xi-descent circle
and identifies every factor with `carrierCharge xiDescent`.

## Proof plan

1. Take the exact finite zero census from `loopCharge_xiDescent_circle`.
2. Rewrite total-order charge using `wCharge_sum`.
3. Apply `deckChar_sum`.
4. Identify each character factor definitionally with the local Xi-descent carrier charge.

No numerical computation is used.

## Novelty status

Post-proof searches found the classical argument principle and standard local/global monodromy
language for branched covers. Those sources support the abstract mechanism. No searched source
stated the exact unconditional `xiDescent` finite-circle census simultaneously in additive
`ZMod (2^k)` form and as the product of the corpus's local `carrierCharge` values. Novelty claim
is restricted to this Xi-descent formal connector.

## Lean result

`formal/GaloisForLFunctions/RHTower/XiDescentCircleLocalGlobalDeckChargeUniversalityLaw.lean`
proves the exact enclosed-zero census together with:

- additive loop charge as the sum of all enclosed local charges;
- multiplicative deck character as the product of all enclosed Xi-descent carrier charges.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/XiDescentCircleLocalGlobalDeckChargeUniversalityLaw.lean`
