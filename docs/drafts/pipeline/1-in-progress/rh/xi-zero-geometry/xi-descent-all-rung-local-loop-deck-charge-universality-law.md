# Xi-descent all-rung local-loop deck-charge universality law

## Status

Exact Lean check passed with
`lake env lean GaloisForLFunctions/RHTower/XiDescentAllRungLocalLoopDeckChargeUniversalityLaw.lean`.

## Lean-generated inputs

- `UPlaneDescent.lean`: analytic order is preserved from a right-half Xi point to its squared
  centered image under `xiDescent`.
- `UPlaneWinding.lean`: every sufficiently small descended circle has winding number equal to that
  Xi analytic order.
- `WindingNumber.lean`: loop charge is winding reduced modulo `2^k`.
- `DeckChargeCalculus.lean`: deck character converts additive `wCharge` to multiplicative
  `deckRed`.
- `CarrierDeckCharge.lean`: carrier charge is `deckRed` of analytic order.

## Survivor

For every right-half point and every dyadic rung, three encodings agree: Xi's local carrier charge,
the descended carrier charge at the squared centered point, and the multiplicative deck character
of every sufficiently small descended loop. Existing transport covered only rung 1 and existing
winding comparison only the integer index; the new law closes the full all-rung commutative
triangle.

## Formal target

`RHTower.deckChar_loopCharge_xiDescent_center_sq`

## Novelty audit

Pending post-formalization literature search.
