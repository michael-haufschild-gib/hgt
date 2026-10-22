# Xi-descent local/global complete deck-charge universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL EXACT SYNTHESIS; CLASSICAL MONODROMY INGREDIENTS]`

## Lean-derived conjecture

Three terminal Xi-descent laws separately provide:

- the all-rung local small-loop charge triangle;
- arbitrary-circle additive and multiplicative local/global factorization;
- arbitrary-circle additive and multiplicative aggregate-cancellation classification.

The two arbitrary-circle theorems quantify separate existential zero censuses.  A stronger common
law should produce one exact finite census that simultaneously carries both factorizations and
both cancellation equivalences, while retaining the all-rung local triangle.

## Corpus inputs

- `RHTower.deckChar_loopCharge_xiDescent_center_sq`
- `RHTower.xiDescent_circle_localGlobalDeckCharge`
- `RHTower.wCharge_eq_zero_iff`
- `RHTower.deckChar_injective`

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof targeted search found classical local/global monodromy and Hadamard-product
factorization machinery, including:

- Pérez-Marco, *Local monodromy formula of Hadamard products*, arXiv:2011.10497:
  <https://arxiv.org/abs/2011.10497>

Verdict: local monodromy products are classical.  The exact Xi-descent law proved here—one common
finite zero census simultaneously carrying additive loop-charge factorization, multiplicative
deck-character factorization, both dyadic divisibility classifications, and the all-rung local
triangle—was absent from the Lean corpus and was not found in targeted literature.

## Lean target

`formal/GaloisForLFunctions/RHTower/XiDescentCircleLocalGlobalDeckChargeUniversalityLaw.lean`

## Verification

- source proof exact, warning-free:
  `lake env lean GaloisForLFunctions/RHTower/XiDescentCircleLocalGlobalDeckChargeUniversalityLaw.lean`
- umbrella already imports target module
- final module build deferred to terminal audit
