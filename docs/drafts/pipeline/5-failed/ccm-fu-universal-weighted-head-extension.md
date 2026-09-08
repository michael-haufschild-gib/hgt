# CCM-FU: universal next-step descent under a fixed head weight

- Stage: 5-failed; exact positive completion classification formalized.
- Type: stronger local rule from the [fixed-weight path candidate](../1-in-progress/ccm-fu-weighted-head-dissipation.md).
- Boundary: the main complete-path claim remains open.

## Refuted rule

For the literal potential `L_alpha=V+alpha H²`, choose one fixed positive
head weight and demand a nonincreasing next prime at every proper actual
processed state. The rule fails for every real alpha already at cutoff 25.

Two cores suffice. The core P={2,7,11,13,17,19,23} leaves primes 3 and 5
and requires a weight above 1/20 to pay for unavoidable V growth. The
core T=primes_below_25\{7} leaves a same-sign scalar absorption and
requires a weight below 1/20. Neither an unprocessed prime nor the
arithmetic source is replaced by model data.

## Strong positive survivor: exact admissible intervals

Both states have nonempty ranges of positive weights permitting COMPLETE
monotone remaining orders. Those ranges are classified exactly in Lean:

- At P, all nonnegative weights at least
  `sigma=(2ac-b²)/(h²-(h+b)²)` work, and no smaller nonnegative weight
  works. Here h,a,b,c are its actual four retained coefficients.
  Prime five is strictly preferable as the first merger for every
  nonnegative weight, and either final merger strictly decreases both
  V and H². Lean proves `1/20<sigma<1/5`.
- At T, exactly the weights at most
  `beta=t²/((g+t)²-g²)` work, where g is its actual head and t its
  remaining seven-fibre. Lean proves `0<beta<1/20`.

This is an exact classification, not merely a negative example. A proof
using a fixed coercive potential must select states that admit continuation;
universal continuation from arbitrary cores is unavailable. Complete
paths from the empty core may avoid the incompatible states. Their
all-cutoff existence has not been proved or refuted by this result.

## Paper and Lean status

The [full analytic proof](../3-formalized/ccm-fu-weighted-head-state-selection.md)
retains every actual fibre and uses rational logarithm, square-root and
Euler-constant bounds. It establishes the interval classifications,
strict rational separation, universal local obstruction and coercive
comparison with complete energy. All proofs passed scratch Lean and exact
foreground leaf emission. The seven new theorem audits report only
propext, Classical.choice and Quot.sound. No numerical premise is used.
The formal certificate records the unrelated global-lint failure and
remaining package-audit limitation.

The [single RunPod diagnostic](../2-fully-proven/computations/ccm-fu-weighted-head-dissipation-2026-09-08/README.md)
screened all saved states and every weight interval without a grid. It
found a common positive interval for complete monotone paths through
cutoff 32 despite failure of the universal local rule. This finite
survival remains guidance and supplies no RH theorem.
