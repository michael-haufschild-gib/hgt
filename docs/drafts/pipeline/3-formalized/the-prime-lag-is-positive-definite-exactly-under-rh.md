# The prime lag is positive definite exactly under RH

- **ID:** prime-lag-positive-definite
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A90.
- **Statement:** RH is equivalent to positive definiteness on the real line of the even prime-count function `primeLag`.

## Formula and proof

For `u ≠ 0`, the lag is `exp(−|u|/2) primeDeviation(exp |u|)`; its diagonal is `poleSharpConstant`. The explicit formula and evenness identify this function with `weilLagFunction`. Expanding the central trace of the zero motive identifies the same lag. The flow Castelnuovo–Severi criterion and the zero-motive purity criterion then give RH.

## Lean

Module: `formal/GaloisForLFunctions/InfiniteRankPurityTheory/ThePrimeLagIsPositiveDefiniteExactlyUnderRH.lean`.

- `primeLag_eq_weilLagFunction`
- `centralTrace_zeroMotive_eq_weilLagFunction`
- `riemannHypothesis_iff_positiveDefinite_weilLagFunction`
- `riemannHypothesis_iff_positiveDefinite_primeLag`

Direct `lake --old env lean` audit passed. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound`. Imported by `InfiniteRankPurityTheory.lean`.
