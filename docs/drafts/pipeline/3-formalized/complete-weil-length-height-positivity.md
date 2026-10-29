# Complete Weil positivity in length and height

- **ID:** complete-weil-length-height-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3; certified Trans-Metzler floor.
- **Statement:** At reciprocal-width height `T=N/c`, the actual complete Weil matrix
  is eventually positive definite for every fixed `0<c<1+δ_*`, where
  `δ_*=1/107520002048050000`.

The width identity `(N/c)⁻¹=c/N` identifies the two matrices exactly, including
Gamma, primes, and both poles. Existing separated positivity covers `c≤1`;
the optimized certificate covers `c=1+δ`, `0≤δ<δ_*`. Its floor transports as
`1/25-2000δ(1+1024000(2100000+1/25))-ε`. Horizons may depend on the fixed overlap.
The coordinate inequality is exactly `N<(1+δ_*)T`.

After subtraction of the prime logarithm, the actual plateau self-energy equals
`completeWeilSelfFinitePart φ 1-γ-log c` up to error at most
`(exp(1/2)/2)c/N` for every `0<c≤N`. Thus the renormalized diagonal retains
the logarithmic loss as overlap grows.

Lean: `GaloisForLFunctions/TransMetzlerWeilPositivity/CompleteWeilLengthHeight.lean`.
Main declarations: `completeWeilMatrixAtHeight_height`,
`eventually_completeWeilMatrixAtHeight_posDef`,
`eventually_completeWeilMatrixAtHeight_floor`,
`abs_plateau_diagonal_add_log_overlap_le`.
Direct `lake --old env lean` check passed; transitive axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Imported by the TransMetzlerWeilPositivity umbrella.
