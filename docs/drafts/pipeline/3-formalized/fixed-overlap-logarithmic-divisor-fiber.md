# A successor divisor fiber grows logarithmically at fixed overlap

- **ID:** fixed-overlap-logarithmic-divisor-fiber
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3; SSHA non-ratio rows.
- **Statement:** At every fixed `c>1`, the plateau's normalized downward divisor fiber
  from row `N` to product `N+1`, divided by `log(N+1)`, converges to
  `bumpCorr φ (1/c)/(∫φ²)>0`.

For product `ℓ`, the Schur weight cancels the prime square root:
`(Λ(k)/√k)√(m/(ℓ/k))=Λ(k)√(m/ℓ)`. Every divisor has lag `logℓ-logm`.
The identity `Σ_(k|ℓ)Λ(k)=logℓ` therefore gives the exact fiber
`√(m/ℓ) logℓ · bumpCorr g(logℓ-logm)`. At `m=N`, `ℓ=N+1`, every divisor
with nonzero Mangoldt coefficient has quotient in `1..N` and is a non-ratio edge.

Dilation and division by atom mass leave
`√(N/(N+1)) log(N+1) · bumpCorr φ(firstExteriorOverlap N/c)/(∫φ²)`.
The lag tends to `1/c`. Continuity of autocorrelation gives the limit;
strict positivity of the plateau on `(0,1)` makes its coefficient positive for `c>1`.
Thus the fiber tends to infinity. This concerns the corpus's Schur weights `n^(-1/2)`;
it does not give an unweighted operator norm lower bound.

Lean: `GaloisForLFunctions/TransMetzlerWeilPositivity/FixedOverlapHasLogarithmicDivisorRows.lean`.
Main declarations: `successor_divisor_in_horizon`, `weightedDownwardDivisorFiber_eq`,
`plateauSuccessorFiber_eq`, `tendsto_plateauSuccessorFiber_div_log`,
`plateauSuccessorFiber_atTop`. Direct `lake --old env lean` check passed;
transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
Imported by the TransMetzlerWeilPositivity umbrella.
