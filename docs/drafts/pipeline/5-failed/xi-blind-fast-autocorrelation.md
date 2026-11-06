# Fast autocorrelation tails cannot produce an exact Xi blind test

- **Stage:** 5-failed
- **Type:** PROVEN NO-GO (specified decay class)
- **Wall:** Γ56; unrestricted existence remains open.

**Excluded class.** Strip factors `Φ=Ξg`, with the prescribed conjugation symmetry,
exponential strip decay, and `g(0)≠0`, whose autocorrelation obeys
`|K(x)|≤C exp(−a exp(b|x|))`, `a>0`, `b>3/2`.

**Killing theorem.** `not_fastDoubleExp_crossCorr_of_stripXiFactor`, in
`BiScaleUncertainty/PositiveSpectralXiDivisorCapacity.lean`. Positivity makes each
real spectral zero at least double; the known simple-critical Xi density exceeds
the angular capacity allowed by this tail.

**Positive survivor.** `four_mul_simpleCriticalCount_le_divisor_of_nonnegative`
gives exact disc divisor mass `≥4N₀,s(T)`. This doubles the real-divisor capacity
without an analytic quotient or Xi multiplicity-transfer assumption.

**Status.** Dependency-closed [paper proof and Lean certificate](../3-formalized/xi-blind-autocorrelation-capacity.md).
Direct Lean audit passed; standard kernel axioms only. The endpoint `b=3/2`
and unrestricted Γ56 existence remain unresolved.
