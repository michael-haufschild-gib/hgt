# F2 — Gaussian synthesis of physical core packets

- **Stage:** 3-formalized
- **Result:** For every `ε>0` and `x∈ℓ²(zeros)`, the literal series
  `Fε,x(a)=Σ_s exp(−ε(Im s)²)x_(2s) core_s(a)` converges absolutely at every `a>0` and in upper Haar `L²(1,∞)`.
- **Weil bridge:** For `x=windowZeroMap H`, the reflected coefficient product is exactly `exp(−2ε(Im s)²)W_s(H,H)`. Twice the real sum tends to the complete Weil form `Q(H)` as `ε↓0`.

## Proof

The [uniform core estimate](f2-uniform-physical-core-spectral-bound.md) and `1/(2 Re s)≤116 Im s` give
`‖core_s/√a‖_(L²(1,∞))≤11C(1+Im s)^(N+1)exp(π Im s/2)`.
Each coordinate of `x` is bounded by `‖x‖`. Completing the square gives

`exp(−εy²)(1+y)^N exp(By)≤exp((B+N+2)²/(4ε))/(1+y²)` for `y≥0`.

Existing multiplicity-weighted zero-count summability implies summability of `1/(1+(Im s)²)` over upper resonances. Thus the physical column norms are summable. The `L²` sum agrees almost everywhere with the literal series divided by `√a`. At fixed `a>0`, `a^(−Re s)≤1+a⁻¹` gives absolute pointwise convergence.

Reflection preserves `Im s` and multiplicity. Pairing the damped CWS coefficients therefore produces exactly the damped Weil summand. Its norm is bounded by the undamped summand for `ε≥0`; absolute Weil summability and dominated convergence recover `Q(H)`.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/GaussianPhysicalCoreSynthesis.lean`:

- `gaussianPhysicalCore_summable`
- `gaussianPhysicalColumn_summable`
- `gaussianPhysicalCore_eq_Lp_tsum`
- `gaussianPhysicalCore_finite_haar_energy`
- `gaussian_window_reflection_product`
- `tendsto_gaussianWindowWeilEnergy`

Final individual `lake --old env lean` audit passed without warnings. All five printed endpoints have only `propext`, `Classical.choice`, `Quot.sound`. Module wired into the umbrella.

The signed coefficient pairing remains separate from physical Haar energy. No positivity, bounded inverse, or infinite coefficient uniqueness follows here. [Faithful completion](../1-in-progress/f2-faithful-gaussian-core-completion.md) addresses the last issue.
