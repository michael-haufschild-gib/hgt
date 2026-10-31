# Explicit power-log positivity and conductor confinement

- **ID:** explicit-power-log-positivity-and-confinement
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../../reports/review-3110/obstacles-summary.md, A1
- **Statement:** Replace the unspecified conductor-confinement constant by a proved explicit constant and sharpen the accuracy and overlap exponents in complete Weil positivity.

## Mathematical targets

1. Explicit conductor confinement, uniformly in the horizon: squared projection error at most `η` for `log R ≤ C (K + 1) / η^p`, with numerical `C` and improved `p`.
2. An explicit reverse defect gap and numerical positive overlap exponent.
3. Optimized low-band, projection-accuracy, and high-cutoff exponents in all-vector positivity, with the residual and confinement ceilings accounted for.

## Existing bounds

`ConductorBandTopTailBounds` proves `p = 3` with an unspecified constant. `TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap` uses `Q₁ = floor((log N)^(1/12))`, squared error `η ≍ c⁻¹⁰`, cutoff `log R ≪ c⁴⁶`, and `α < min(1/500, 1/(60 C_cut))`. The constant originates in smooth–rough conditioning.

## Strengthened confinement proof

The finite-sieve harmonic comparison at horizon one, together with `L(P) ≤ 2(log P + log 4 + 4)`, gives `P(n) log n ≥ 1/128` for the Mertens product. Put

`S = 24/log 2 + 1715/(1 − 2^(−1/4))`, `T = max(1, 512S)`,
`C₀ = (1+4T) exp(3(1+1/(4T)) T(4T+2))`.

Dyadic shell summation and prime peeling give conditioning error `≤ C₀ D/log P` uniformly in the horizon.

For the conditioned profile `f`, weighted Jensen and the smooth-part moment give
`Σ_(a≤A) (log a+L(P)) w_N(a) f(a)² ≤ 2D+3L(P)‖x‖²`.
Spectral truncation, retaining this moment, gives error at most `16(2K+3L(P))/log R`. The former support bound `16(log A+L(P))/log R` is unnecessary.

Set `δ=η/8`. Choose `log P ≥ C₀(K+1)/δ`, `log A ≥ 2(K+L(P))/δ`, and
`log R ≥ 2log A+2L(P)+4+16(2K+3L(P))/δ`, with logarithmic rounding error at most three. These choices give squared approximation error at most `6δ≤η` and

`log R ≤ C₂(K+1)/η²`,
`C₂ = 64[54(2(C₀+3)+2(log 4+4))+49]`.

The reverse gap constant is consequently `256C₂`. These statements are being checked in `Conductor/ExplicitRoughConditioning.lean`, `Conductor/RamanujanApproximationByLogarithmicMoment.lean`, and `Conductor/QuadraticConductorConfinement.lean` under `RenormalizedArithmeticPotentialTheory`.

## Remaining mathematical work

Propagate quadratic confinement through complete-Weil high-tail suppression; optimize the low-band and accuracy choices; audit the resulting numerical positivity exponent. A2–A18 remain outside this card and unsolved by these bounds.

## Gates

- [x] Precise target and source dependencies identified.
- [ ] Dependency-closed proof of the strengthened bounds.
- [ ] Lean formalization, direct file audit, and transitive axiom audit.
