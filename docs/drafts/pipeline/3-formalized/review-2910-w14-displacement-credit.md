# Displacement thresholds and the credit retained by actual Grams

- **ID:** review-2910-w14-displacement-credit
- **Stage:** 3-formalized
- **Type:** THEOREM / integration
- **Source:** W14 of the obstacles summary.

## Exact task

Treat bandwidths λ∈[3/4,1), both target proportions 7/10 and 3/4, and negative-part
credit of the actual evaluation Grams. Orthogonal model blocks alone do not finish this task.

## Paper proof

Write κ(λ)=1/λ+λ/3 and H(λ)=2−κ(λ). For an orthogonal hyperbolic pair model with
displacement energy η≥0, let h=1+2η. Its Frobenius constraint is
`2p h²=(κ−1)N`. For p>0 and N>0, direct cancellation gives the following exact tests
for any target proportion θ:

1. `θN≤N−2p` iff `(κ−1)≤(1−θ)h²`.
2. Full slack `4pηh≥(θ+κ−2)N` iff `2(1−θ)η≥θ+κ−2`.
3. Off-line slack `4pη(1+η)≥(θ+κ−2)N` iff
   `(3−2θ−κ)h²≥κ−1`.

At κ=4/3, the 70% thresholds are h²≥10/9, η≥1/18, and h²≥5/4.
The 75% thresholds are h²≥4/3, η≥1/6, and h²≥2.
These are model thresholds, not claims about the locations of zeta zeros.

For the actual matrix, write Q=A−B with A,B positive semidefinite, representing real
and imaginary evaluation components. Every positive contraction U satisfies
`−tr(UQ)≤tr(Q₋)`: use positivity of tr(UQ₊) and tr((I−U)Q₋).
Choose U as the spectral projector onto ker A. Then UA=0, so
`tr(UB)≤tr(Q₋)`. For B=2Σ mρ bρbρ*, the lower bound is exactly the sum of squared
imaginary evaluation components surviving projection away from the real span.
This is unconditional and includes cancellations between different off-line pairs.
It can vanish despite nonzero displacement; displacement magnitude alone is insufficient.

## Formalization gates

- [x] Generic κ,θ threshold equivalences.
- [x] λ∈[3/4,1) and both target specializations.
- [x] Positive-contraction and real-kernel lower bounds.
- [x] Instantiate on actual zeta evaluation Grams; expose projected displacement sum.
- [x] Direct leaf checks, transitive axiom audit, umbrella import.

## Lean declarations and audit

`ArithmeticCastelnuovoSeveri/DisplacementThresholdsAcrossBandwidths.lean`:
`hyperbolic_pair_thresholds`, `hyperbolic_pair_bandwidth_thresholds`,
`hyperbolic_pair_seventy_percent`, `hyperbolic_pair_three_quarters`, and
`hyperbolic_pair_seventy_percent_at_four_thirds`.

`ArithmeticCastelnuovoSeveri/ProjectedDisplacementPaysNegativePartCredit.lean`:
`neg_trace_contraction_le_negPart`, `realKernel_trace_le_negativePart`,
`blockQ_negativePart_credit_ge_projectedDisplacement`,
`zetaProjectedDisplacementEnergy_eq`,
`zeta_negativePart_credit_ge_projectedDisplacement`, and
`zeta_zeroSideSlack_ge_projectedDisplacement`.

The actual imaginary vector is written explicitly as
`Im φ̂_T(Im ρ − i(Re ρ−1/2) − τ_k)`; no surrogate zero configuration is used.
The normalization is `2(a(T)L(T)²)⁻¹` times the projected imaginary energy.
Both leaves passed `lake --old env lean`; seven terminal transitive-axiom
audits returned only `propext`, `Classical.choice`, and `Quot.sound`.
Both imports are wired into the ACS umbrella, which was not compiled.

The bound may vanish when the real evaluation span is full. It supplies a
certified zero-side observable, not the missing positive lower bound on actual
zeta displacement needed for a 70% or 75% census.
