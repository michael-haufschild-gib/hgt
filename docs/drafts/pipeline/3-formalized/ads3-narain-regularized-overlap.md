# The actual regularized Narain–Eisenstein overlap

- **ID:** W11-NR
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [W11](../1-in-progress/ads3-scalar-modular-bootstrap.md)

## Theorem

Let `E_s` be the actual Poincaré Eisenstein series with constant term
`y^s+φ(s)y^(1−s)`, where `φ(s)=Λ(2s−1)/Λ(2s)` and
`Λ(s)=Γ_ℝ(s)ζ(s)`. For every target pair `(ρ,σ)`, the actual normalized
Narain partition `Z_(ρ,σ)`, `F_T={z∈F: Im z≤T}`, and `Re s>1`,

`lim_(T→∞)[∫_(F_T) Z_(ρ,σ)(z) E_s(z) dμ(z)`
`             −T^s/s−φ(s)T^(1−s)/(1−s)]`
`  = Mellin(H_(ρ,σ))(s) = 2Λ(2s)E_s(ρ)E_s(σ)`.

This is a bilinear overlap, without complex conjugation.

## Proof

Poisson triality gives the positive majorant
`|Z_(B+iV,σ)(τ)|≤Z_(iV,σ)(τ)`. Its horizontal integral is
`y[1+H_(iV,σ)(y)]`. Absolute scalar Mellin convergence for `Re s>1`
therefore gives absolute strip integrability of the incomplete seed.
Primitive-row unfolding, including its factor two, identifies the
normalized incomplete overlap with `∫₀ᵀ y^(s−1)(1+H(y))dy`.

On `F`, for `T≥1`, only primitive rows `±(0,1)` lie above the cutoff.
The incomplete Eisenstein series consequently equals
`E_s−1_(y>T)y^s`. Thus the finite-cutoff overlap minus `T^s/s` equals
`∫₀ᵀ y^(s−1)H(y)dy−∫_F 1_(y>T)Z(E_s−y^s)`.

The linear cusp bound for `Z` and the exact Eisenstein expansion bound
the corrected product by `Cy^(2−Re s)` plus an integrable exponential
tail. Powers `y^β` are integrable on `F` for `β<1`; dominated convergence
makes the cusp correction vanish. Absolute Mellin convergence gives the
full scalar Mellin integral. The explicit scattering counterterm tends
to zero as well. The proved scalar Mellin product formula gives the result.

## Lean endpoints

Main theorem:
[`narain_regularized_overlap_poincare`](../../../../formal/GaloisForLFunctions/ArithmeticScatteringHolography/ModularBootstrap/NarainRegularizedOverlap.lean).
The exact finite identity is `narainTruncatedOverlap_sub_vacuum`.

Supporting modules in `ArithmeticScatteringHolography/ModularBootstrap`:
`NarainIncompleteSeed`, `NarainPartitionStripBounds`,
`NarainIncompleteUnfolding`, `NarainIncompleteIntegral`,
`NarainEisensteinNormalization`, `NarainOverlapCusp`,
`NarainTruncatedOverlap`, `NarainRegularizedOverlap`.

All eight modules passed direct Lean checks. Sixteen endpoint axiom
audits contain only `propext`, `Classical.choice`, `Quot.sound`.
All umbrella imports are wired.

The existing meromorphic continuation and pole-detection results now
apply to the actual regularized overlap. No small-height RH rate follows
from this identity alone.

## Gates

- [x] 0 → 1: modularity and source norm majorant formalized.
- [x] 1 → 2: absolute unfolding, exact truncation and cusp limit proved.
- [x] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
