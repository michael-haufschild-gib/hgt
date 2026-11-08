# The actual regularized Narain–Eisenstein overlap

- **ID:** W11-NR
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [W11](../1-in-progress/ads3-scalar-modular-bootstrap.md)

## Conjecture

Let `E_s` be the Eisenstein series with constant term
`y^s+φ(s)y^(1−s)`, where `φ(s)=Λ(2s−1)/Λ(2s)` and
`Λ(s)=Γ_ℝ(s)ζ(s)`. For the actual normalized Narain partition `Z_(ρ,σ)`,
`F_T={z∈F: Im z≤T}`, and `Re s>1`,

`lim_(T→∞)[∫_(F_T) Z_(ρ,σ)(z) E_s(z) dμ(z)`
`             −T^s/s−φ(s)T^(1−s)/(1−s)]`
`  = Mellin(H_(ρ,σ))(s) = 2Λ(2s)E_s(ρ)E_s(σ)`.

This is a bilinear overlap; no complex conjugation is inserted.

## Norm-unfolding mechanism

Proved Poisson triality reduces norm unfolding to the domination

`|Z_(B+iV,σ)(τ)| ≤ Z_(iV,σ)(τ)`, with the right side real and nonnegative.

Indeed exchange `ρ` and `τ`, remove the spin phase by the triangle
inequality, then exchange back. Its horizontal integral is
`y[1+H_(iV,σ)(y)]`. The proved scalar Mellin convergence therefore gives
absolute norm-unfolding for `Re s>1`, even though a direct four-dimensional
Gaussian bound alone only reaches `Re s>2`.

Use the lower-height incomplete Eisenstein series: on `F`, for `T≥1`,
it equals `E_s−1_(y>T)y^s`. Primitive-row unfolding gives
`T^s/s+∫₀ᵀ y^(s−1)H(y)dy`. The remaining cusp integral has explicit
vacuum contribution `φ(s)T^(1−s)/(s−1)`. For `Re s>1`, the whole remaining cusp integral tends to zero; the
explicit scattering correction does too. A linear bound `|Z(x,y)|≤Cy`
on `y≥1/2` suffices: after subtracting `y^s`, the Eisenstein constant
term contributes at most `Cy^(2−Re s)` and its Fourier tail is
exponentially small. The corpus proves integrability of `y^β` on `F`
for `β<1`. Thus this overlap does not require the full nonvacuum
exponential tail.

## Remaining inputs

- [Poisson triality and full modular invariance](../3-formalized/ads3-narain-modular-inversion.md) are formalized.
- The [positivity majorant, angular norm control and both cusp bounds](../3-formalized/ads3-narain-partition-cusp-bounds.md) are formalized.
- Specialize `HTGeometry.ModularStripLIntegralUnfolding` and
  `ModularStripUnfolding` to this actual source. The truncated-row
  comparison is modeled by `EisensteinMaassSelbergRegion` and
  `EisensteinUnfoldedRowSum`; their existing endpoints pair two
  Eisenstein functions and cannot substitute for the Narain proof.
- Audit the primitive-row factor two against the normalized `E_s`.
  `EisensteinTruncatedRowSum.tsum_above_eq` identifies the only rows
  above a cutoff `T≥1` on the fundamental domain as `±(0,1)`.

## Gates

- [x] 0 → 1: modularity and source norm majorant formalized.
- [ ] 1 → 2: truncated unfolding and cusp limit proved without extra admissions.
- [ ] 2 → 3: Lean formalization, axiom audit and umbrella import.
