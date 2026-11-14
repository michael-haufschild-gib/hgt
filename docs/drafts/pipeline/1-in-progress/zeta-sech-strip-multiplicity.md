# A positive strip test bounds zeta multiplicity

- **ID:** zeta-sech-strip-multiplicity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For every `ε>0`, every sufficiently high critical zeta zero satisfies `m(1/2+iγ) ≤ (3/(8π)+ε)log|γ|`.

## Exact stronger target

For fixed `3/8<a<1/2`, the horizontal fibre satisfies

`Σ_{Imρ=γ} m(ρ) sec(π(Reρ−1/2)/(2a)) ≤ (a/π+o(1))log|γ|`.

All zeros here are nontrivial; multiplicities are analytic orders. The error is uniform over heights, not an averaged assertion.

## Proof mechanism and remaining inputs

`MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_quasiRH_strip` supplies `|Reρ−1/2|≤3/8`. Choose `3/8<b<a` and use `K_a(z)=1/cosh(πz/(2a))` on the contour `Re s=1/2±b`. On the entire zero strip, `Re K_a(Imρ−γ−i(Reρ−1/2))>0`. At the target horizontal fibre its value is the displayed secant weight.

The proposed residue identity sums these positive terms as

`(1/(2π)) ∫_R [L_b(γ+u)K_a(u−ib)−L_{−b}(γ+u)K_a(u+ib)] du`,

where `L_b(t)=ξ′/ξ(1/2+b+it)`. Fixed-line `ζ′/ζ=o(log|t|)` would give `L_b(t)/log|t|→1/2` and `L_{−b}(t)/log|t|→−1/2`. Since each shifted kernel integrates to `2a`, the main term is `(a/π)log|γ|`. Exponential decay dominates the global logarithmic bound, so dominated convergence gives an all-height error. Horizontal contour edges and divisor tails must be justified, not assumed.

The implementation can avoid an infinite divisor sum: apply `rectIntegral_mul_logDeriv_zetaResidueUnit_eq_closedRectangleZeroSum` to `G=(s−1)ζ`, retain the positive target fibre, and send independently selected lower and upper edges to infinity. `exists_horizontal_height_polylog` supplies those edges near `−n,+n` with `G≠0` and `|G′/G|≪log²n`. The shifted kernel mass has the direct primitive `arctan(sinh y/cos θ)`.

For the fixed-line input, `CCMGeneralizedVonKoch.lean` gives an `O(log|t|)` bound inside the zero-free half-plane. Three-circles interpolation for `ζ′/ζ` between an inner disk in `Re s>1` and an outer disk in `Re s>7/8` yields `O((log|t|)^θ)` with `θ<1`. This step is being formalized separately in `ConjugateDiagonalGeometry`.

The fibre estimate would also give the uniform envelope `m(β+iγ)/log|γ| ≤ (3/(8π))cos((4π/3)(β−1/2))+o(1)`. In particular, multiplicities on the two outer strip boundaries would be sublogarithmic. These consequences remain unformalized.

- [x] Strip source statement read; kernel coefficient checked on paper.
- [ ] Derive fixed-line sublogarithmic logarithmic derivative from the corpus zero-free half-plane.
- [ ] Prove the sech residue identity, summability, and all-height error.
- [ ] Formalize the unconditional weighted fibre theorem and critical specialization.
- [ ] Check new modules and audit transitive axioms.

## Lean results

`SquareRootThreshold/SechStripKernel.lean` proves strip positivity, exponential decay,
vertical real mass `2a`, and weighted integrability.
`ConjugateDiagonalGeometry/LogarithmicConvolution.lean` proves preservation of an
all-height logarithmic asymptotic under convolution with an integrable first moment.
`SquareRootThreshold/SechRectangleMultiplicity.lean` bounds the weighted
multiplicity of every finite subset of enclosed zeros by the rectangle boundary
integral. All three modules pass Lean and use only `propext`, `Classical.choice`,
`Quot.sound`.

The fixed-line drafts depend on `Detector/QuasiRiemannHypothesis.lean`; its split
import closure lacks compiled dependencies. The existing consolidated artifact
does not export the required theorem. The fixed-line drafts and final fibre
estimate are not certified. B47 still requires the coefficient to tend to zero.
