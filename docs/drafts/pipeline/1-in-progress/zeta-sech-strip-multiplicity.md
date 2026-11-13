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

- [x] Strip source statement read; kernel coefficient checked on paper.
- [ ] Derive fixed-line sublogarithmic logarithmic derivative from the corpus zero-free half-plane.
- [ ] Prove the sech residue identity, summability, and all-height error.
- [ ] Formalize the unconditional weighted fibre theorem and critical specialization.
- [ ] Check new modules and audit transitive axioms.

No new Lean theorem is claimed. B47 still requires the coefficient to tend to zero.
