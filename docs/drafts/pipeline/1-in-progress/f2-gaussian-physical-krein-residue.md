# F2 — Gaussian physical realization of complete Weil energy

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** Extend the finite physical cusp-energy residue to the existing Gaussian-damped zero coordinates, then recover complete Weil energy as damping vanishes.

## Exact target

For `ε>0` and `x∈ℓ²(zetaZeroConfig.carrier,ℂ)`, use the existing damping

`c_s=exp(−ε(Im s)²)x(upperMayerZero s)`.

Set `κ_s=−core_s/b_s`, `b_s=2ζ(2s−1)/(2s−1)`, and

`Ψ(u)=exp(u/2) Σ_s c_s κ_s(exp(−u))`, `λ_st=2s+2 conjugate(t)−1`.

Prove absolute convergence of the physical packet and the finite-depth counterterm, and

`lim_(T→∞) [∫_0^T |Ψ(u)|²du − Re Σ_(λ_st≠0) c_s conjugate(c_t)(exp(λ_st T)−1)/λ_st]/T`

`= Re Σ_s c_s conjugate(c_(s♯))`.

For the existing real-window zero coordinates, twice this residue should tend to complete Weil energy as `ε→0+`. This is a literal physical realization of the signed form. Subtracting growing counterterms supplies no positivity by itself.

## Uniform analytic gate [K]

The [audited uniform cusp bound](../3-formalized/f2-uniform-normalized-cusp-remainder.md) gives

`|κ_s(a)−a^(1−2s)|≤C(1+Im s)^4 exp(π Im s) a`.

Real-order Bessel comparison removes height from the Eisenstein tail bound. Charge normalization cancels to `w/Λ(2−w)`, where `w=2s`; the weighted field mass and the exact Cauchy kernel tail yield the boundary exponent. Gamma estimates in the Euler strip and the reciprocal resonance-gap bounds supply the uniform constant. No common spectral gap or separate inverse-charge estimate is assumed.

## Passage to infinite packets

With the required uniform bound proved, each normalized logarithmic error is bounded by `C_s exp(−u/2)`. Its cross integral with mode `t` costs `C_s/(1−2 Re t)`. The audited reflected zero-free bound gives `(1−2 Re t)⁻¹≤116 Im t`; existing Gaussian spectral summability then controls both cross terms and error squares.

At fixed `T`, the bound `|(exp(λT)−1)/λ|≤T exp(T)` for `T≥0` avoids any zero-separation premise. Integrate the absolutely convergent model sum before taking the depth limit. Zero exponents pair exactly reflected resonances; the integrable physical error disappears after division by `T`.

## Status

Finite-packet physical residue: [audited physical realization](../3-formalized/f2-physical-cusp-krein-residue.md). The uniform estimate is formalized; the infinite physical residue remains to be Lean-audited. No complete-Weil positivity claim.
