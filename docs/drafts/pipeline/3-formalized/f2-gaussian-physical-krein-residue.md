# F2 — Gaussian physical realization of complete Weil energy

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Complete Weil energy is the vanishing-damping limit of twice the renormalized mean square-energy of actual Gaussian cusp packets.

## Exact theorem

For `ε>0` and `x∈ℓ²(zetaZeroConfig.carrier,ℂ)`, set

`c_s=exp(−ε(Im s)²)x(upperMayerZero s)`,

`κ_s=−core_s/b_s`, `b_s=2ζ(2s−1)/(2s−1)≠0`,

`Ψ(u)=exp(u/2) Σ_s c_s κ_s(exp(−u))`, `λ_st=2s+2 conjugate(t)−1`.

The physical series converges absolutely at every positive physical coordinate. For every finite depth `T≥0`, the counterterm

`CT(T)=Re Σ_(λ_st≠0) c_s conjugate(c_t)(exp(λ_st T)−1)/λ_st`

is absolutely summable, and

`[∫_0^T |Ψ(u)|²du − CT(T)]/T → Re Σ_s c_s conjugate(c_(s♯))`.

For `x=windowZeroMap A H`, twice this physical residue equals the existing Gaussian-damped Weil energy. Consequently

`lim_(ε→0+) lim_(T→∞) 2[∫_0^T |Ψ_ε(u)|²du − CT_ε(T)]/T = weilQuad H`.

Every zero multiplicity and both half planes are retained. Subtracting the explicit counterterms supplies no positivity.

## Proof

The [uniform exact cusp estimate](f2-uniform-normalized-cusp-remainder.md) gives

`|κ_s(a)−a^(1−2s)|≤C(1+Im s)^4 exp(π Im s) a`.

Gaussian spectral summability therefore bounds the logarithmic packet error by `D exp(−u/2)`. Write `B(u)=Σ_s c_s exp((2s−1/2)u)`. Retaining each individual spectral gap gives

`exp(−u/2)|B(u)|≤Σ_s |c_s|exp(−(1−2 Re s)u)`.

The right side is integrable on `u>0`: its integral is `Σ_s |c_s|/(1−2 Re s)`, finite because the reciprocal gap is at most `116 Im s`. Thus

`||Ψ|²−|B|²|≤2D exp(−u/2)|B|+D²exp(−u)`

is integrable. No common spectral gap is assumed.

At fixed `T≥0`, every pair mode on `[0,T]` is bounded by `|c_s c_t|exp(T)`. Absolute summability permits integration of the complete pair series. Zero exponents occur exactly at `t=s♯`; they contribute `T Σ_s c_s conjugate(c_(s♯))`. Every other integrated mode is the displayed counterterm. This argument requires no lower bound on nonzero pair exponents.

The integrable physical energy error disappears after division by `T`. The existing reflected window-coordinate identity identifies the remaining coefficient sum, including multiplicities, with half the Gaussian Weil energy. Its audited vanishing-damping limit proves the literal iterated physical-energy limit.

## Lean

Module: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.GaussianPhysicalCuspResidue`.

- `gaussianNormalizedCuspCore_summable`
- `gaussianCuspCounterterm_summable`
- `gaussianCuspEnergy_renormalized_mean`
- `gaussianWindowCuspEnergy_renormalized_mean`
- `tendsto_physicalCuspMean_weilQuad`

Individual `lake --old env lean` audit passed. All five declarations have exactly `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Imported by the RIT umbrella. Complete-Weil / PM Krein positivity remains open.
