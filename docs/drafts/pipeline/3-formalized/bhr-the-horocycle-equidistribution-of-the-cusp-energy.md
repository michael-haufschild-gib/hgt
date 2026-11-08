# BHR — long horocycles equidistribute the energy of a cusp mode

- **ID:** bhr-cusp-horocycle-equidistribution
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** queued item "horocycle equidistribution of `|g|²`" after the mean-square law (`bhr-the-mean-square-law-of-the-cusp-modes.md`).
- **Statement:** For `g ∈ S(λ)` with Whittaker coefficients `ρ(n)` (`ρ(0) = 0`),
  `m(y) = ∫_{−1/2}^{1/2} |g(x+iy)|² dx → (3/π) ∫_𝒟 |g|² dμ = ‖g‖²/vol(𝒟)` as `y → 0⁺`.

## Paper proof
1. *Parseval and pairing.* `m(y) = Σ_n |ρ(n)|² y K_ν(2π|n|y)² = Σ_{k≥0} f(k)·y k(ky)`, `f(k) = |ρ(k)|²+|ρ(−k)|²`,
   `k(u) = K_ν(2πu)²` (`K_ν` real for imaginary `ν`).
2. *Bessel bounds* (`ν = it`). `|K_ν(x)| ≤ M(x^{−1/4}+1)e^{−x}` (corpus log bound for `x < 1`, `|log x| ≤ 4x^{−1/4}`;
   corpus exponential bound for `x ≥ 1`). `|K_μ(x)| ≤ 2/x` for `|Re μ| ≤ 1`: the kernel is
   `≤ e^{−x cosh t}cosh t ≤ e^t e^{−xe^t/2}`, whose integral is `(2/x)e^{−x/2}`. Hence `|K_ν'| = ½|K_{ν+1}+K_{ν−1}| ≤ 2/x`
   and `|k'(u)| ≤ 4|K_ν(2πu)|/u`.
3. *Partial sums.* `S(t) = Σ_{k≤t} f(k)` satisfies `S(t)/t → A = (24/π²)cosh(πt)‖g‖²` (mean-square law, via
   `⌊t⌋+1`), `0 ≤ S(t) ≤ Ct`, `S = 0` on `[0,1)`.
4. *Abel summation* on `[½, N]` with `φ(t) = y k(ty)`, then `N → ∞` (`φ(N)S(N) ≤ C e² yN e^{−4πyN} → 0`; the integrand
   is `≤ const·e^{−2πyt}`): `m(y) = −∫_{1/2}^∞ y²k'(ty)S(t) dt`. Substituting `u = ty` and using `S = 0` on `(0, ½]`:
   `m(y) = −∫_0^∞ k'(u)·yS(u/y) du`.
5. *Dominated convergence.* `yS(u/y) → Au`; `|k'(u) yS(u/y)| ≤ 4C|K_ν(2πu)|`, integrable. So
   `m(y) → −A∫_0^∞ u k'(u) du`.
6. *Integration by parts.* `(u k(u))' = k + u k'`; `u k(u) ≤ 2M²((2π)^{−1/2}u^{1/2} + u) → 0` at `0`, `≤ e²u e^{−4πu} → 0` at `∞`;
   both terms integrable. So `∫ u k' = −∫ k`.
7. *Mellin.* `∫_0^∞ K_ν(2πu)² du = (2π)^{−1}G(1)`, `G(1) = ¼Γ(½)²Γ(½+it)Γ(½−it) = π²/(4cosh πt)`. Hence
   `m(y) → A·π/(8 cosh πt) = 3‖g‖²/π`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheHorocycleEquidistributionOfTheCuspEnergy.lean`, wired into
`BlackHoleRingdown.lean`, checked with `lake --old env lean`, no messages. Axioms of `tendsto_slice`: `propext`,
`Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspHE`) |
|---|---|
| 2 | `exists_norm_K_le`, `norm_K_le_two_div`, `norm_besKd_le`, `kk`, `kkd`, `hasDerivAt_kk`, `norm_kkd_le`, `norm_kk_le`, `integrableOn_rpow_exp` |
| 3 | `partialRS`, `partialRS_of_lt_one`, `tendsto_partialRS_div`, `exists_partialRS_le` |
| 1, 4 | `hasSum_slice_nat`, `abel_N`, `slice_eq_integral`, `integral_subst` |
| 5 | `tendsto_integral` |
| 6 | `integral_mul_kkd` |
| 7 | `gammaFactor_one`, `integral_kk` |
| main | `tendsto_slice` |

## Scope
The energy density of every cusp ringdown mode, sampled along the closed horocycle of height `y`, converges to its
spatial mean: quadratic observables of the modes thermalize along long horocycles. The corpus already has the
pseudo-Eisenstein (continuous-spectrum) case with rates (`TheHorocycleRateIsTheZeroFreeRegion`); this is the first
case for products of cusp forms. Not formalized: a rate. The Mellin transform is
`∫_0^∞ m(y)y^{s−2}dy = (2π)^{−s}G(s)Σ|ρ|²|n|^{−s} = 2Λ_g(s)/Λ(2s)` (C16, C17), so the rate is governed by the zeros of
`ζ(2s)` (and by `Λ_g` at them), which needs growth bounds of `Λ_g` in vertical strips.

## Log
- 2026-11-08 — created and formalized.
