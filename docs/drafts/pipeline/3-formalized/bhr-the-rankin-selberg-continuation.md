# BHR — the continuation of the Rankin–Selberg function of a cusp mode

- **ID:** bhr-cusp-rankin-selberg-continuation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** "Not formalized" item of `bhr-the-rankin-selberg-integral-of-the-cusp-modes.md`.
- **Statement:** Let `g ∈ S(λ)`, `E*(u; z) = ξ(1+2u) E(u; z)/((1+2u)(2u))` and
  `Λ_g(s) = ∫_𝒟 |g(z)|² E*(s − ½; z) dμ(z)`.
  1. `Λ_g` is holomorphic on `ℂ ∖ {0, ½, 1}`.
  2. `Λ_g(1 − s) = Λ_g(s)`.
  3. For `Re s > 1`, `Im s ≠ 0`: `Λ_g(s) = c(s) Σ_{n≠0} |ρ(n)|² |n|^{−s}`,
     `c(s) = ξ(2s)/(2s(2s−1)) · (2π)^{−s} G(s)`.
  4. `c` is holomorphic and nonvanishing on `Re s > ½`, so `Λ_g/c` is a holomorphic continuation of the
     Rankin–Selberg series to `{Re s > ½} ∖ {1}`.

## Paper proof
1. *Uniform cusp decay.* Fourier inversion at every `x ∈ (0,1]` (the `C²` periodic slice) and periodicity give
   `|g(x+iy)| ≤ Σ_n |a_n(y)| ≤ D√y e^{−2πy}` for `y ≥ 1`, every `x`.
2. *Tail bound.* For `|Re u| ≤ R`, `Y ≥ ½`: `|K_u(X)| ≤ e^{1−X} M_R` (`X ≥ 1`, `M_R = ∫ e^{−cosh t}cosh(Rt)dt`),
   `|c_N(u)| ≤ (N+1)^k`, and `√Y e^{1−2π(N+1)Y} ≤ e^{1+π}e^{−π(N+1)}`; the modes have a summable majorant uniform in
   `x, Y ≥ ½, u`. Hence the tail is bounded and, with `Y ↦ max(Y, ½)`, continuous in `z` (Weierstrass).
3. *Domination.* On a compact `K ⊂ ℂ∖{0, ±½}`: `|Y^w| ≤ Y^a + 2^a` (`Y ≥ ½`, `|Re w| ≤ a`), the coefficient functions
   are bounded and `|(1+2u)2u| ≥ m > 0`, so `|E*(u; x, Y)| ≤ αY^a + β` for `Y ≥ ½`. On `𝒟` (`Y > ½`),
   `|g|²(αY^a + β)` is bounded (by 1 and `y^n ≤ n!e^y`), and `𝒟` has finite volume.
4. *Holomorphy.* `s ↦ 1_𝒟|g|²E*(s−½)` is holomorphic on `ℂ∖{0,½,1}` (C15) and measurable (2); the corpus
   Cauchy-domination lemma gives (1).
5. *Functional equation:* `E*(−u) = E*(u)` (C15), pointwise.
6. *Identification:* for `Re s > 1`, `ξ(2s) ≠ 0` and `E* = E·ξ(2s)/(2s(2s−1))`; then C16.
7. *Continuation:* `ξ(2s) ≠ 0` for `Re 2s > 1`; the Gamma factors have positive real parts for `Re s > 0`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheRankinSelbergContinuation.lean`, wired into `BlackHoleRingdown.lean`,
checked with `lake --old env lean`, no messages. Axioms of `differentiableOn_completedRS`, `completedRS_one_sub`,
`rankinSelberg_continuation`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspRSC`) |
|---|---|
| decay | `hasSum_point`, `norm_fourier_eq_one`, `norm_point_le` |
| tail | `kMass`, `norm_besselK_le`, `summable_pow_exp`, `exists_term_bound`, `norm_weightedTail_le`, `continuous_weightedTail_max`, `continuous_completed_max` |
| domination | `norm_cpow_le`, `exists_completed_bound`, `exists_bound_on_fd` |
| (1) | `completedRS`, `differentiableOn_completedRS` |
| (2) | `completedRS_one_sub` |
| (3) | `completedRS_eq` |
| (4) | `rsFactor`, `differentiableAt_rsFactor`, `rsFactor_ne_zero`, `rankinSelberg_continuation` |

## Scope
The quadratic coupling of a cusp tone to the Eisenstein channel is a symmetric meromorphic function; on `Re s > ½`
the Rankin–Selberg series has at most the pole at `s = 1`. In `0 < Re s < ½` the continuation is `Λ_g/c` with
`c ∝ ξ(2s)`, so its possible poles there are the half-zeros `ρ/2` of `ζ`. Not formalized: the residue at `s = 1`
(`∝ ‖g‖²`), the identification at real `s`, and horocycle equidistribution of `|g|²` with a rate from the zeros.

## Log
- 2026-11-08 — created and formalized.
