# BHR — the vertical decay of the Rankin–Selberg function

- **ID:** bhr-cusp-rankin-selberg-vertical-decay
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** "converse direction needs vertical growth bounds" of
  `bhr-the-horocycle-rate-of-the-cusp-energy-reads-the-zeros.md`.
- **Statement:** For `g ∈ S(λ)` let `Λ_g(s) = ∫_𝒟|g|²E*(s−½)` and `P_g(s) = s(s−½)(s−1)Λ_g(s)`.
  1. `P_g` extends to an entire function with `P_g(1−s) = −P_g(s)`.
  2. On `−¼ ≤ Re s ≤ 5/4`: `‖P_g(s)‖ ≤ C(1+|Im s|)^N e^{−π|Im s|}`; hence `‖Λ_g(s)‖ ≤ C(1+|Im s|)^N e^{−π|Im s|}` for
     `|Im s| ≥ 1`.

## Paper proof
1. *Entire.* `u(u²−¼)E*(u) = ((u−½)ξ(1+2u)/4)Y^{½+u} + ((u+½)ξ(2u)/4)Y^{½−u} + u(u²−¼)T(u)` (from
   `E* = Y^{½+u}ξ(1+2u)/((1+2u)2u) + ξ(2u)Y^{½−u}/(2u(2u−1)) + T`); the coefficients are entire, so the cusp
   domination (mean-square module) makes `∫_𝒟|g|²(...)` entire, and it equals `P_g` off `{0,½,1}`. Oddness: from
   `Λ_g(1−s) = Λ_g(s)` off three points, then density and continuity.
2. *Polynomial growth in the strip.* `|ξ(w)| ≤ C(1+|Im w|)^N` on `−3/2 ≤ Re w ≤ 5/2`: corpus strip bound on
   `[−½, 3/2]`, `ξ = w(w−1)/2·Γ_ℝ(w)ζ(w)` with `|Γ(w/2)| ≤ Γ(Re w/2)` and `|ζ| ≤ 3` on `[3/2, 5/2]`, the functional
   equation on `[−3/2, −½]`, compactness near the axis. The Whittaker tail is bounded uniformly in `Im u`. So
   `|P_g(s)| ≤ (|A₁|+|A₂|+|A₃|)·∫_𝒟|g|²(Y^{5/4}+2^{5/4}+2C_T) ≤ K(1+|Im s|)^N`.
3. *Decay on `Re s = 5/4`.* `P_g(s) = (s−1)/4·ξ(2s)G(s)·(2π)^{−s}Σ|ρ(n)|²|n|^{−s}` and
   `ξ(2s)G(s) = s(2s−1)π^{−s}ζ(2s)2^{s−3}Γ(s/2+ν)Γ(s/2)²Γ(s/2−ν)` (the `Γ(s)` cancels). On `Re = 5/8`,
   `|Γ(5/8+iy)| ≤ C(1+|y|)^N e^{−π|y|/2}` (corpus); `|T/2+t|+|T/2−t| ≥ |T|` gives total decay `e^{−π|T|}`.
   On `Re s = −¼` use oddness.
4. *Phragmén–Lindelöf* (Mathlib vertical strip, with the double-exponential growth class absorbing `e^{L|Im z|}`)
   for `F_ε(z) = P_g(z)e^{−iεπz}/(z+3)^N`, `ε = ±1`: bounded by `D·2^N` on both lines (`1+|Im z| ≤ 2|z+3|`), hence
   in the strip; choose `ε = sign Im s`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheVerticalDecayOfTheRankinSelbergFunction.lean`, wired into
`BlackHoleRingdown.lean`, checked with `lake --old env lean`, no messages. Axioms of `exists_norm_completedRS_le`,
`entireRS_one_sub`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspRSV`) |
|---|---|
| 1 | `pA₁`, `pA₂`, `pA₃`, `shape_entire_eq`, `entireRS`, `differentiable_entireRS`, `entireRS_eq`, `entireRS_one_sub` |
| 2 | `norm_mul_sub_one_le`, `exists_xi_bound_right`, `exists_xi_bound_wide`, `exists_shape_bound_uniform`, `exists_integral_bound`, `exists_entireRS_poly` |
| 3 | `xi_mul_gammaFactor`, `norm_tsum_rs_le`, `exists_entireRS_right` |
| 4 | `norm_le_of_strip`, `exists_norm_entireRS_le`, `exists_norm_completedRS_le` |

## Scope
The quadratic Eisenstein response of a cusp mode decays in frequency exactly at the rate of its Gamma factors:
`|Λ_g(σ+iT)| ≪ |T|^N e^{−π|T|}` across the critical strip, with no information on `ζ` needed. Dividing by
`Λ(2s) ≫ |T|^{−N}e^{−π|T|/2}|ζ(2s)|` makes the Mellin transform `2Λ_g(s)/Λ(2s)` of the horocycle energy decay like
`e^{−π|T|/2}` wherever `ζ(2s)` is controlled — the input for a horocycle rate. `norm_le_of_strip` is a reusable
Phragmén–Lindelöf form.

## Log
- 2026-11-08 — created and formalized.
