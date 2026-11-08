# BHR — the horocycle rate of the cusp energy

- **ID:** bhr-cusp-horocycle-energy-rate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** forward direction left open in `bhr-the-horocycle-rate-of-the-cusp-energy-reads-the-zeros.md`; uses
  `bhr-the-vertical-decay-of-the-rankin-selberg-function.md`.
- **Statement:** For `g ∈ S(λ)`, `m(y) = ∫_{−1/2}^{1/2}|g(x+iy)|²dx`, `0 < ε < ½`, `y ∈ (0,1]`:
  1. `|m(y) − (3/π)‖g‖²| ≤ C y^{½−ε}`;
  2. under RH, `|m(y) − (3/π)‖g‖²| ≤ C y^{¾−ε}`;
  3. generally, if `ξ(z) ≠ 0` for `Re z > θ` (`0 ≤ θ ≤ 1`) and `1/ζ` is polynomially bounded on each
     `Re z ≥ θ + δ`, `|Im z| ≥ 2`, then `‖m(y) − c‖ ≤ C y^{1−θ/2−ε}`, `c = 4P_g(1)/ξ(2)`.

## Paper proof
1. *Mellin transform.* For `Re w > 0`: `𝓜(m − ce^{−y})(w) = 𝓜m(w) − cΓ(w)` and `𝓜m(w) = (2π)^{−s}G(s)Σ|ρ|²|n|^{−s}`
   (`s = w+1`) `= 4P_g(s)/((s−1)ξ(2s))` (for `Im w ≠ 0`, via `Λ_g = ξ(2s)/(2s(2s−1))·(...)` and `P_g = s(s−½)(s−1)Λ_g`).
   With `N(s) = 4P_g(s)/ξ(2s) − cΓ(s)` and `Γ(w+1) = wΓ(w)` this is `N(w+1)/w = Ψ(w)`, `Ψ = dslope N 1 (·+1)`
   (`N(1) = 0` by the choice of `c`).
2. *Regularity of `Ψ` on `θ/2 − 1 < Re w < ¼`.* `N` is holomorphic on `Re s > θ/2` (`P_g` entire, `ξ(2s) ≠ 0`),
   hence `Ψ`. For `|Im w| ≥ 1`: `ξ(2s) = s(2s−1)π^{−s}Γ(s)ζ(2s)`, so
   `|1/ξ(2s)| ≤ π²·|Γ(s)|^{−1}·|ζ(2s)|^{−1} ≪ (1+|t|)^{N}e^{π|t|/2}` (corpus `|Γ|^{−1}` bound on `[0,1]`, shifted by
   `Γ(s) = (s−1)Γ(s−1)` for `Re s ∈ (1, 5/4]`; hypothesis on `1/ζ`). With `|P_g| ≪ (1+|t|)^N e^{−π|t|}` and
   `|Γ(s)| ≪ |t|^N e^{−π|t|/2}`: `|Ψ(w)| ≤ |N(w+1)| ≪ |t|^N e^{−π|t|/2} ≪_K (1+t²)^{−K}`. Compact box for `|t| ≤ 1`.
3. *Inversion and shift.* `m − ce^{−y}` is Mellin-convergent at `Re w = 1/8`, its Mellin transform equals `Ψ` there
   off `t = 0`, so Mellin inversion gives `m(y) − ce^{−y} = 𝓜^{−1}_{1/8}Ψ(y) = 𝓜^{−1}_{c'}Ψ(y)`,
   `c' = θ/2 − 1 + ε`, and `|𝓜^{−1}_{c'}Ψ(y)| ≤ (2π)^{−1}y^{−c'}∫|Ψ(c'+it)|dt`. Finally `|c||e^{−y} − 1| ≤ |c|y`.
4. *Constant.* A rate `y^γ`, `γ > 0`, gives `m → c`; equidistribution gives `m → (3/π)‖g‖²`.
5. `θ = 1`: `ξ ≠ 0` on `Re > 1`, `|1/ζ| ≤ 1 + 1/δ`. `θ = ½` under RH: corpus `exists_invZeta_shift_data_of_rh`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheHorocycleRateOfTheCuspEnergy.lean`, wired into
`BlackHoleRingdown.lean`, checked with `lake --old env lean`, no messages. Axioms of `horocycle_energy_rate`,
`horocycle_energy_rate_of_RH`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspHRate`) |
|---|---|
| 1 | `rateConst`, `poleNum`, `regPart`, `poleNum_one`, `regPart_eq`, `mellin_eq_regPart` |
| 2 | `xi_two_mul_eq_gamma`, `exists_norm_inv_Gamma_le`, `differentiableOn_poleNum`, `differentiableAt_regPart`, `mellinRegularStrip_regPart` |
| 3 (general θ) | `norm_mass_sub_le_of_zeroFree` |
| 4 | `rateConst_eq` |
| (1), (2) | `horocycle_energy_rate`, `horocycle_energy_rate_of_RH` |

## Scope
The energy of every cusp ringdown mode equidistributes along long horocycles at the square-root rate
unconditionally and at `y^{3/4−ε}` under RH. With `not_rate_of_ne_zero` this is a quadratic Zagier dichotomy:
under RH every cusp energy reaches `y^{3/4−ε}`; an off-line zero `ρ` with `Λ_g(ρ/2) ≠ 0` keeps `g` below
`y^{1−Re ρ/2}`. Whether every zero is visible to some `Λ_g` (non-vanishing of `Λ_g(ρ/2)` for some `g`) is not
known; it is the missing step to an equivalence with RH.

## Log
- 2026-11-08 — created and formalized.
