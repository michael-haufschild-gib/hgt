# BHR — the horocycle rate of the cusp energy reads the zeros

- **ID:** bhr-cusp-horocycle-rate-zeros
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** "Not formalized: a rate" of `bhr-the-horocycle-equidistribution-of-the-cusp-energy.md`; quadratic analogue of
  the corpus Zagier converse (`TheHorocycleReadsTheZeros.re_le_of_horocycle_rate`, pseudo-Eisenstein test functions).
- **Statement:** Let `g ∈ S(λ)`, `m(y) = ∫_{−1/2}^{1/2}|g(x+iy)|²dx`, `Λ_g(s) = ∫_𝒟|g|²E*(s−½)`. Suppose
  `|m(y) − c| ≤ C y^α` for `0 < y ≤ 1`. Then
  1. `Λ_g(s₀) = 0` for every `s₀` with `Re s₀ > 1 − α` and `ξ(2s₀) = 0`;
  2. `Λ_g(ρ/2) = 0` for every zero `ρ` of `ζ` with `Re ρ > max(0, 2 − 2α)`;
  3. contrapositive: if `ζ(ρ) = 0`, `Re ρ > 0` and `Λ_g(ρ/2) ≠ 0`, no rate `y^α` with `α > 1 − Re ρ/2` holds.

## Paper proof
1. For `Re s > 1`: `𝓜m(s−1) = ∫_0^∞ m(y)y^{s−2}dy = Σ_n|ρ(n)|²(2π|n|)^{−s}G(s) = (2π)^{−s}G(s)Σ|ρ(n)|²|n|^{−s}`
   (Rankin–Selberg unfolding), hence `Λ_g(s) = ξ(2s)/(2s(2s−1))·𝓜m(s−1)` for `Re s > 1`, `Im s ≠ 0`.
2. `m = c1_{(0,1]} + r`. `𝓜(c1_{(0,1]})(w) = c/w`. `r = O(y^α)` as `y → 0⁺` (hypothesis) and `r = m = O(e^{−2πy})` as
   `y → ∞` (`m ≤ Dye^{−4πy}`, `y ≤ e^{2πy}`); so `𝓜r` is holomorphic on `Re w > −α`.
3. `F(s) = ξ(2s)/(2s(2s−1))·(𝓜r(s−1) + c/(s−1))` is holomorphic on `{Re s > 1−α, Im s ≠ 0}`; `Λ_g` is holomorphic
   on `ℂ∖{0,½,1}`; they agree on `{Re s > 1, Im s ≠ 0}`. Each quarter plane `{Re s > 1−α, ±Im s > 0}` is convex,
   so `Λ_g = F` there (identity theorem from `max(1−α,1)+1 ± i`).
4. `ξ` has no real zeros, so a zero `s₀` of `ξ(2s)` lies in a quarter plane, and `Λ_g(s₀) = F(s₀) = 0`.
5. For `ζ(ρ) = 0`, `Re ρ > 0`: `ρ` is not trivial, so `ξ(ρ) = 0` (corpus correspondence); apply 4 at `s₀ = ρ/2`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheHorocycleRateOfTheCuspEnergyReadsTheZeros.lean`, wired into
`BlackHoleRingdown.lean`, checked with `lake --old env lean`, no messages. Axioms of `not_rate_of_ne_zero`:
`propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspHR`) |
|---|---|
| step 1 | `mass`, `continuousOn_mass`, `mellinConvergent_mass`, `mellin_mass`, `completedRS_eq_mellin` |
| (1) | `completedRS_eq_zero_of_rate` |
| (2) | `completedRS_half_eq_zero_of_rate` |
| (3) | `not_rate_of_ne_zero` |

## Scope
The equidistribution of a ringdown mode's energy along long horocycles is limited by the zeros of `ζ` that its
Rankin–Selberg function sees: a zero `ρ` with `Λ_g(ρ/2) ≠ 0` forbids every rate faster than `y^{1−Re ρ/2}`. On the
critical line this is `y^{3/4}`; a zero off the line visible to some `g` pushes the cap below `y^{3/4}`. The
converse direction (a zero-free region gives a rate) needs vertical growth bounds for `Λ_g(s)/Λ(2s)` and is not
formalized; nor is any non-vanishing of `Λ_g` at the points `ρ/2`.

## Log
- 2026-11-08 — created and formalized.
