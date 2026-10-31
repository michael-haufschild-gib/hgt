# A Weyl bump breaks size-only repair below 2/3

- **ID:** weyl-bump-size-floor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #11; `reboot-final.md` WP-B1
- **Statement:** `g(x) = cosh(Lx) + e^{θL}(1 + cos x)` is even, `≥ 1` on `ℝ`, and satisfies the
  two-profile size bound of `exists_norm_xiSliceProduct_le_two_profiles` (with `C = 2(1 + cosh R)`, any
  `c₂ ≤ 1`, whenever `θ ≤ 1/3 + 2η`) and the Euler-point bound `g^{(n)}(x₀) ≥ g(x₀)Lⁿ/4`. Its Gaussian
  heat at `κ/L` has nonnegative Taylor coefficients at `0` iff `κ ≥ 2θ` (for large `L`).

## Lean
Module `RHTower/Heat/AWeylBumpBreaksSizeOnlyRepair.lean` (namespace `RHTower.DeBruijn`):
`weylBumpModel`, `weylBumpModelC`, `weylBumpModelC_ofReal`, `one_le_weylBumpModel`,
`weylBumpModel_neg`, `norm_weylBumpModelC_le`, `norm_weylBumpModelC_le_two_profiles`,
`iteratedDeriv_cosh_mul`, `abs_iteratedDeriv_cos_sin_le`, `iteratedDeriv_weylBumpModel`,
`weylBumpModel_mul_pow_le_iteratedDeriv`, `weylBumpHeat`, `weylBumpHeat_eq`, `weylBumpHeatCoeff`,
`hasSum_weylBumpHeatCoeff`, `weylBumpHeatCoeff_nonneg`, `two_mul_le_add_of_hasSum_nonneg`,
`cos_le_one_sub_sq_div_four`, `not_exists_nonneg_hasSum_weylBumpHeat`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
1. **Size.** `‖g(a + ic)‖ ≤ cosh(La) + A(1 + cosh c)` and `g(½ + 2η) ≥ e^{L(½+2η)}/2`. The background
   is `≤ e^{L|a|} ≤ 2g(½+2η)e^{−L(η + c₂(½+η−|a|))}` because `(1 − c₂)(½ + η − |a|) ≥ 0`; the bump is
   `≤ 2g(½+2η)e^{−L(1/9 + (1/9)(½ − |a|))}` because `½ + 2η − θ ≥ 1/6 ≥ 1/9 + (1/9)(½ − |a|)`.
2. **Euler points.** `g^{(n)}(x₀) = (Lⁿe^{Lx₀} + (−L)ⁿe^{−Lx₀})/2 + A cos^{(n)}(x₀)`; with
   `e^{−Lx₀} ≤ e^{Lx₀}/7` (`Lx₀ ≥ 1`) and `12A ≤ e^{Lx₀}` this is `≥ g(x₀)Lⁿ/4`.
3. **Heat.** Gaussian moment generating function and cosine transform:
   `H(x) = e^{λL²/2}cosh(Lx) + A(1 + e^{−λ/2}cos x)`, coefficient of `x^{2m}`, `m ≥ 1`:
   `(e^{λL²/2}L^{2m} + (−1)^m A e^{−λ/2})/(2m)!`.
4. **Threshold.** At `λ = κ/L`, `A = e^{θL}`: for `κ ≥ 2θ`, `e^{κL/2}L^{2m} ≥ e^{θL} ≥ Ae^{−λ/2}`.
   For `κ < 2θ`, a nonnegative power series forces `H(y) + H(−y) ≥ 2H(0)`; at `y = 1/L`,
   `H(y) + H(−y) − 2H(0) ≤ 2e^{κL/2} − Ae^{−κ/(2L)}/(2L²) < 0` once `e^{(θ − κ/2)L} > 4L²e^{κ/2}`.

## What it changes (WP-B1)
With `θ = 1/3` the model meets both size-only inputs for every `η > 0` and large `L`, together with
positivity and evenness on the real axis, and has threshold `2/3`. So the size-only floor is
genuine: no argument from those inputs proves repair below `2/3 = 4μ(½)` (Weyl `μ(½) ≤ 1/6`). It is
attained: with the profile point `μ(11/18) ≤ 1/9`, repair holds at `2/3 + ε` for every `ε > 0`
(`size-only-repair-near-the-weyl-floor.md`); the two-piece method floor `27/40` is exact for its own
inputs (`a-signed-weyl-bump-attains-the-method-floor.md`). The obstruction
is a centre-concave defect: the heated `x²` coefficient `(e^{κL/2}L² − e^{θL−κ/(2L)})/2`. For the
slice of `ξ` the unheated `x²` coefficient is the Laguerre form `Ξ′(t)² − Ξ(t)Ξ″(t)`. A non-size
input that lowers the rate below `2/3` therefore has to bound the central Laguerre defect against the
centre size.
With the cosh model (programme card, B1: same inputs, threshold `δ/2`, `δ` up to `½`), the
size-only floor is at least `max(4μ(½), ¼)`.

## Log
- 2026-10-31 — created; proved; formalized.
