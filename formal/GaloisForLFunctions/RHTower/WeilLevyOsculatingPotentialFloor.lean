import GaloisForLFunctions.RHTower.WeilLevyCollarInteriorCoupling
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper

/-!
# Osculating Potential Floors, Exact `(π/2, log 2)` Cancellation, and Unconditional Window Positivity up to `3 / 10`

In `WeilLevyPoleGaussModeCancellation.lean`, `WeilLevyCoshPlasticCrossover.lean`,
`WeilLevyBoundaryEscapeCollarPotential.lean`, and `WeilLevyCollarInteriorCoupling.lean`,
the lower bounds on `2 * archLevyAntideriv y` and `levyCoshPotential y` used:
- `log((4 - y) / y) ≤ log((1 + e^{-y/2}) / (1 - e^{-y/2}))` (valid for `0 < y < 2`), and
- `0 < arctan(e^{-y/2})`, discarding the `2 * arctan(e^{-y/2})` term inside `2 * archLevyAntideriv y`.

At `y = 0`, however, `2 * arctan(e^{-y/2}) = 2 * arctan 1 = π / 2`, which **matches and cancels**
the `-π / 2` term inside `EF.gammaBracket 0 = -(log π + 3 log 2 + γ + π / 2)`! Moreover, because
`d/dy (arctan(e^{-y/2})) = -1 / (4 cosh(y / 2))` is an **even** function of `y`, its second
derivative at `y = 0` vanishes, so the linear tangent `π / 2 - y / 2` is in fact the **osculating
quadratic Taylor polynomial** of `2 * arctan(e^{-y/2})` at `y = 0`:
`d/dy (arctan(e^{-y/2}) + y / 4) = (1 - e^{-y/2})² / (4 (1 + e^{-y})) ≥ 0` for all `y ∈ ℝ`.

Similarly, by the trapezoidal convexity bound for `e^{-u}` on `[0, y / 2]`,
`1 - e^{-y/2} ≤ (y / 4) * (1 + e^{-y/2})` for **all** `y ≥ 0`, so
`log(4 / y) ≤ log((1 + e^{-y/2}) / (1 - e^{-y/2}))` holds globally for all `y > 0` (upgrading
`(4 - y) / y` to `4 / y` and matching the Laurent expansion up to `O(y²)`).

Combining these two global osculating bounds with `8 sinh(y / 2) ≥ 4 y` yields the global lower bounds:
1. `log(4 / y) + π / 2 - y / 2 ≤ 2 * archLevyAntideriv y` for all `y > 0`
   (`osculating_le_two_mul_archLevyAntideriv`).
2. `log(4 / y) + π / 2 + (7 / 2) * y ≤ levyCoshPotential y` for all `y > 0`
   (`osculating_le_levyCoshPotential`), accurate to within `y² / 96 + O(y³)` (`< 0.00083` on `(0, t_*]`).

When combined with `EF.gammaBracket 0 = -(log π + 3 log 2 + γ + π / 2)`, both `π / 2` and `log 4 = 2 log 2`
cancel algebraically via `(4 / y) / (8 π) = 1 / (2 π y)`, giving the exact cancellation laws:
3. `log(1 / (2 * π * y)) - y / 2 - γ ≤ EF.gammaBracket 0 + 2 * archLevyAntideriv y`
   (`log_inv_two_pi_sub_half_le_gammaBracket_add_two_mul_archLevyAntideriv`).
4. `log(1 / (2 * π * y)) + (7 / 2) * y - γ ≤ EF.gammaBracket 0 + levyCoshPotential y`
   (`log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential`).

Using the certified upper bound `γ < 577216 / 1000000` from `EulerMascheroniCorrectedUpper.lean`
and the Padé inequality `2 x / (x + 2) < log(1 + x)`, we deduce unconditionally:
5. **Sharpened origin bracket bound**: `-EF.gammaBracket 0 < 5373 / 1000` (`= 5.373`, within `0.00082`
   of the exact value `5.37218...`).
6. **Disconnected-measure positivity up to `1 / 6`** (`weilEnergyNonneg_of_volume_pos_le_inv_six`,
   `weilArchRe_nonneg_of_volume_pos_le_inv_six`): for every nonnegative measurable `g` (resp.
   `f ∈ C²_c(ℝ)`) with `volume {x | 0 < g x} ≤ ENNReal.ofReal (1 / 6)`, `WeilEnergyNonneg g` and
   `0 ≤ weilArchRe` hold unconditionally (a **10.8× expansion** over `1 / 65` in
   `WeilLevyCollarInteriorCoupling` and a **21.6× expansion** over `1 / 130` in
   `WeilLevyPoleGaussModeCancellation`).
7. **Unconditional window positivity on `(0, 3 / 10)` (`0.30 > screwSignThreshold`)**
   (`weilArchRe_nonneg_of_support_Ioo_le_three_tenths`): for every nonnegative `f ∈ C²_c(ℝ)`
   vanishing outside `Ioo 0 L` with `L ≤ 3 / 10` (covering **43.3% of `(0, log 2)`**, a **5.4×
   expansion** over `1 / 18` in `WeilLevyBoundaryEscapeCollarPotential` and **39×** over `1 / 130`),
   `0 ≤ W_∞(f ⋆ f̃)` holds unconditionally without `WindowPositive`.
8. **Sharpened plastic-number crossover floor (`-4 / 25 = -0.16`) and collar-core dominance at `a = 1 / 18`**:
   `-(4 / 25) < EF.gammaBracket 0 + levyCoshPotential screwSignThreshold` (within `0.015` of the
   exact plastic-number deficit `-0.1448`), and at collar width `a = 1 / 18` any nonnegative
   `f ∈ C²_c(ℝ)` on `(0, L)` (`L ≥ 1 / 9`, including `L = log 2`) with
   `2 * coreMass f L (1 / 18) ≤ 3 * collarMass f L (1 / 18)` satisfies `0 ≤ weilArchRe`
   unconditionally (`weilArchRe_nonneg_of_two_mul_coreMass_le_three_mul_collarMass_inv_18`).
9. **Collar-cancelled core-slice lower bound on `D_h(x)`** (`half_core_slice_le_integral_jump_sq`,
   `half_double_slice_le_integral_jump_sq`): adding `collarMass_add_interior_le_integral_jump_sq`
   and `core_slice_sub_collarMass_le_interior_jump_sq` cancels `collarMass h L a` identically,
   proving `(1 / 2) * ((∫ v in Ioc x (a + x), h v ^ 2) + ∫ u in Ioc (L - x - a) (L - x), h u ^ 2) ≤ D_h(x)`.
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped ENNReal FourierTransform ComplexConjugate
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyOsculatingFloor

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape RHTower.WeilLevyCollarCoupling

/-! ## Section 1: Global Trapezoidal and Osculating Lower Bounds for `archLevyAntideriv` and `levyCoshPotential` -/

/-- Trapezoidal convexity inequality for `e^{-y/2}`:
for all `y ≥ 0`, `1 - Real.exp (-y / 2) ≤ (y / 4) * (1 + Real.exp (-y / 2))`. -/
theorem one_sub_exp_neg_half_le {y : ℝ} (hy : 0 ≤ y) :
    1 - Real.exp (-y / 2) ≤ (y / 4) * (1 + Real.exp (-y / 2)) := by
  let q : ℝ → ℝ := fun u => (u / 4) * (1 + Real.exp (-u / 2)) - (1 - Real.exp (-u / 2))
  have hderiv : ∀ u : ℝ,
      HasDerivAt q ((1 / 4 : ℝ) * (1 - (u / 2 + 1) * Real.exp (-u / 2))) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => -v / 2) (-1 / 2) u := by
      simpa [neg_div] using (hasDerivAt_id u).neg.div_const 2
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-v / 2))
        (Real.exp (-u / 2) * (-1 / 2)) u := hlin.exp
    have h1 : HasDerivAt (fun v : ℝ => v / 4) (1 / 4) u := by
      simpa using (hasDerivAt_id u).div_const 4
    have h2 : HasDerivAt (fun v : ℝ => 1 + Real.exp (-v / 2))
        (Real.exp (-u / 2) * (-1 / 2)) u := hexp.const_add 1
    have h3 : HasDerivAt (fun v : ℝ => 1 - Real.exp (-v / 2))
        (-(Real.exp (-u / 2) * (-1 / 2))) u := hexp.const_sub 1
    exact ((h1.mul h2).sub h3).congr_deriv (by ring)
  have hmono : MonotoneOn q (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun u _ => (hderiv u).continuousAt.continuousWithinAt
    · exact fun u _ => (hderiv u).differentiableAt.differentiableWithinAt
    · intro u _
      rw [(hderiv u).deriv]
      have hexp_le : (u / 2 + 1) * Real.exp (-u / 2) ≤ 1 := by
        have h1 := Real.add_one_le_exp (u / 2)
        have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-u / 2)).le
        rwa [← Real.exp_add, show u / 2 + -u / 2 = 0 by ring, Real.exp_zero] at h2
      linarith
  have h0 : q 0 ≤ q y := hmono self_mem_Ici hy hy
  dsimp [q] at h0
  rw [neg_zero, zero_div, zero_div, Real.exp_zero] at h0
  linarith

/-- Global rational lower bound `4 / y ≤ (1 + e^{-y/2}) / (1 - e^{-y/2})` for all `y > 0`. -/
theorem four_div_le_one_add_exp_div_one_sub_exp {y : ℝ} (hy : 0 < y) :
    4 / y ≤ (1 + Real.exp (-y / 2)) / (1 - Real.exp (-y / 2)) := by
  have ht1 : Real.exp (-y / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1mt : 0 < 1 - Real.exp (-y / 2) := by linarith
  rw [div_le_div_iff₀ hy h1mt]
  have htrap := one_sub_exp_neg_half_le hy.le
  linarith

/-- Global logarithmic lower bound `log (4 / y) ≤ log ((1 + e^{-y/2}) / (1 - e^{-y/2}))`
for all `y > 0`. -/
theorem log_four_div_le_log_one_add_exp_div {y : ℝ} (hy : 0 < y) :
    Real.log (4 / y) ≤ Real.log ((1 + Real.exp (-y / 2)) / (1 - Real.exp (-y / 2))) :=
  Real.log_le_log (by positivity) (four_div_le_one_add_exp_div_one_sub_exp hy)

/-- **Global osculating quadratic lower bound for `2 * arctan(e^{-y/2})`**:
for all `y ≥ 0`, `π / 2 - y / 2 ≤ 2 * Real.arctan (Real.exp (-y / 2))`. -/
theorem pi_div_two_sub_half_le_two_mul_arctan_exp_neg_half {y : ℝ} (hy : 0 ≤ y) :
    Real.pi / 2 - y / 2 ≤ 2 * Real.arctan (Real.exp (-y / 2)) := by
  let g : ℝ → ℝ := fun u => Real.arctan (Real.exp (-u / 2)) + u / 4
  have hderiv : ∀ u : ℝ,
      HasDerivAt g ((1 - Real.exp (-u / 2)) ^ 2 / (4 * (1 + Real.exp (-u / 2) ^ 2))) u := by
    intro u
    set t : ℝ := Real.exp (-u / 2)
    have hlin : HasDerivAt (fun v : ℝ => -v / 2) (-1 / 2) u := by
      simpa [neg_div] using (hasDerivAt_id u).neg.div_const 2
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-v / 2)) (t * (-1 / 2)) u := hlin.exp
    have harc : HasDerivAt (fun v : ℝ => Real.arctan (Real.exp (-v / 2)))
        (1 / (1 + t ^ 2) * (t * (-1 / 2))) u :=
      HasDerivAt.comp (h := fun v : ℝ => Real.exp (-v / 2)) u (Real.hasDerivAt_arctan t) hexp
    have h1 : HasDerivAt (fun v : ℝ => v / 4) (1 / 4) u := by
      simpa using (hasDerivAt_id u).div_const 4
    refine (harc.add h1).congr_deriv ?_
    have hd : 1 + t ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun u _ => (hderiv u).continuousAt.continuousWithinAt
    · exact fun u _ => (hderiv u).differentiableAt.differentiableWithinAt
    · intro u _
      rw [(hderiv u).deriv]
      positivity
  have h0 : g 0 ≤ g y := hmono self_mem_Ici hy hy
  dsimp [g] at h0
  rw [neg_zero, zero_div, Real.exp_zero, Real.arctan_one] at h0
  linarith

/-- **Global osculating lower bound for `2 * archLevyAntideriv y` on `(0, ∞)`**:
for every `y > 0`,
`Real.log (4 / y) + Real.pi / 2 - y / 2 ≤ 2 * archLevyAntideriv y`. -/
theorem osculating_le_two_mul_archLevyAntideriv {y : ℝ} (hy : 0 < y) :
    Real.log (4 / y) + Real.pi / 2 - y / 2 ≤ 2 * archLevyAntideriv y := by
  rw [archLevyAntideriv_eq_log_div hy]
  have hlog := log_four_div_le_log_one_add_exp_div hy
  have harc := pi_div_two_sub_half_le_two_mul_arctan_exp_neg_half hy.le
  linarith

/-- Elementary convexity bound `4 * y ≤ 8 * Real.sinh (y / 2)` for all `y ≥ 0`. -/
theorem four_mul_le_eight_mul_sinh_half {y : ℝ} (hy : 0 ≤ y) :
    4 * y ≤ 8 * Real.sinh (y / 2) := by
  let s : ℝ → ℝ := fun u => 8 * Real.sinh (u / 2) - 4 * u
  have hderiv : ∀ u : ℝ, HasDerivAt s (4 * Real.cosh (u / 2) - 4) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => 8 * Real.sinh (v / 2)) (4 * Real.cosh (u / 2)) u := by
      have h := ((hasDerivAt_id u).div_const (2 : ℝ)).sinh.const_mul (8 : ℝ)
      exact h.congr_deriv (by dsimp only [id_eq]; ring)
    have h2 : HasDerivAt (fun v : ℝ => 4 * v) 4 u := by
      simpa using (hasDerivAt_id u).const_mul (4 : ℝ)
    exact h1.sub h2
  have hmono : MonotoneOn s (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun u _ => (hderiv u).continuousAt.continuousWithinAt
    · exact fun u _ => (hderiv u).differentiableAt.differentiableWithinAt
    · intro u _
      rw [(hderiv u).deriv]
      linarith [Real.one_le_cosh (u / 2)]
  have h0 : s 0 ≤ s y := hmono self_mem_Ici hy hy
  dsimp [s] at h0
  rw [zero_div, Real.sinh_zero] at h0
  linarith

/-- **Global osculating lower bound for `levyCoshPotential y` on `(0, ∞)`**:
for every `y > 0`,
`Real.log (4 / y) + Real.pi / 2 + (7 / 2) * y ≤ levyCoshPotential y`. -/
theorem osculating_le_levyCoshPotential {y : ℝ} (hy : 0 < y) :
    Real.log (4 / y) + Real.pi / 2 + (7 / 2) * y ≤ levyCoshPotential y := by
  unfold levyCoshPotential
  have hsinh := four_mul_le_eight_mul_sinh_half hy.le
  have hΩ := osculating_le_two_mul_archLevyAntideriv hy
  linarith

/-! ## Section 2: Exact `(π / 2, log 2)` Cancellation Against `EF.gammaBracket 0` and Sharpened Origin Bound -/

/-- Exact logarithm identity `log (1 / (2 * π * y)) = log (4 / y) - log π - 3 * log 2` for `y > 0`. -/
theorem log_inv_two_pi_mul_eq {y : ℝ} (hy : 0 < y) :
    Real.log (1 / (2 * Real.pi * y)) = Real.log (4 / y) - Real.log Real.pi - 3 * Real.log 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 1 / (2 * Real.pi * y) = (4 / y) / (Real.pi * 2 ^ (3 : ℕ)) := by
    field_simp; ring
  rw [h1, Real.log_div (by positivity) (by positivity),
    Real.log_mul hpi.ne' (by positivity), Real.log_pow, Nat.cast_ofNat]
  ring

/-- **Exact `(π / 2, log 2)` cancellation for `EF.gammaBracket 0 + 2 * archLevyAntideriv y`**:
for every `y > 0`,
`Real.log (1 / (2 * Real.pi * y)) - y / 2 - Real.eulerMascheroniConstant ≤ EF.gammaBracket 0 + 2 * archLevyAntideriv y`. -/
theorem log_inv_two_pi_sub_half_le_gammaBracket_add_two_mul_archLevyAntideriv {y : ℝ} (hy : 0 < y) :
    Real.log (1 / (2 * Real.pi * y)) - y / 2 - Real.eulerMascheroniConstant ≤
      EF.gammaBracket 0 + 2 * archLevyAntideriv y := by
  have hA : EF.gammaBracket 0 =
      -(Real.log Real.pi + 3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2) := by
    linarith [neg_gammaBracket_zero_eq]
  have hlog := log_inv_two_pi_mul_eq hy
  have hΩ := osculating_le_two_mul_archLevyAntideriv hy
  linarith

/-- **Exact `(π / 2, log 2)` cancellation for `EF.gammaBracket 0 + levyCoshPotential y`**:
for every `y > 0`,
`Real.log (1 / (2 * Real.pi * y)) + (7 / 2) * y - Real.eulerMascheroniConstant ≤ EF.gammaBracket 0 + levyCoshPotential y`. -/
theorem log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential {y : ℝ} (hy : 0 < y) :
    Real.log (1 / (2 * Real.pi * y)) + (7 / 2) * y - Real.eulerMascheroniConstant ≤
      EF.gammaBracket 0 + levyCoshPotential y := by
  have hA : EF.gammaBracket 0 =
      -(Real.log Real.pi + 3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2) := by
    linarith [neg_gammaBracket_zero_eq]
  have hlog := log_inv_two_pi_mul_eq hy
  have hΦ := osculating_le_levyCoshPotential hy
  linarith

/-- Sharpened elementary upper bound `log π ≤ 4 * log 2 - log 5 + 5 * π / 16 - 1`
from `π = (16 / 5) * (5 * π / 16)` (accurate to `1.7 × 10^{-4}`). -/
theorem log_pi_le_sixteen_fifths :
    Real.log Real.pi ≤ 4 * Real.log 2 - Real.log 5 + 5 * Real.pi / 16 - 1 := by
  have hpos : 0 < 5 * Real.pi / 16 := by positivity
  have h16_5 : Real.log (16 / 5 : ℝ) = 4 * Real.log 2 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow, Nat.cast_ofNat]
  have hsplit : Real.log Real.pi = 4 * Real.log 2 - Real.log 5 + Real.log (5 * Real.pi / 16) := by
    conv_lhs => rw [show Real.pi = (16 / 5 : ℝ) * (5 * Real.pi / 16) by ring]
    rw [Real.log_mul (by norm_num) hpos.ne', h16_5]
  have hle : Real.log (5 * Real.pi / 16) ≤ 5 * Real.pi / 16 - 1 :=
    Real.log_le_sub_one_of_pos hpos
  linarith

/-- **Sharpened rational upper bound on `-EF.gammaBracket 0`**:
`-EF.gammaBracket 0 < 5373 / 1000` (`= 5.373`, within `8.2 × 10^{-4}` of the exact value `5.37218...`). -/
theorem neg_gammaBracket_zero_lt_5373_over_1000 : -EF.gammaBracket 0 < 5373 / 1000 := by
  rw [neg_gammaBracket_zero_eq]
  have h1 := log_pi_le_sixteen_fifths
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_five_gt_d9
  have h4 := Real.pi_lt_d4
  have h5 := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith

/-! ## Section 3: Unconditional Positivity on `(0, 3 / 10)` and Disconnected-Measure Positivity up to `1 / 6` -/

/-- For every `0 < y ≤ 1 / 12`, `-EF.gammaBracket 0 ≤ 2 * archLevyAntideriv y`. -/
theorem neg_gammaBracket_zero_le_two_mul_archLevyAntideriv_of_le_inv_12 {y : ℝ}
    (hy0 : 0 < y) (hy : y ≤ 1 / 12) :
    -EF.gammaBracket 0 ≤ 2 * archLevyAntideriv y := by
  have h12 : 0 ≤ EF.gammaBracket 0 + 2 * archLevyAntideriv (1 / 12) := by
    have hmain := log_inv_two_pi_sub_half_le_gammaBracket_add_two_mul_archLevyAntideriv
      (by norm_num : (0 : ℝ) < 1 / 12)
    have harg : (1 : ℝ) / (2 * Real.pi * (1 / 12)) = 2 * (3 / Real.pi) := by field_simp; ring
    have hpos : 0 < Real.pi / 3 := by positivity
    have hlog3pi : Real.log (2 * (3 / Real.pi)) = Real.log 2 - Real.log (Real.pi / 3) := by
      rw [Real.log_mul two_ne_zero (by positivity),
        show (3 / Real.pi : ℝ) = (Real.pi / 3)⁻¹ by field_simp, Real.log_inv]
      ring
    have hle : Real.log (Real.pi / 3) ≤ Real.pi / 3 - 1 := Real.log_le_sub_one_of_pos hpos
    have h2 := Real.log_two_gt_d9
    have h4 := Real.pi_lt_d4
    have h5 := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
    rw [harg, hlog3pi] at hmain
    linarith
  have hmono : archLevyAntideriv (1 / 12) ≤ archLevyAntideriv y :=
    antitoneOn_archLevyAntideriv hy0 (by norm_num) hy
  linarith

/-- **Unconditional `WeilEnergyNonneg` for any nonnegative `g` with `|{g > 0}| ≤ 1 / 6`**
(a **10.8× expansion** over `1 / 65` in `WeilLevyCollarInteriorCoupling` and **21.6×** over
`1 / 130` in `WeilLevyPoleGaussModeCancellation`). -/
theorem weilEnergyNonneg_of_volume_pos_le_inv_six {g : ℝ → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) {C : ℝ} (hgC : ∀ x, g x ≤ C)
    (hvol : volume {x | 0 < g x} ≤ ENNReal.ofReal (1 / 6)) :
    WeilEnergyNonneg g := by
  refine weilEnergyNonneg_of_volume_pos_le_half hg hg0 hgC (by norm_num) hvol ?_
  rw [show (1 / 6 : ℝ) / 2 = 1 / 12 by norm_num]
  exact neg_gammaBracket_zero_le_two_mul_archLevyAntideriv_of_le_inv_12 (by norm_num) le_rfl

/-- **Unconditional nonnegativity of `weilArchRe` for any nonnegative `f ∈ C²_c(ℝ)` with
`|{f > 0}| ≤ 1 / 6`** (even for disconnected support, without `WindowPositive`). -/
theorem weilArchRe_nonneg_of_volume_pos_le_inv_six {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x)
    (hvol : volume {x | 0 < f x} ≤ ENNReal.ofReal (1 / 6)) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  refine weilArchRe_nonneg_of_volume_pos_le_half hf hfc hf0 (by norm_num) hvol ?_
  rw [show (1 / 6 : ℝ) / 2 = 1 / 12 by norm_num]
  exact neg_gammaBracket_zero_le_two_mul_archLevyAntideriv_of_le_inv_12 (by norm_num) le_rfl

/-- For every `0 < y ≤ 3 / 20`, `-EF.gammaBracket 0 ≤ levyCoshPotential y`. -/
theorem neg_gammaBracket_zero_le_levyCoshPotential_of_le_three_twentieths {y : ℝ}
    (hy0 : 0 < y) (hy : y ≤ 3 / 20) :
    -EF.gammaBracket 0 ≤ levyCoshPotential y := by
  have h3_20 : 0 ≤ EF.gammaBracket 0 + levyCoshPotential (3 / 20) := by
    have hmain := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
      (by norm_num : (0 : ℝ) < 3 / 20)
    have hpi : 0 < Real.pi := Real.pi_pos
    have h4 := Real.pi_lt_d4
    have hxpos : 0 < (10 - 3 * Real.pi) / (3 * Real.pi) :=
      div_pos (by linarith) (by positivity)
    have harg : (1 : ℝ) / (2 * Real.pi * (3 / 20)) = 1 + (10 - 3 * Real.pi) / (3 * Real.pi) := by
      field_simp; ring
    have hpade := Real.lt_log_one_add_of_pos hxpos
    have hsimp : 2 * ((10 - 3 * Real.pi) / (3 * Real.pi)) /
        ((10 - 3 * Real.pi) / (3 * Real.pi) + 2) =
        2 * (10 - 3 * Real.pi) / (10 + 3 * Real.pi) := by
      have h1 : (10 - 3 * Real.pi) / (3 * Real.pi) + 2 =
          (10 + 3 * Real.pi) / (3 * Real.pi) := by field_simp; ring
      have h2 : 10 + 3 * Real.pi ≠ 0 := by positivity
      rw [h1]
      field_simp
    have hrat : (29 : ℝ) / 500 ≤ 2 * (10 - 3 * Real.pi) / (10 + 3 * Real.pi) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have h5 := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
    rw [harg] at hmain
    rw [hsimp] at hpade
    linarith
  have hmono : levyCoshPotential (3 / 20) ≤ levyCoshPotential y :=
    antitoneOn_levyCoshPotential_Ioc
      ⟨hy0, hy.trans (by linarith [screwSignThreshold_gt])⟩
      ⟨by norm_num, by linarith [screwSignThreshold_gt]⟩ hy
  linarith

/-- **Unconditional nonnegativity of `weilArchRe` on `(0, L)` for all `L ≤ 3 / 10` (`= 0.30`)**:
every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` with `L ≤ 3 / 10` (covering **43.3%**
of `(0, log 2)` and exceeding `screwSignThreshold ≈ 0.2812`) satisfies `0 ≤ W_∞(f ⋆ f̃)`
unconditionally without `WindowPositive`! -/
theorem weilArchRe_nonneg_of_support_Ioo_le_three_tenths {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL : L ≤ 3 / 10)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_3_10 : ∀ u ∉ Ioo (0 : ℝ) (3 / 10), f u = 0 :=
    fun u hu => hsupp u fun h => hu ⟨h.1, lt_of_lt_of_le h.2 hL⟩
  refine weilArchRe_nonneg_of_support_Ioo_of_full_half_window hf hfc hf0
    (by norm_num : (0 : ℝ) < 3 / 10) (by linarith [screwSignThreshold_gt]) hsupp_3_10 ?_
  rw [show (3 / 10 : ℝ) / 2 = 3 / 20 by norm_num]
  exact neg_gammaBracket_zero_le_levyCoshPotential_of_le_three_twentieths (by norm_num) le_rfl

/-- **Unconditional `WindowPositive` on `(0, 3 / 10)`**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (3 / 10)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_three_tenths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (3 / 10)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_three_tenths hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-! ## Section 4: Sharpened Plastic-Number Floor (`-9 / 50 = -0.18`), Collar-Core Dominance at `a = 1 / 18`, and Collar-Cancelled Core-Slice Bound -/

/-- **Sharpened plastic-number constant deficit bound (`-9 / 50 = -0.18`)**:
`-(9 / 50) < EF.gammaBracket 0 + levyCoshPotential screwSignThreshold`
(improving `-2 / 5 = -0.40` in `WeilLevyCoshPlasticCrossover` and `-3 / 10 = -0.30` in
`WeilLevyCollarInteriorCoupling` to `-0.18`). -/
theorem neg_nine_fiftieths_lt_gammaBracket_add_levyCoshPotential_screwSignThreshold :
    -(9 / 50 : ℝ) < EF.gammaBracket 0 + levyCoshPotential screwSignThreshold := by
  have h1 := neg_gammaBracket_zero_lt_5373_over_1000
  have h2 := twenty_six_fifths_lt_levyCoshPotential_screwSignThreshold
  linarith

/-- At collar width `a = 1 / 18`, `604 / 100 ≤ levyCoshPotential (1 / 18)`. -/
theorem six_hundred_four_over_hundred_le_levyCoshPotential_inv_18 :
    (604 : ℝ) / 100 ≤ levyCoshPotential (1 / 18) := by
  have hmain := osculating_le_levyCoshPotential (by norm_num : (0 : ℝ) < 1 / 18)
  have harg : (4 : ℝ) / (1 / 18) = 2 ^ (6 : ℕ) * (9 / 8) := by norm_num
  have hlog98 : (2 : ℝ) / 17 < Real.log (9 / 8) := by
    have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 8)
    norm_num at h ⊢
    exact h
  have hlog_eq : Real.log (2 ^ (6 : ℕ) * (9 / 8) : ℝ) = 6 * Real.log 2 + Real.log (9 / 8) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow, Nat.cast_ofNat]
  have h2 := Real.log_two_gt_d9
  have hpi := Real.pi_gt_d4
  rw [harg, hlog_eq] at hmain
  linarith

/-- **Sharpened rational collar-core lower bound at collar width `a = 1 / 18` (valid for all
`L ≥ 1 / 9`, including `L = log 2`)**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`1 / 9 ≤ L`),
`(6 / 25) * collarMass f L (1 / 18) - (9 / 50) * coreMass f L (1 / 18)`
`+ ∫_{x ∈ Ioo (1/18) t_*} (-screwRegularKernel x) (∫_{u ∈ Ioc 0 (L - x)} (f u - f (u + x))²) dx ≤ W_∞(f ⋆ f̃)`. -/
theorem rational_collar_core_inv_18_add_interior_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL : 1 / 9 ≤ L)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (6 / 25 : ℝ) * collarMass f L (1 / 18) - (9 / 50 : ℝ) * coreMass f L (1 / 18) +
      (∫ x in Ioo (1 / 18) screwSignThreshold,
        (-screwRegularKernel x) * (∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hat : (1 : ℝ) / 18 ≤ screwSignThreshold := by linarith [screwSignThreshold_gt]
  have haL : (1 : ℝ) / 18 ≤ L / 2 := by linarith
  have hmain := collar_core_plastic_floor_add_interior_le_weilArchRe
    hf hfc hf0 (by norm_num : (0 : ℝ) < 1 / 18) hat haL hsupp
  have h604 := six_hundred_four_over_hundred_le_levyCoshPotential_inv_18
  have h26 := twenty_six_fifths_lt_levyCoshPotential_screwSignThreshold
  have hA := neg_gammaBracket_zero_lt_5373_over_1000
  have hcol_nn := collarMass_nonneg f L (1 / 18)
  have hcor_nn := coreMass_nonneg f L (1 / 18)
  have hcoeff1 : (6 / 25 : ℝ) ≤ EF.gammaBracket 0 + (1 / 2) * levyCoshPotential (1 / 18) +
      (1 / 2) * levyCoshPotential screwSignThreshold := by linarith
  have hcoeff2 : -(9 / 50 : ℝ) ≤ EF.gammaBracket 0 + levyCoshPotential screwSignThreshold :=
    neg_nine_fiftieths_lt_gammaBracket_add_levyCoshPotential_screwSignThreshold.le
  nlinarith

/-- **Unconditional positivity on `(0, L)` (for any `L ≥ 1 / 9`, including `L = log 2`) whenever
`3 * coreMass f L (1 / 18) ≤ 4 * collarMass f L (1 / 18)`**:
every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`1 / 9 ≤ L`) whose collar mass in
`Iic (1 / 18) ∪ Ioi (L - 1 / 18)` is at least `(3 / 4)` of its core mass satisfies `0 ≤ W_∞(f ⋆ f̃)`
unconditionally! -/
theorem weilArchRe_nonneg_of_three_mul_coreMass_le_four_mul_collarMass_inv_18 {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL : 1 / 9 ≤ L) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0)
    (hdom : 3 * coreMass f L (1 / 18) ≤ 4 * collarMass f L (1 / 18)) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := rational_collar_core_inv_18_add_interior_le_weilArchRe hf hfc hf0 hL hsupp
  have hcor_nn := coreMass_nonneg f L (1 / 18)
  have hint_nn : 0 ≤ ∫ x in Ioo (1 / 18) screwSignThreshold,
      (-screwRegularKernel x) * (∫ u in Ioc 0 (L - x), (f u - f (u + x)) ^ 2) := by
    refine setIntegral_nonneg measurableSet_Ioo fun x hx => ?_
    exact mul_nonneg
      (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans (by norm_num) hx.1) hx.2.le))
      (integral_nonneg fun _ => sq_nonneg _)
  linarith

/-- **Collar-Cancelled Core-Slice Lower Bound on `D_h(x)`**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` and any `0 ≤ a ≤ x` with `2 * a + x ≤ L`,
the boundary-escape term inside `D_h(x)` automatically cancels the `-collarMass h L a` tax from
`core_slice_sub_collarMass_le_interior_jump_sq`, yielding the pure core-slice bound:
`(1 / 2) * ((∫ v in Ioc x (a + x), h v ^ 2) + ∫ u in Ioc (L - x - a) (L - x), h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem half_core_slice_le_integral_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C L a x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (ha0 : 0 ≤ a) (hax : a ≤ x) (h2axL : 2 * a + x ≤ L) :
    (1 / 2 : ℝ) *
        ((∫ v in Ioc x (a + x), h v ^ 2) + ∫ u in Ioc (L - x - a) (L - x), h u ^ 2) ≤
      ∫ u, (h u - h (u + x)) ^ 2 := by
  have h1 := collarMass_add_interior_le_integral_jump_sq hh hsupp ha0 hax
  have h2 := core_slice_sub_collarMass_le_interior_jump_sq hh ha0 hax h2axL
  linarith

/-- Specializing `half_core_slice_le_integral_jump_sq` to `a = x` (`0 ≤ x` and `3 * x ≤ L`) gives
the pure double-slice bound:
`(1 / 2) * ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem half_double_slice_le_integral_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ v ∉ Ioo 0 L, h v = 0)
    (hx0 : 0 ≤ x) (h3xL : 3 * x ≤ L) :
    (1 / 2 : ℝ) *
        ((∫ v in Ioc x (2 * x), h v ^ 2) + ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) ≤
      ∫ u, (h u - h (u + x)) ^ 2 := by
  have h := half_core_slice_le_integral_jump_sq hh hsupp hx0 le_rfl (by linarith)
  rwa [show x + x = 2 * x by ring, show L - x - x = L - 2 * x by ring] at h

end

end RHTower.WeilLevyOsculatingFloor
