import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The limiting improvement of the joint moment recursion

The descending joint moment recursion is bounded by
`G(R) = 11R/16 − 7/24 − (5/16) H(R)`, `H(R) = (7R⁴(R − 2/3))^{1/5}`, on `R > 2/3`.

* `limitImprovement_seven_ninths`: `G(7/9) = 0`; `limitImprovement_two_thirds`: `G(2/3) = 1/6`.
* `hasDerivAt_limitImprovement`, `limitSlope_eq_recursionSlope`: `G` solves the differential
  equation `G′(R) = ((45R − 24)G(R) + 9R − 7)/(R(45R − 30))`.
* `hasDerivAt_limitSlope`, `limitCurvature_pos`: `G″(R) = H(R)(1/R − 3/(3R − 2))²/20 > 0`.
* `limitImprovement_tangent_le`: `G` lies above each of its tangent lines. After dividing by
  `H(R)` this is the weighted AM–GM inequality `(x⁴y)^{1/5} ≤ (4x + y)/5` at `x = r/R`,
  `y = (3r − 2)/(3R − 2)`.
* `convexOn_limitImprovement`, `limitImprovement_nonneg`: `G` is convex on `(2/3, ∞)` and
  nonnegative on `[2/3, ∞)`, since its tangent at `7/9` is horizontal.
-/

namespace GaloisForLFunctions.JointMarkedMoments

open Real Set

noncomputable section

/-- The fifth-root core `H(R) = (7R⁴(R − 2/3))^{1/5}`. -/
def limitCore (R : ℝ) : ℝ := (7 * R ^ 4 * (R - 2 / 3)) ^ (1 / 5 : ℝ)

/-- The limiting improvement `G(R) = 11R/16 − 7/24 − (5/16) H(R)`. -/
def limitImprovement (R : ℝ) : ℝ := 11 * R / 16 - 7 / 24 - 5 / 16 * limitCore R

/-- The slope field `((45R − 24)z + 9R − 7)/(R(45R − 30))` of the propagation at its threshold
cutoff. -/
def recursionSlope (R z : ℝ) : ℝ := ((45 * R - 24) * z + 9 * R - 7) / (R * (45 * R - 30))

/-- The logarithmic derivative `H′/H = (4/R + 3/(3R − 2))/5`. -/
def coreLogSlope (R : ℝ) : ℝ := (4 / R + 3 / (3 * R - 2)) / 5

/-- `G′(R) = 11/16 − (5/16) H(R) H′(R)/H(R)`. -/
def limitSlope (R : ℝ) : ℝ := 11 / 16 - 5 / 16 * (limitCore R * coreLogSlope R)

/-- `G″(R) = H(R)(1/R − 3/(3R − 2))²/20`. -/
def limitCurvature (R : ℝ) : ℝ := limitCore R * (1 / R - 3 / (3 * R - 2)) ^ 2 / 20

theorem limitCore_pos {R : ℝ} (hR : 2 / 3 < R) : 0 < limitCore R := by
  have h0 : 0 < R := by linarith
  have h1 : 0 < R - 2 / 3 := by linarith
  exact Real.rpow_pos_of_pos (by positivity) _

theorem limitCore_two_thirds : limitCore (2 / 3) = 0 := by
  unfold limitCore
  rw [show (7 : ℝ) * (2 / 3) ^ 4 * (2 / 3 - 2 / 3) = 0 by ring]
  exact Real.zero_rpow (by norm_num)

theorem limitCore_seven_ninths : limitCore (7 / 9) = 7 / 9 := by
  unfold limitCore
  rw [show (7 : ℝ) * (7 / 9) ^ 4 * (7 / 9 - 2 / 3) = (7 / 9) ^ 5 by norm_num,
    show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

theorem limitImprovement_seven_ninths : limitImprovement (7 / 9) = 0 := by
  unfold limitImprovement; rw [limitCore_seven_ninths]; norm_num

theorem limitImprovement_two_thirds : limitImprovement (2 / 3) = 1 / 6 := by
  unfold limitImprovement; rw [limitCore_two_thirds]; norm_num

/-- Weighted AM–GM with weights `4/5, 1/5`: `(x⁴y)^{1/5} ≤ (4x + y)/5`. -/
theorem fifthRoot_le_mean {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x ^ 4 * y) ^ (1 / 5 : ℝ) ≤ (4 * x + y) / 5 := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 4 / 5) (w₂ := 1 / 5) (p₁ := x)
    (p₂ := y) (by norm_num) (by norm_num) hx hy (by norm_num)
  have hx4 : (x ^ 4) ^ (1 / 5 : ℝ) = x ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  rw [Real.mul_rpow (by positivity) hy, hx4]
  linarith

/-- `H(r) = H(R) ((r/R)⁴ (3r − 2)/(3R − 2))^{1/5}`. -/
theorem limitCore_eq_mul {R r : ℝ} (hR : 2 / 3 < R) (hr : 2 / 3 ≤ r) :
    limitCore r = limitCore R * ((r / R) ^ 4 * ((3 * r - 2) / (3 * R - 2))) ^ (1 / 5 : ℝ) := by
  have hR0 : 0 < R := by linarith
  have hR1 : 0 < R - 2 / 3 := by linarith
  have hR2 : 0 < 3 * R - 2 := by linarith
  unfold limitCore
  rw [← Real.mul_rpow (by positivity)
    (mul_nonneg (by positivity) (div_nonneg (by linarith) hR2.le))]
  congr 1
  field_simp
  ring

/-- `H` is concave: it lies below each tangent line `H(R) + (r − R) H′(R)`. -/
theorem limitCore_le_tangent {R r : ℝ} (hR : 2 / 3 < R) (hr : 2 / 3 ≤ r) :
    limitCore r ≤ limitCore R + (r - R) * (limitCore R * coreLogSlope R) := by
  have hR0 : 0 < R := by linarith
  have hR2 : 0 < 3 * R - 2 := by linarith
  have hmean := fifthRoot_le_mean (div_nonneg (by linarith : (0 : ℝ) ≤ r) hR0.le)
    (div_nonneg (by linarith : (0 : ℝ) ≤ 3 * r - 2) hR2.le)
  have key : limitCore R + (r - R) * (limitCore R * coreLogSlope R) =
      limitCore R * ((4 * (r / R) + (3 * r - 2) / (3 * R - 2)) / 5) := by
    unfold coreLogSlope
    have : R ≠ 0 := hR0.ne'
    have : 3 * R - 2 ≠ 0 := hR2.ne'
    field_simp
    ring
  rw [limitCore_eq_mul hR hr, key]
  exact mul_le_mul_of_nonneg_left hmean (limitCore_pos hR).le

theorem hasDerivAt_limitCore {R : ℝ} (hR : 2 / 3 < R) :
    HasDerivAt limitCore (limitCore R * coreLogSlope R) R := by
  have hR0 : R ≠ 0 := by linarith
  have hR1 : R - 2 / 3 ≠ 0 := by linarith
  have hR2 : 3 * R - 2 ≠ 0 := by linarith
  have hb : 7 * R ^ 4 * (R - 2 / 3) ≠ 0 := by positivity
  have hpoly : HasDerivAt (fun y : ℝ => 7 * y ^ 4 * (y - 2 / 3))
      (7 * ((4 : ℕ) * R ^ (4 - 1)) * (R - 2 / 3) + 7 * R ^ 4 * 1) R :=
    HasDerivAt.mul (HasDerivAt.const_mul 7 (hasDerivAt_pow 4 R))
      ((hasDerivAt_sub_const_iff (2 / 3 : ℝ)).mpr (hasDerivAt_id' (x := R)))
  refine (hpoly.rpow_const (p := 1 / 5) (Or.inl hb)).congr_deriv ?_
  rw [Real.rpow_sub_one hb]
  unfold limitCore coreLogSlope
  generalize (7 * R ^ 4 * (R - 2 / 3)) ^ (1 / 5 : ℝ) = Hc
  push_cast
  field_simp
  ring

theorem hasDerivAt_limitImprovement {R : ℝ} (hR : 2 / 3 < R) :
    HasDerivAt limitImprovement (limitSlope R) R := by
  have h1 : HasDerivAt (fun y : ℝ => 11 * y / 16) (11 * 1 / 16) R :=
    HasDerivAt.div_const (HasDerivAt.const_mul 11 (hasDerivAt_id' (x := R))) 16
  have h := HasDerivAt.sub ((hasDerivAt_sub_const_iff (7 / 24 : ℝ)).mpr h1)
    (HasDerivAt.const_mul (5 / 16) (hasDerivAt_limitCore hR))
  exact h.congr_deriv (by unfold limitSlope; ring)

/-- The limiting improvement solves the slope-field equation `G′ = ((45R − 24)G + 9R − 7)/(R(45R − 30))`. -/
theorem limitSlope_eq_recursionSlope {R : ℝ} (hR : 2 / 3 < R) :
    limitSlope R = recursionSlope R (limitImprovement R) := by
  have hR0 : R ≠ 0 := by linarith
  have hR2 : 3 * R - 2 ≠ 0 := by linarith
  have hR3 : 45 * R - 30 ≠ 0 := by linarith
  unfold limitSlope recursionSlope limitImprovement coreLogSlope
  generalize limitCore R = Hc
  field_simp
  ring

theorem limitSlope_seven_ninths : limitSlope (7 / 9) = 0 := by
  rw [limitSlope_eq_recursionSlope (by norm_num), limitImprovement_seven_ninths]
  unfold recursionSlope; norm_num

theorem hasDerivAt_coreLogSlope {R : ℝ} (hR : 2 / 3 < R) :
    HasDerivAt coreLogSlope ((-4 / R ^ 2 - 9 / (3 * R - 2) ^ 2) / 5) R := by
  have hR0 : R ≠ 0 := by linarith
  have hR2 : 3 * R - 2 ≠ 0 := by linarith
  have h4 := HasDerivAt.div (hasDerivAt_const R (4 : ℝ)) (hasDerivAt_id' (x := R)) hR0
  have hlin : HasDerivAt (fun y : ℝ => 3 * y - 2) (3 * 1) R :=
    (hasDerivAt_sub_const_iff (2 : ℝ)).mpr (HasDerivAt.const_mul 3 (hasDerivAt_id' (x := R)))
  have h3 := HasDerivAt.div (hasDerivAt_const R (3 : ℝ)) hlin hR2
  refine (HasDerivAt.div_const (HasDerivAt.add h4 h3) 5).congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_limitSlope {R : ℝ} (hR : 2 / 3 < R) :
    HasDerivAt limitSlope (limitCurvature R) R := by
  have hR0 : R ≠ 0 := by linarith
  have hR2 : 3 * R - 2 ≠ 0 := by linarith
  have h := HasDerivAt.const_sub (11 / 16 : ℝ) (HasDerivAt.const_mul (5 / 16 : ℝ)
    (HasDerivAt.mul (hasDerivAt_limitCore hR) (hasDerivAt_coreLogSlope hR)))
  refine h.congr_deriv ?_
  unfold limitCurvature coreLogSlope
  generalize limitCore R = Hc
  field_simp
  ring

/-- Strict convexity in the form of Lemma 6.1: `G″(R) > 0` for `R > 2/3`. -/
theorem limitCurvature_pos {R : ℝ} (hR : 2 / 3 < R) : 0 < limitCurvature R := by
  have hR0 : 0 < R := by linarith
  have hR2 : 0 < 3 * R - 2 := by linarith
  have hgap : 1 / R - 3 / (3 * R - 2) = -2 / (R * (3 * R - 2)) := by
    field_simp; ring
  have hneg : 1 / R - 3 / (3 * R - 2) < 0 := by
    rw [hgap]; exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  unfold limitCurvature
  have := limitCore_pos hR
  have : 0 < (1 / R - 3 / (3 * R - 2)) ^ 2 := by positivity
  positivity

/-- `G` lies above its tangent lines: `G(R) + (r − R) G′(R) ≤ G(r)`. -/
theorem limitImprovement_tangent_le {R r : ℝ} (hR : 2 / 3 < R) (hr : 2 / 3 ≤ r) :
    limitImprovement R + (r - R) * limitSlope R ≤ limitImprovement r := by
  have := limitCore_le_tangent hR hr
  unfold limitImprovement limitSlope
  nlinarith [this]

theorem convexOn_limitImprovement : ConvexOn ℝ (Ioi (2 / 3)) limitImprovement := by
  refine ⟨convex_Ioi _, fun x hx y hy a b ha hb hab => ?_⟩
  have hz : 2 / 3 < a * x + b * y := by
    simpa [smul_eq_mul] using (convex_Ioi (2 / 3 : ℝ)) hx hy ha hb hab
  have h1 := mul_le_mul_of_nonneg_left (limitImprovement_tangent_le hz (le_of_lt hx)) ha
  have h2 := mul_le_mul_of_nonneg_left (limitImprovement_tangent_le hz (le_of_lt hy)) hb
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [smul_eq_mul]
  nlinarith [h1, h2]

/-- `G ≥ 0` on `[2/3, ∞)`: the tangent at `7/9` is the zero line. -/
theorem limitImprovement_nonneg {r : ℝ} (hr : 2 / 3 ≤ r) : 0 ≤ limitImprovement r := by
  have h := limitImprovement_tangent_le (R := 7 / 9) (by norm_num) hr
  rw [limitImprovement_seven_ninths, limitSlope_seven_ninths] at h
  linarith

end

end GaloisForLFunctions.JointMarkedMoments
