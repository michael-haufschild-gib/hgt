import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The degree-one discriminant cross term has an exact positive range

For a reciprocal atom `y = u + i v` with `u > 0` and `v ≠ 0` and a positive real bulk atom `x`, the
degree-one cross term is

`C_y(x) = Re (y (y - x) ^ 2) = u x ^ 2 + 2 (a ^ 2 - u ^ 2) x + u (u ^ 2 - 3 a ^ 2)`,  `a = |v|`.

It factors as `u (x - x₋) (x - x₊)` with

`x∓ = (u ^ 2 - a ^ 2 ∓ a r) / u`,  `r = ‖y‖`,

so `x₊ > 0` always, `x₋ > 0` exactly when `u > √3 a`, and the sign of `C_y` on the positive axis is
determined by the explicit interval `(x₋, x₊)`.  Moreover `x₊ ≤ C * r` with `C ^ 2 = 6√3 - 9`, so
`x ≥ 1.18 ‖y‖` already forces `C_y(x) > 0`.
-/

noncomputable section

namespace RHTower

open Complex

/-- The degree-one discriminant cross term. -/
def discriminantCross (y : ℂ) (x : ℝ) : ℝ := (y * (y - (x : ℂ)) ^ 2).re

/-- Lower root of the cross term. -/
def crossRootLow (y : ℂ) : ℝ := (y.re ^ 2 - y.im ^ 2 - |y.im| * ‖y‖) / y.re

/-- Upper root of the cross term. -/
def crossRootHigh (y : ℂ) : ℝ := (y.re ^ 2 - y.im ^ 2 + |y.im| * ‖y‖) / y.re

theorem norm_sq_eq (y : ℂ) : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Expanded real quadratic form of the cross term. -/
theorem discriminantCross_eq (y : ℂ) (x : ℝ) :
    discriminantCross y x =
      y.re * x ^ 2 + 2 * (y.im ^ 2 - y.re ^ 2) * x + y.re * (y.re ^ 2 - 3 * y.im ^ 2) := by
  simp only [discriminantCross, pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Exact factorization.**  The cross term is a real quadratic with the two displayed roots. -/
theorem discriminantCross_factor {y : ℂ} (hu : 0 < y.re) (x : ℝ) :
    discriminantCross y x = y.re * (x - crossRootLow y) * (x - crossRootHigh y) := by
  have hune : y.re ≠ 0 := ne_of_gt hu
  have hr2 : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := norm_sq_eq y
  have habs : |y.im| ^ 2 = y.im ^ 2 := sq_abs _
  rw [discriminantCross_eq, crossRootLow, crossRootHigh]
  field_simp
  nlinarith [hr2, habs, sq_nonneg (|y.im| * ‖y‖)]

/-- The upper root is strictly positive. -/
theorem crossRootHigh_pos {y : ℂ} (hu : 0 < y.re) (hv : y.im ≠ 0) : 0 < crossRootHigh y := by
  have habs : 0 < |y.im| := abs_pos.mpr hv
  have hr2 : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := norm_sq_eq y
  have hrpos : 0 < ‖y‖ := by
    have : y ≠ 0 := by
      intro h
      rw [h] at hu
      simp at hu
    exact norm_pos_iff.mpr this
  have habs2 : |y.im| ^ 2 = y.im ^ 2 := sq_abs _
  have hnum : 0 < y.re ^ 2 - y.im ^ 2 + |y.im| * ‖y‖ := by
    rcases le_or_gt (y.im ^ 2) (y.re ^ 2) with h | h
    · have hprod : 0 < |y.im| * ‖y‖ := mul_pos habs hrpos
      linarith
    · have hexp : (|y.im| * ‖y‖) ^ 2 = y.im ^ 2 * (y.re ^ 2 + y.im ^ 2) := by
        rw [mul_pow, habs2, hr2]
      have hsq : (y.im ^ 2 - y.re ^ 2) ^ 2 < (|y.im| * ‖y‖) ^ 2 := by
        rw [hexp]
        have hu2 : 0 < y.re ^ 2 := pow_pos hu 2
        have h3 : 0 < 3 * y.im ^ 2 - y.re ^ 2 := by nlinarith
        nlinarith [mul_pos hu2 h3]
      have hprod : 0 < |y.im| * ‖y‖ := mul_pos habs hrpos
      nlinarith [hsq, hprod]
  exact div_pos hnum hu

/-- The lower root never exceeds the upper root. -/
theorem crossRootLow_le_crossRootHigh {y : ℂ} (hu : 0 < y.re) :
    crossRootLow y ≤ crossRootHigh y := by
  rw [crossRootLow, crossRootHigh, div_le_div_iff_of_pos_right hu]
  have : 0 ≤ |y.im| * ‖y‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  linarith

/-- **Positivity of the lower root** is exactly the scale separation `u > √3 a`. -/
theorem crossRootLow_pos_iff {y : ℂ} (hu : 0 < y.re) (hv : y.im ≠ 0) :
    0 < crossRootLow y ↔ Real.sqrt 3 * |y.im| < y.re := by
  have habs : 0 < |y.im| := abs_pos.mpr hv
  have habs2 : |y.im| ^ 2 = y.im ^ 2 := sq_abs _
  have hr2 : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := norm_sq_eq y
  have hrpos : 0 < ‖y‖ := by
    nlinarith [hr2, habs2, habs, norm_nonneg y]
  have hsqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hexp : (|y.im| * ‖y‖) ^ 2 = y.im ^ 2 * (y.re ^ 2 + y.im ^ 2) := by
    rw [mul_pow, habs2, hr2]
  have hnn : 0 ≤ |y.im| * ‖y‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hkey : (0 < y.re ^ 2 - y.im ^ 2 - |y.im| * ‖y‖) ↔ 3 * y.im ^ 2 < y.re ^ 2 := by
    constructor
    · intro hpos
      have h2 : (|y.im| * ‖y‖) ^ 2 < (y.re ^ 2 - y.im ^ 2) ^ 2 := by nlinarith [hnn, hpos]
      rw [hexp] at h2
      have hu2 : 0 < y.re ^ 2 := pow_pos hu 2
      rcases lt_or_ge (3 * y.im ^ 2) (y.re ^ 2) with hlt | hge
      · exact hlt
      · exfalso
        nlinarith [mul_nonneg hu2.le (sub_nonneg.mpr hge), h2]
    · intro h3
      have hgt : 0 < y.re ^ 2 - y.im ^ 2 := by nlinarith [sq_nonneg y.im]
      have h2 : (|y.im| * ‖y‖) ^ 2 < (y.re ^ 2 - y.im ^ 2) ^ 2 := by
        rw [hexp]
        have hu2 : 0 < y.re ^ 2 := pow_pos hu 2
        nlinarith [mul_pos hu2 (sub_pos.mpr h3)]
      nlinarith [h2, hnn, hgt]
  have hsq3 : Real.sqrt 3 * |y.im| < y.re ↔ 3 * y.im ^ 2 < y.re ^ 2 := by
    constructor
    · intro h
      have hnn3 : 0 ≤ Real.sqrt 3 * |y.im| := mul_nonneg (le_of_lt hsqrt3pos) (abs_nonneg _)
      have hmul := mul_self_lt_mul_self hnn3 h
      nlinarith [hmul, hsqrt3, habs2]
    · intro h3
      rcases lt_or_ge (Real.sqrt 3 * |y.im|) y.re with hlt | hge
      · exact hlt
      · exfalso
        have hmul := mul_self_le_mul_self hu.le hge
        nlinarith [hmul, hsqrt3, habs2, h3]
  rw [crossRootLow, div_pos_iff]
  constructor
  · rintro (⟨hnum, -⟩ | ⟨-, hden⟩)
    · exact hsq3.mpr (hkey.mp hnum)
    · linarith
  · intro h
    exact Or.inl ⟨hkey.mpr (hsq3.mp h), hu⟩

/-- Above the upper root the cross term is strictly positive. -/
theorem discriminantCross_pos_of_gt {y : ℂ} (hu : 0 < y.re) {x : ℝ} (hx : crossRootHigh y < x) :
    0 < discriminantCross y x := by
  have hlow : crossRootLow y ≤ crossRootHigh y := crossRootLow_le_crossRootHigh hu
  rw [discriminantCross_factor hu]
  have h1 : 0 < x - crossRootLow y := by linarith
  have h2 : 0 < x - crossRootHigh y := by linarith
  exact mul_pos (mul_pos hu h1) h2

/-- Strictly inside the root interval the cross term is strictly negative. -/
theorem discriminantCross_neg_of_mem_Ioo {y : ℂ} (hu : 0 < y.re) {x : ℝ}
    (hlow : crossRootLow y < x) (hhigh : x < crossRootHigh y) :
    discriminantCross y x < 0 := by
  rw [discriminantCross_factor hu]
  have h1 : 0 < x - crossRootLow y := by linarith
  have h2 : x - crossRootHigh y < 0 := by linarith
  exact mul_neg_of_pos_of_neg (mul_pos hu h1) h2

/-- Below the lower root the cross term is strictly positive. -/
theorem discriminantCross_pos_of_lt {y : ℂ} (hu : 0 < y.re) {x : ℝ} (hx : x < crossRootLow y) :
    0 < discriminantCross y x := by
  have hlow : crossRootLow y ≤ crossRootHigh y := crossRootLow_le_crossRootHigh hu
  rw [discriminantCross_factor hu]
  have h1 : x - crossRootLow y < 0 := by linarith
  have h2 : x - crossRootHigh y < 0 := by linarith
  exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hu h1) h2

/-- The universal scale constant `C` with `C ^ 2 = 6√3 - 9`. -/
def crossScaleConstant : ℝ := Real.sqrt (6 * Real.sqrt 3 - 9)

theorem crossScaleConstant_sq : crossScaleConstant ^ 2 = 6 * Real.sqrt 3 - 9 := by
  have hsqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlow : (1.7 : ℝ) < Real.sqrt 3 := by
    nlinarith [hsqrt3, Real.sqrt_nonneg 3]
  exact Real.sq_sqrt (by nlinarith)

theorem crossScaleConstant_nonneg : 0 ≤ crossScaleConstant := Real.sqrt_nonneg _

theorem crossScaleConstant_lt : crossScaleConstant < 1.18 := by
  have hsqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hup : Real.sqrt 3 < 1.7320509 := by
    nlinarith [hsqrt3, Real.sqrt_nonneg 3]
  have hsq := crossScaleConstant_sq
  nlinarith [crossScaleConstant_nonneg, hsq, hup]

/-- Polynomial core of the universal scale bound: with `S ^ 2 = 3` and `C ^ 2 = 6 S - 9`, the
squared upper root never exceeds the squared scale bound. -/
theorem scaleBound_aux {R A S C : ℝ} (hA : 0 ≤ A) (hAR : A ≤ R)
    (hS : S ^ 2 = 3) (hS1 : 1 ≤ S) (hC : C ^ 2 = 6 * S - 9) :
    (R ^ 2 - 2 * A ^ 2 + A * R) ^ 2 ≤ C ^ 2 * R ^ 2 * (R ^ 2 - A ^ 2) := by
  have hident : C ^ 2 * R ^ 2 * (R ^ 2 - A ^ 2) - (R ^ 2 - 2 * A ^ 2 + A * R) ^ 2 =
      4 * (R - A) * (A - (S - 1) / 2 * R) ^ 2 * (A + (S - 1) * R) := by
    rw [hC]
    linear_combination (-(R - A) * (R ^ 3 * (S - 3) - 3 * A * R ^ 2)) * hS
  have h2 : 0 ≤ A + (S - 1) * R := by nlinarith
  have hnonneg : 0 ≤ 4 * (R - A) * (A - (S - 1) / 2 * R) ^ 2 * (A + (S - 1) * R) :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) h2
  linarith [hident, hnonneg]

/-- **Universal scale bound.**  The upper root is at most `C ‖y‖`. -/
theorem crossRootHigh_le_scale {y : ℂ} (hu : 0 < y.re) (hv : y.im ≠ 0) :
    crossRootHigh y ≤ crossScaleConstant * ‖y‖ := by
  have habs : 0 < |y.im| := abs_pos.mpr hv
  have habs2 : |y.im| ^ 2 = y.im ^ 2 := sq_abs _
  have hr2 : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := norm_sq_eq y
  have hrnn : 0 ≤ ‖y‖ := norm_nonneg y
  have hsqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsqrt3one : (1 : ℝ) ≤ Real.sqrt 3 := by nlinarith [hsqrt3, hsqrt3nn]
  have hC : crossScaleConstant ^ 2 = 6 * Real.sqrt 3 - 9 := crossScaleConstant_sq
  have hAR : |y.im| ≤ ‖y‖ := by nlinarith [hr2, habs2, sq_nonneg y.re, hrnn, abs_nonneg y.im]
  have haux := scaleBound_aux (R := ‖y‖) (A := |y.im|) (S := Real.sqrt 3)
    (C := crossScaleConstant) (abs_nonneg _) hAR hsqrt3 hsqrt3one hC
  have hU2 : y.re ^ 2 = ‖y‖ ^ 2 - |y.im| ^ 2 := by rw [habs2, hr2]; ring
  have hlhs : y.re ^ 2 - y.im ^ 2 + |y.im| * ‖y‖ =
      ‖y‖ ^ 2 - 2 * |y.im| ^ 2 + |y.im| * ‖y‖ := by rw [hU2, habs2]; ring
  have hrhs : (crossScaleConstant * ‖y‖ * y.re) ^ 2 =
      crossScaleConstant ^ 2 * ‖y‖ ^ 2 * (‖y‖ ^ 2 - |y.im| ^ 2) := by rw [← hU2]; ring
  have hsq : (y.re ^ 2 - y.im ^ 2 + |y.im| * ‖y‖) ^ 2 ≤
      (crossScaleConstant * ‖y‖ * y.re) ^ 2 := by
    rw [hlhs, hrhs]
    exact haux
  have hrhsnn : 0 ≤ crossScaleConstant * ‖y‖ * y.re := by
    have := crossScaleConstant_nonneg
    positivity
  rw [crossRootHigh, div_le_iff₀ hu]
  nlinarith [hsq, hrhsnn]

/-- **Sufficient scale separation.**  A bulk atom at least `1.18 ‖y‖` has positive cross term. -/
theorem discriminantCross_pos_of_scale {y : ℂ} (hu : 0 < y.re) (hv : y.im ≠ 0) {x : ℝ}
    (hx : 1.18 * ‖y‖ ≤ x) : 0 < discriminantCross y x := by
  have hrpos : 0 < ‖y‖ := by
    have hyne : y ≠ 0 := by
      intro h
      rw [h] at hu
      simp at hu
    exact norm_pos_iff.mpr hyne
  have hle : crossRootHigh y ≤ crossScaleConstant * ‖y‖ := crossRootHigh_le_scale hu hv
  have hlt : crossScaleConstant * ‖y‖ < 1.18 * ‖y‖ := by
    have := crossScaleConstant_lt
    nlinarith
  exact discriminantCross_pos_of_gt hu (by linarith)

end RHTower
