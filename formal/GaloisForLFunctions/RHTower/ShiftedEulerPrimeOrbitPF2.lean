import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The shifted Euler prime orbit is positive but fails PF2

For `x > 1` the local factor of `ζ(s-ω)/ζ(s+ω)` at a prime, written in the variable `z = p^{-s}`
with `x = p^ω`, is

`(1 - x⁻¹ z) / (1 - x z) = ∑ k, a k z ^ k`,  `a 0 = 1`,  `a k = x ^ k - x ^ (k - 2)` for `k ≥ 1`.

All coefficients are positive, yet the first nontrivial Toeplitz minor is

`det ![![a 1, a 2], ![a 0, a 1]] = a 1 ^ 2 - a 0 * a 2 = x⁻² - 1 < 0`,

so the orbit is not a Pólya-frequency sequence of order two.  Coefficient positivity therefore does
not upgrade to a variation-diminishing dilation law.
-/

noncomputable section

namespace RHTower

open scoped BigOperators

/-- Coefficients of the shifted local Euler factor `(1 - x⁻¹ z)/(1 - x z)`. -/
def shiftedEulerOrbitCoeff (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | (k + 1) => x ^ ((k : ℤ) + 1) - x ^ ((k : ℤ) - 1)

@[simp]
theorem shiftedEulerOrbitCoeff_zero (x : ℝ) : shiftedEulerOrbitCoeff x 0 = 1 := rfl

theorem shiftedEulerOrbitCoeff_succ (x : ℝ) (k : ℕ) :
    shiftedEulerOrbitCoeff x (k + 1) = x ^ ((k : ℤ) + 1) - x ^ ((k : ℤ) - 1) := rfl

theorem shiftedEulerOrbitCoeff_one (x : ℝ) : shiftedEulerOrbitCoeff x 1 = x - x⁻¹ := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, shiftedEulerOrbitCoeff_succ]
  norm_num

theorem shiftedEulerOrbitCoeff_two (x : ℝ) : shiftedEulerOrbitCoeff x 2 = x ^ 2 - 1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, shiftedEulerOrbitCoeff_succ,
    show ((1 : ℕ) : ℤ) + 1 = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
  norm_num

/-- Every coefficient of the shifted orbit is positive for a genuine positive shift. -/
theorem shiftedEulerOrbitCoeff_pos {x : ℝ} (hx : 1 < x) (k : ℕ) :
    0 < shiftedEulerOrbitCoeff x k := by
  cases k with
  | zero => norm_num
  | succ k =>
      rw [shiftedEulerOrbitCoeff_succ]
      have hlt : x ^ ((k : ℤ) - 1) < x ^ ((k : ℤ) + 1) := by
        refine zpow_lt_zpow_right₀ hx ?_
        omega
      linarith

/-- The orbit term splits into a geometric term and its once-shifted copy. -/
theorem shiftedEulerOrbitCoeff_mul_pow {x : ℝ} (hx : 0 < x) (z : ℝ) (k : ℕ) :
    shiftedEulerOrbitCoeff x k * z ^ k =
      (x * z) ^ k - (if k = 0 then 0 else x⁻¹ * z * (x * z) ^ (k - 1)) := by
  cases k with
  | zero => simp
  | succ k =>
      have hx0 : x ≠ 0 := ne_of_gt hx
      have h1 : x ^ ((k : ℤ) + 1) = x ^ (k + 1) := by
        rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      have h2 : x ^ ((k : ℤ) - 1) = x⁻¹ * x ^ k := by
        rw [show ((k : ℤ) - 1) = (k : ℤ) + (-1) by ring, zpow_add₀ hx0,
          zpow_natCast, zpow_neg, zpow_one]
        ring
      rw [shiftedEulerOrbitCoeff_succ, h1, h2]
      simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero k)]
      ring

/-- **Generating identity.**  On the disc of convergence the orbit sums to the shifted local Euler
factor. -/
theorem tsum_shiftedEulerOrbitCoeff {x z : ℝ} (hx : 0 < x) (hxz : ‖x * z‖ < 1) :
    ∑' k : ℕ, shiftedEulerOrbitCoeff x k * z ^ k = (1 - x⁻¹ * z) / (1 - x * z) := by
  have hgeomSummable : Summable (fun k : ℕ => (x * z) ^ k) :=
    summable_geometric_of_norm_lt_one hxz
  have hgeom : ∑' k : ℕ, (x * z) ^ k = (1 - x * z)⁻¹ := tsum_geometric_of_norm_lt_one hxz
  set u : ℕ → ℝ := fun k => x⁻¹ * z * (x * z) ^ k with hu
  have huSummable : Summable u := hgeomSummable.mul_left _
  set f : ℕ → ℝ := fun k => if k = 0 then 0 else x⁻¹ * z * (x * z) ^ (k - 1) with hf
  have hshift : (fun k : ℕ => f (k + 1)) = u := by
    funext k
    simp [hf, hu]
  have hfSummable : Summable f := by
    refine (summable_nat_add_iff (f := f) 1).mp ?_
    rw [hshift]
    exact huSummable
  have hfsum : ∑' k : ℕ, f k = ∑' k : ℕ, u k := by
    rw [hfSummable.tsum_eq_zero_add, hshift]
    simp [hf]
  have hsplit : (fun k : ℕ => shiftedEulerOrbitCoeff x k * z ^ k) =
      fun k : ℕ => (x * z) ^ k - f k := by
    funext k
    exact shiftedEulerOrbitCoeff_mul_pow hx z k
  have hne : (1 : ℝ) - x * z ≠ 0 := by
    intro h
    have hxz1 : x * z = 1 := by linarith
    rw [hxz1] at hxz
    norm_num at hxz
  rw [hsplit, Summable.tsum_sub hgeomSummable hfSummable, hfsum, hgeom]
  have husum : ∑' k : ℕ, u k = x⁻¹ * z * (1 - x * z)⁻¹ := by
    rw [hu, tsum_mul_left, hgeom]
  rw [husum]
  field_simp

/-- The first nontrivial Toeplitz matrix of the orbit. -/
def shiftedEulerOrbitToeplitzTwo (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![shiftedEulerOrbitCoeff x 1, shiftedEulerOrbitCoeff x 2;
     shiftedEulerOrbitCoeff x 0, shiftedEulerOrbitCoeff x 1]

theorem det_shiftedEulerOrbitToeplitzTwo {x : ℝ} (hx : 0 < x) :
    (shiftedEulerOrbitToeplitzTwo x).det = x⁻¹ ^ 2 - 1 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [shiftedEulerOrbitToeplitzTwo, Matrix.det_fin_two_of,
    shiftedEulerOrbitCoeff_one, shiftedEulerOrbitCoeff_two, shiftedEulerOrbitCoeff_zero]
  field_simp
  ring

/-- **PF2 failure.**  The first nontrivial Toeplitz minor of the shifted Euler prime orbit is
strictly negative, so the orbit is not a Pólya-frequency sequence of order two, although all of its
coefficients are positive. -/
theorem det_shiftedEulerOrbitToeplitzTwo_neg {x : ℝ} (hx : 1 < x) :
    (shiftedEulerOrbitToeplitzTwo x).det < 0 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [det_shiftedEulerOrbitToeplitzTwo hx0]
  have hinv : x⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hx
  have hinvpos : 0 < x⁻¹ := inv_pos.mpr hx0
  nlinarith

/-- The positive-coefficient orbit is not PF2: positivity of every coefficient coexists with a
negative order-two minor. -/
theorem exists_positive_orbit_failing_pf2 {x : ℝ} (hx : 1 < x) :
    (∀ k : ℕ, 0 < shiftedEulerOrbitCoeff x k) ∧
      (shiftedEulerOrbitToeplitzTwo x).det < 0 :=
  ⟨shiftedEulerOrbitCoeff_pos hx, det_shiftedEulerOrbitToeplitzTwo_neg hx⟩

end RHTower
