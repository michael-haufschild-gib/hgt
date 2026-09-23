import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The Fejér kernel as a square

Writing the Fejér kernel as `(N+1)^{-1}` times the squared modulus of a finite exponential sum makes
its nonnegativity immediate and expresses it as a finite double sum of characters, which is all a
pairing argument needs: pairing a periodic function against it produces a finite combination of the
function's Fourier coefficients.

The concentration bound comes from the closed form of the finite geometric sum.
-/

open Complex Finset

noncomputable section

namespace HTGeometry

/-- The finite exponential sum whose squared modulus is the Fejér kernel. -/
def fejerSum (N : ℕ) (θ : ℝ) : ℂ := ∑ n ∈ Finset.range (N + 1), Complex.exp ((n : ℂ) * θ * I)

/-- The Fejér kernel. -/
def fejerKernel (N : ℕ) (θ : ℝ) : ℝ := ‖fejerSum N θ‖ ^ (2 : ℕ) / (N + 1)

theorem fejerKernel_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ fejerKernel N θ := by
  rw [fejerKernel]
  positivity

/-- The Fejér kernel as a finite double sum of characters. -/
theorem fejerKernel_eq_double_sum (N : ℕ) (θ : ℝ) :
    ((fejerKernel N θ : ℝ) : ℂ)
      = (((N : ℝ) + 1)⁻¹ : ℂ) * ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
          Complex.exp (((n : ℂ) - (m : ℂ)) * θ * I) := by
  have hsq : ((‖fejerSum N θ‖ : ℂ)) ^ (2 : ℕ) = fejerSum N θ * (starRingEnd ℂ) (fejerSum N θ) :=
    (Complex.mul_conj' _).symm
  rw [fejerKernel]
  push_cast
  rw [hsq, fejerSum, map_sum, Finset.sum_mul_sum]
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.conj_I]
  ring

theorem normSq_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * I) - 1‖ ^ (2 : ℕ) = 2 - 2 * Real.cos θ := by
  have h : Complex.exp ((θ : ℂ) * I) - 1
      = ((Real.cos θ - 1 : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [h, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **The concentration bound.**  Away from the origin the Fejér kernel is `O(1/N)`. -/
theorem fejerKernel_le {N : ℕ} {θ : ℝ} (hθ : Complex.exp ((θ : ℂ) * I) ≠ 1) :
    fejerKernel N θ ≤ 2 / (((N : ℝ) + 1) * (1 - Real.cos θ)) := by
  have hne : Complex.exp ((θ : ℂ) * I) - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have hnormpos : 0 < ‖Complex.exp ((θ : ℂ) * I) - 1‖ := norm_pos_iff.mpr hne
  have hgeom : fejerSum N θ
      = ((Complex.exp ((θ : ℂ) * I)) ^ (N + 1) - 1) / (Complex.exp ((θ : ℂ) * I) - 1) := by
    rw [fejerSum, ← geom_sum_eq hθ (N + 1)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hnum : ‖(Complex.exp ((θ : ℂ) * I)) ^ (N + 1) - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_pow, Complex.norm_exp]
    have hre : ((θ : ℂ) * I).re = 0 := by simp
    rw [hre, Real.exp_zero, one_pow]
    norm_num
  have hbound : ‖fejerSum N θ‖ ≤ 2 / ‖Complex.exp ((θ : ℂ) * I) - 1‖ := by
    rw [hgeom, norm_div]
    exact div_le_div_of_nonneg_right hnum hnormpos.le
  have hcos : 2 - 2 * Real.cos θ = ‖Complex.exp ((θ : ℂ) * I) - 1‖ ^ (2 : ℕ) :=
    (normSq_exp_mul_I_sub_one θ).symm
  have hcospos : 0 < 1 - Real.cos θ := by
    have := normSq_exp_mul_I_sub_one θ
    nlinarith [hnormpos]
  rw [fejerKernel]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : ‖fejerSum N θ‖ ^ (2 : ℕ) ≤ 4 / ‖Complex.exp ((θ : ℂ) * I) - 1‖ ^ (2 : ℕ) := by
    have h1 : ‖fejerSum N θ‖ ^ (2 : ℕ) ≤ (2 / ‖Complex.exp ((θ : ℂ) * I) - 1‖) ^ (2 : ℕ) := by
      nlinarith [hbound, norm_nonneg (fejerSum N θ), hnormpos]
    calc ‖fejerSum N θ‖ ^ (2 : ℕ) ≤ (2 / ‖Complex.exp ((θ : ℂ) * I) - 1‖) ^ (2 : ℕ) := h1
      _ = 4 / ‖Complex.exp ((θ : ℂ) * I) - 1‖ ^ (2 : ℕ) := by
          rw [div_pow]
          norm_num
  have hden : ‖Complex.exp ((θ : ℂ) * I) - 1‖ ^ (2 : ℕ) = 2 * (1 - Real.cos θ) := by
    rw [normSq_exp_mul_I_sub_one]
    ring
  rw [hden] at hsq
  have hNn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [le_div_iff₀ (by positivity)] at hsq
  have hkey : ‖fejerSum N θ‖ ^ (2 : ℕ) * (1 - Real.cos θ) ≤ 2 := by nlinarith [hsq]
  nlinarith [hkey, hNn, sq_nonneg (‖fejerSum N θ‖)]

theorem continuous_fejerSum (N : ℕ) : Continuous (fejerSum N) := by
  refine continuous_finsetSum _ fun n _ => ?_
  fun_prop

theorem continuous_fejerKernel (N : ℕ) : Continuous (fejerKernel N) := by
  refine Continuous.div_const ?_ _
  exact ((continuous_fejerSum N).norm).pow 2

/-- The crude bound: the Fejér kernel never exceeds `N + 1`. -/
theorem fejerKernel_le_card (N : ℕ) (θ : ℝ) : fejerKernel N θ ≤ (N : ℝ) + 1 := by
  have hsum : ‖fejerSum N θ‖ ≤ (N : ℝ) + 1 := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.range (N + 1), ‖Complex.exp ((n : ℂ) * θ * I)‖ ≤ 1 := by
      intro n _
      rw [Complex.norm_exp]
      have hre : ((n : ℂ) * θ * I).re = 0 := by simp [Complex.mul_re]
      rw [hre, Real.exp_zero]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    simp
  have hNn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [fejerKernel, div_le_iff₀ hNn]
  nlinarith [hsum, norm_nonneg (fejerSum N θ)]

end HTGeometry

end
