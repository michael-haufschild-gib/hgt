import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Round

/-!
# The condition-count multiplier of an iterated extrapolation

An extrapolation that multiplies the sample range by `K` and halves the multiplicity at each of `J`
steps multiplies the number of conditions by `(K / 2^{d-1})^J`, subject only to per-step
feasibility, which caps `2^{J+1} K` by a fixed budget `A`.  Writing `K = A / 2^{J+1}`, the exponent
of the multiplier is

`J · (log₂ A - d - J)`,

a downward parabola in the number of steps.  Choosing `J` near `(log₂ A - d)/2` therefore makes the
multiplier `2^{(log₂ A - d)²/4}` — *superpolynomial* in the budget, not linear in it.

The consequence is that the Siegel exponent, the ratio of the initial condition count to the number
of unknowns, can be driven superpolynomially small by spending the budget on more steps rather than
on a larger per-step jump.  Any parameter elimination that fixes the number of steps in advance
misses this and will report a spurious obstruction.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Real

/-- **The integer maximum of a downward parabola.**  Rounding to the nearest integer loses at most
a quarter. -/
theorem exists_nat_quadratic_ge {M : ℝ} (hM : 0 ≤ M) :
    ∃ J : ℕ, M ^ 2 / 4 - 1 / 4 ≤ (J : ℝ) * (M - (J : ℝ)) := by
  have hhalf : (0 : ℝ) ≤ M / 2 := by linarith
  have hround : (0 : ℤ) ≤ round (M / 2) := by
    rw [round_eq]
    exact Int.floor_nonneg.mpr (by linarith)
  refine ⟨(round (M / 2)).toNat, ?_⟩
  have hcast : (((round (M / 2)).toNat : ℕ) : ℝ) = ((round (M / 2) : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hround
  rw [hcast]
  set J : ℝ := ((round (M / 2) : ℤ) : ℝ) with hJ
  have hdist : |M / 2 - J| ≤ 1 / 2 := by
    rw [hJ]
    exact abs_sub_round (M / 2)
  have hsq : (M / 2 - J) ^ 2 ≤ (1 / 2) ^ 2 := by
    nlinarith [abs_nonneg (M / 2 - J), sq_abs (M / 2 - J), hdist]
  nlinarith [hsq]

/-- **The multiplier exponent.**  With the whole feasibility budget spent, the exponent of the
condition-count multiplier is the parabola `J ↦ J (log₂ A - d - J)`, whose integer maximum is
`(log₂ A - d)²/4` up to a quarter. -/
theorem exists_extrapolation_multiplier {A : ℝ} (d : ℕ) (hAd : (d : ℝ) ≤ Real.logb 2 A) :
    ∃ J : ℕ, (Real.logb 2 A - (d : ℝ)) ^ 2 / 4 - 1 / 4
      ≤ (J : ℝ) * (Real.logb 2 A - (d : ℝ) - (J : ℝ)) :=
  exists_nat_quadratic_ge (by linarith)

/-- The multiplier exponent is unbounded: no fixed number of steps realises it. -/
theorem extrapolation_multiplier_unbounded (d : ℕ) (Y : ℝ) :
    ∃ (A : ℝ) (J : ℕ), (d : ℝ) ≤ Real.logb 2 A ∧
      Y ≤ (J : ℝ) * (Real.logb 2 A - (d : ℝ) - (J : ℝ)) := by
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ Y + 1 / 4 ≤ M ^ 2 / 4 := by
    refine ⟨max 0 (2 * Real.sqrt (|Y| + 1)), le_max_left _ _, ?_⟩
    have h1 : 0 ≤ Real.sqrt (|Y| + 1) := Real.sqrt_nonneg _
    have h2 : max 0 (2 * Real.sqrt (|Y| + 1)) = 2 * Real.sqrt (|Y| + 1) :=
      max_eq_right (by linarith)
    rw [h2]
    have h3 : Real.sqrt (|Y| + 1) ^ 2 = |Y| + 1 := Real.sq_sqrt (by positivity)
    have h4 : Y ≤ |Y| := le_abs_self Y
    nlinarith
  refine ⟨(2 : ℝ) ^ (M + (d : ℝ)), ?_⟩
  have hlogb : Real.logb 2 ((2 : ℝ) ^ (M + (d : ℝ))) = M + (d : ℝ) := by
    rw [Real.logb, Real.log_rpow (by norm_num)]
    field_simp [Real.log_ne_zero_of_pos_of_ne_one]
  obtain ⟨J, hJ⟩ := exists_nat_quadratic_ge hM0
  refine ⟨J, ?_, ?_⟩
  · rw [hlogb]; linarith
  · rw [hlogb]
    have : (M + (d : ℝ)) - (d : ℝ) = M := by ring
    rw [this]
    linarith

end GaloisForLFunctions.RHTower.Matveev
