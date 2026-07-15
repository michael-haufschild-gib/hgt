import GaloisForLFunctions.HTGeometry.MagnitudeBalancedGap

/-!
# Polynomial mass versus a superlacunary exponential gap

A positive fixed polynomial in the coefficient level is eventually dominated by
`exp (b m / (R+1))` whenever the successive ratios of `b` tend to infinity.  This is the
analytic comparison used to turn the valuation gap into strict Archimedean dominance.
-/

open Filter

namespace GaloisForLFunctions

/-- Every fixed positive polynomial scale is eventually below the exponential of a divided
superlacunary magnitude. -/
theorem exists_const_mul_pow_lt_exp_div_of_ratio {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    (A : ℝ) (hA : 0 < A) (C E R : ℕ) (hC : 0 < C) :
    ∃ M₀ : ℕ, ∀ m ≥ M₀,
      A * ((C : ℝ) * ((m : ℝ) + 1)) ^ E <
        Real.exp (b m / ((R : ℝ) + 1)) := by
  let R₁ : ℝ := (R : ℝ) + 1
  let K : ℝ := R₁ * (Real.log A + (E : ℝ) * Real.log C + 1)
  obtain ⟨M₀, hM₀⟩ :=
    exists_dominates_log hpos hratio (R₁ * (E : ℝ)) K
  refine ⟨max M₀ 1, fun m hm => ?_⟩
  have hm₀ : M₀ ≤ m := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  have hmp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hCp : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hxpos : 0 < A * ((C : ℝ) * ((m : ℝ) + 1)) ^ E := by positivity
  have hlogm : Real.log ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 2) := by
    exact Real.log_le_log (by positivity) (by linarith)
  have hlogx :
      Real.log (A * ((C : ℝ) * ((m : ℝ) + 1)) ^ E) =
        Real.log A + (E : ℝ) * (Real.log C + Real.log ((m : ℝ) + 1)) := by
    rw [Real.log_mul (ne_of_gt hA) (pow_ne_zero _ (mul_ne_zero (ne_of_gt hCp) (ne_of_gt hmp))),
      Real.log_pow, Real.log_mul (ne_of_gt hCp) (ne_of_gt hmp)]
  have hgrow := hM₀ m hm₀
  have hR₁ : 0 < R₁ := by dsimp [R₁]; positivity
  have hlog_lt :
      Real.log (A * ((C : ℝ) * ((m : ℝ) + 1)) ^ E) < b m / R₁ := by
    rw [lt_div_iff₀ hR₁]
    rw [hlogx]
    dsimp [K] at hgrow
    have hE : 0 ≤ (E : ℝ) := by positivity
    have hlog_le :
        Real.log A + (E : ℝ) * (Real.log C + Real.log ((m : ℝ) + 1)) ≤
          Real.log A + (E : ℝ) * Real.log C +
            (E : ℝ) * Real.log ((m : ℝ) + 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hlogm hE]
    nlinarith
  rw [← Real.exp_log hxpos]
  exact Real.exp_lt_exp.mpr hlog_lt

end GaloisForLFunctions
