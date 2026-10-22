import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianResolvedAdmission

/-!
# Stability boundary of reflected-Gaussian horizon admission

The fixed reflected Meyer Gaussian supplies a nonvanishing square-summable horizon grade and an
actual resolved singular class.  Square summability forces that grade to decay along the cofinite
Xi divisor.  Thus its diagonal multiplier is coefficient-faithful but has no positive lower
modulus in the ordinary unweighted divisor norm.  The source-graded completion is necessary, not
an optional renormalization.
-/

open Complex Filter Topology

namespace RHTower.DeningerMeyerGaussianGreen

noncomputable section

/-- The reflected-Gaussian source grade decays at the infinite Xi-divisor horizon. -/
theorem tendsto_norm_reflectedGaussianHorizonGrade_cofinite_zero :
    Tendsto (fun q : XiZeroCopy => ‖reflectedGaussianHorizonGrade q‖)
      cofinite (nhds 0) := by
  have hsq := summable_norm_sq_reflectedGaussianHorizonGrade.tendsto_cofinite_zero
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg, norm_nonneg, Real.sqrt_zero] using hsqrt

/-- Ordinary unweighted stable recovery is impossible despite coefficientwise faithfulness. -/
theorem not_exists_uniform_lower_bound_reflectedGaussianHorizonGrade :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ q : XiZeroCopy, c ≤ ‖reflectedGaussianHorizonGrade q‖ := by
  rintro ⟨c, hc, hlower⟩
  have hev :=
    tendsto_norm_reflectedGaussianHorizonGrade_cofinite_zero.eventually_lt_const hc
  obtain ⟨q, hq⟩ := hev.exists
  exact (not_lt_of_ge (hlower q)) hq

/-- Multiplication by the reflected-Gaussian grade loses no divisor coefficient. -/
theorem reflectedGaussianHorizonGrade_mul_injective :
    Function.Injective
      (fun u : XiZeroCopy → ℂ =>
        fun q => reflectedGaussianHorizonGrade q * u q) := by
  intro u v huv
  funext q
  exact mul_left_cancel₀ (reflectedGaussianHorizonGrade_ne_zero q)
    (congrFun huv q)

end

end RHTower.DeningerMeyerGaussianGreen
