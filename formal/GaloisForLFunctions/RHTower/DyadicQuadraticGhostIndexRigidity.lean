import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPositiveStarUntwisting

/-!
# Dyadic quadratic-ghost index rigidity

The full integral Laurent producer already carries the one-copy Hermitian-square ghost

`(T - 1)(T⁻¹ - 1)`.

At dyadic clock and normalized horizontal grade `a`, its physical value is

`-2 (cosh (a log 2) - 1)`.

Throughout the open critical strip this lies strictly between `-1` and `0`. Consequently, if a
separate source construction identifies this value with an ordinary integer index, the value must
vanish and the horizontal grade must be neutral. The final theorem specializes this exact scalar
law to every actual Xi divisor copy. It does not assume or manufacture the missing index producer.
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- At the dyadic clock, the one-copy quadratic Gamma ghost is strictly subunit and nonpositive
throughout the open critical strip. -/
theorem dyadicOneCopyQuadraticGhost_mem_subunit
    (a : ℝ) (ha : |a| < 1) :
    -1 < deningerIntegralGammaEvaluation (Real.log 2 * a)
        sourceHorizontalGammaSixIntegralHermitianSquare ∧
      deningerIntegralGammaEvaluation (Real.log 2 * a)
        sourceHorizontalGammaSixIntegralHermitianSquare ≤ 0 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have habs : |Real.log 2 * a| < |Real.log 2| := by
    rw [abs_mul, abs_of_pos hlog]
    nlinarith
  have hcosh : Real.cosh (Real.log 2 * a) < Real.cosh (Real.log 2) :=
    (Real.cosh_lt_cosh).2 habs
  have hcoshTwo : Real.cosh (Real.log 2) = (5 : ℝ) / 4 := by
    rw [Real.cosh_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [deningerIntegralGammaEvaluation_hermitianSquare_eq_neg_curvature]
  constructor
  · rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]
    rw [hcoshTwo] at hcosh
    linarith
  · exact neg_nonpos.mpr
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_nonneg _)

/-- An integral value of the one-copy dyadic quadratic ghost in the open strip is possible only
at neutral horizontal grade. -/
theorem dyadicOneCopyQuadraticGhost_integral_iff
    (a : ℝ) (ha : |a| < 1) :
    (∃ z : ℤ,
      deningerIntegralGammaEvaluation (Real.log 2 * a)
          sourceHorizontalGammaSixIntegralHermitianSquare = (z : ℝ)) ↔
      a = 0 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hlower, hupper⟩ :=
      dyadicOneCopyQuadraticGhost_mem_subunit a ha
    rw [hz] at hlower hupper
    have hzLower : (-1 : ℤ) < z := by exact_mod_cast hlower
    have hzUpper : z ≤ 0 := by exact_mod_cast hupper
    have hz0 : z = 0 := by omega
    have hghost :
        deningerIntegralGammaEvaluation (Real.log 2 * a)
            sourceHorizontalGammaSixIntegralHermitianSquare = 0 := by
      simpa [hz0] using hz
    rw [deningerIntegralGammaEvaluation_hermitianSquare_eq_neg_curvature] at hghost
    have hcurvature :
        sourceHorizontalGammaSixUnitOppositeBoundaryCurvature (Real.log 2 * a) = 0 := by
      linarith
    have hproduct : Real.log 2 * a = 0 :=
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff _).1 hcurvature
    exact (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hlog)
  · rintro rfl
    refine ⟨0, ?_⟩
    simp [deningerIntegralGammaEvaluation_hermitianSquare_eq_neg_curvature,
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]

/-- On one actual Xi divisor copy, dyadic one-copy ghost integrality is exactly critical-line
placement. -/
theorem xiDyadicOneCopyQuadraticGhost_integral_iff_line
    (q : XiZeroCopy) :
    (∃ z : ℤ,
      deningerIntegralGammaEvaluation
          (Real.log 2 * primeDepthBVWoldXiCenteredRate q.1)
          sourceHorizontalGammaSixIntegralHermitianSquare = (z : ℝ)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have ha : |primeDepthBVWoldXiCenteredRate q.1| < 1 := by
    obtain ⟨hzero, hone⟩ := xi_divisor_support_re_mem_open_unit q.1
    rw [primeDepthBVWoldXiCenteredRate, abs_lt]
    constructor <;> linarith
  rw [dyadicOneCopyQuadraticGhost_integral_iff _ ha,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

end

end RHTower
