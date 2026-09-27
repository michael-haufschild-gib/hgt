import GaloisForLFunctions.RHTower.XiGaussianLateOrientationEnvelope

/-!
# A strict residual-source saving for every finite Hankel order

Beyond an explicit order-dependent heat time, the orientation phase ceiling
is less than one half of the residual fourth-trace source times the decaying
half-anchor factorial envelope. The same time works for every coefficient
vector and every finite critical-source selection.
-/

open scoped Real BigOperators
noncomputable section

namespace RHTower

theorem xiGaussianLateOrientation_source_coefficient_lt (F : Finset XiZeroCopy) :
    97 * xiResidualOrientationBudget F < (1 / 2 : ℝ) * xiCriticalFourthTraceResidual F := by
  have hgap := xiGaussianCertifiedPhaseGap_le_residualPhaseGap F
  rw [xiGaussianCertifiedPhaseGap_eq] at hgap
  have hcoeff : (97 : ℝ) * 129 <
      (1 / 2 : ℝ) * (128 * xiCriticalResidualPhaseGap F - 129) := by
    linarith only [hgap]
  have hfrac : (97 : ℝ) * 129 / (128 * xiCriticalResidualPhaseGap F - 129) < 1 / 2 :=
    (div_lt_iff₀ (xiResidualOrientationDenominator_pos F)).mpr hcoeff
  have h := mul_lt_mul_of_pos_right hfrac (xiCriticalFourthTraceResidual_pos F)
  simpa only [xiResidualOrientationBudget, div_mul_eq_mul_div, mul_div_assoc,
    mul_assoc] using h

/-- The strict saving retains exponential heat decay and covers every positive order. -/
theorem xiGaussianOrientationPhaseBudget_half_late_lt (F : Finset XiZeroCopy) (n : ℕ)
    (t : {t : {t : ℝ // 0 < t} // xiGaussianOrientationLateTime n ≤ (t : ℝ)}) :
    xiGaussianOrientationPhaseBudget F (n + 1) (xiGaussianHalfHeat t.1) t.1 <
      ((1 / 2 : ℝ) * xiCriticalFourthTraceResidual F) *
        Real.exp (-(((t.1 : ℝ) - (xiGaussianHalfHeat t.1 : ℝ)) *
          xiCriticalResidualPhaseGap F)) *
            xiGaussianFourthTraceEnvelope (n + 1) (xiGaussianHalfHeat t.1) := by
  have henv := xiGaussianOrientationEnvelope_half_late_le n ⟨t.1, t.property⟩
  have h := mul_le_mul_of_nonneg_right henv (xiResidualOrientationBudget_pos F).le
  have h' := mul_le_mul_of_nonneg_left h
    (Real.exp_pos (-(((t.1 : ℝ) - (xiGaussianHalfHeat t.1 : ℝ)) *
      xiCriticalResidualPhaseGap F))).le
  have hs := mul_lt_mul_of_pos_right (xiGaussianLateOrientation_source_coefficient_lt F)
    (mul_pos (Real.exp_pos (-(((t.1 : ℝ) - (xiGaussianHalfHeat t.1 : ℝ)) *
      xiCriticalResidualPhaseGap F)))
      (xiGaussianFourthTraceEnvelope_pos n (xiGaussianHalfHeat t.1)))
  unfold xiGaussianOrientationPhaseBudget
  nlinarith only [h', hs]

theorem xiGaussianOrientationPhaseBudget_half_late_lt_residual
    (F : Finset XiZeroCopy) (n : ℕ)
    (t : {t : {t : ℝ // 0 < t} // xiGaussianOrientationLateTime n ≤ (t : ℝ)}) :
    xiGaussianOrientationPhaseBudget F (n + 1) (xiGaussianHalfHeat t.1) t.1 <
      xiGaussianResidualPhaseBudget F (n + 1) (xiGaussianHalfHeat t.1) t.1 := by
  have h := xiGaussianOrientationPhaseBudget_half_late_lt F n t
  have hcoeff : (1 / 2 : ℝ) < 42 / 41 := by linarith
  have hδ := mul_lt_mul_of_pos_right hcoeff (xiCriticalFourthTraceResidual_pos F)
  have he := mul_lt_mul_of_pos_right hδ
    (Real.exp_pos (-(((t.1 : ℝ) - (xiGaussianHalfHeat t.1 : ℝ)) *
      xiCriticalResidualPhaseGap F)))
  exact h.trans (mul_lt_mul_of_pos_right he
    (xiGaussianFourthTraceEnvelope_pos n (xiGaussianHalfHeat t.1)))

/-- Actual whole-polynomial imaginary energy, with all coefficient cross terms retained. -/
theorem xiGaussianImaginaryChannel_half_late_le_half_source
    (F : Finset XiZeroCopy) (n : ℕ) (a : ℕ → ℝ)
    (t : {t : {t : ℝ // 0 < t} // xiGaussianOrientationLateTime n ≤ (t : ℝ)}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range (n + 1), Polynomial.C (a j) * Polynomial.X ^ j) t.1 q) ≤
        ((1 / 2 : ℝ) * xiCriticalFourthTraceResidual F *
          Real.exp (-((t.1 : ℝ) * xiCriticalResidualPhaseGap F / 2)) *
            xiGaussianFourthTraceEnvelope (n + 1) (xiGaussianHalfHeat t.1)) *
              (∑ j ∈ Finset.range (n + 1), a j ^ 2) := by
  have h := xiGaussianImaginaryChannel_le_orientation_budget F (n + 1) a
    (xiGaussianHalfHeat t.1)
    ⟨t.1, by change (t.1 : ℝ) / 2 ≤ (t.1 : ℝ); linarith only [t.1.property]⟩
  have h' := mul_le_mul_of_nonneg_right
    (xiGaussianOrientationPhaseBudget_half_late_lt F n t).le
      (Finset.sum_nonneg (s := Finset.range (n + 1)) fun j _ => sq_nonneg (a j))
  have he : -(((t.1 : ℝ) - (xiGaussianHalfHeat t.1 : ℝ)) *
      xiCriticalResidualPhaseGap F) = -((t.1 : ℝ) * xiCriticalResidualPhaseGap F / 2) := by
    change -(((t.1 : ℝ) - (t.1 : ℝ) / 2) * _) = _
    ring
  rw [he] at h'
  exact h.trans h'

/-- An independent positive floor and the improved late phase ceiling for the full family. -/
theorem exists_xiHeatHankelForm_late_half_source_lower (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (F : Finset XiZeroCopy) (a : ℕ → ℝ)
        (t : {t : {t : ℝ // 0 < t} // xiGaussianOrientationLateTime n ≤ (t : ℝ)}),
        (c * Real.exp (-(L * (t.1 : ℝ))) -
          (1 / 2 : ℝ) * xiCriticalFourthTraceResidual F *
            Real.exp (-((t.1 : ℝ) * xiCriticalResidualPhaseGap F / 2)) *
              xiGaussianFourthTraceEnvelope (n + 1) (xiGaussianHalfHeat t.1)) *
                (∑ j ∈ Finset.range (n + 1), a j ^ 2) ≤ xiHeatHankelForm (n + 1) a t.1 := by
  obtain ⟨c, hc, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor (n + 1)
  refine ⟨c, hc, L, hL, ?_⟩
  intro F a t
  have hf := hfloor a t.1
  have hI := xiGaussianImaginaryChannel_half_late_le_half_source F n a t
  have he := xiGaussianTrace_eq_realChannel_sub_imaginary
    (∑ j ∈ Finset.range (n + 1), Polynomial.C (a j) * Polynomial.X ^ j) t.1
  rw [xiPolynomialGaussianHeatTraceReal_rangeSum t.1.property] at he
  nlinarith only [hf, hI, he]

/-- Literal complete three-by-three specialization; the lower bracket is not assigned a sign. -/
theorem exists_xiHeatThirdQuadratic_late_half_source_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (F : Finset XiZeroCopy) (a b c : ℝ)
        (t : {t : {t : ℝ // 0 < t} // xiGaussianOrientationLateTime 2 ≤ (t : ℝ)}),
        (c₀ * Real.exp (-(L * (t.1 : ℝ))) -
          (1 / 2 : ℝ) * xiCriticalFourthTraceResidual F *
            Real.exp (-((t.1 : ℝ) * xiCriticalResidualPhaseGap F / 2)) *
              xiGaussianFourthTraceEnvelope 3 (xiGaussianHalfHeat t.1)) *
                (a ^ 2 + b ^ 2 + c ^ 2) ≤ xiHeatThirdQuadratic a b c t.1 := by
  obtain ⟨c₀, hc₀, L, hL, hbound⟩ := exists_xiHeatHankelForm_late_half_source_lower 2
  refine ⟨c₀, hc₀, L, hL, ?_⟩
  intro F a b c t
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [Finset.sum_range_succ] using
    hbound F (fun n => if n = 0 then a else if n = 1 then b else c) t

end RHTower
