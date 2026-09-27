import GaloisForLFunctions.RHTower.XiGaussianOrientationEnvelope

/-!
# Complete Hankel bounds from the residual transverse orientation

The entire polynomial phase is bounded by its orientation-weighted envelope.
Taking the minimum with the previous full-source estimate preserves the
stronger bound at each order and heat time. No cross term or spectral copy
is discarded, and no sign of the resulting Hankel lower bracket is assumed.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

def xiGaussianOrientationPhaseBudget (F : Finset XiZeroCopy) (N : ℕ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  Real.exp (-((t - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
    xiGaussianOrientationEnvelope N s t * xiResidualOrientationBudget F

theorem xiGaussianOrientationPhaseBudget_nonneg (F : Finset XiZeroCopy) (N : ℕ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : 0 ≤ xiGaussianOrientationPhaseBudget F N s t :=
  mul_nonneg (mul_nonneg (Real.exp_pos _).le (xiGaussianOrientationEnvelope_nonneg N s t))
    (xiResidualOrientationBudget_pos F).le

/-- The actual full imaginary channel, before replacing orientation by an arithmetic ceiling. -/
theorem xiGaussianImaginaryChannel_le_actual_orientation
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 q) ≤
        Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
          xiGaussianOrientationEnvelope N s t.1 * xiThermalOrientationEnergy *
            (∑ j ∈ Finset.range N, a j ^ 2) := by
  let C := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
    xiGaussianOrientationEnvelope N s t.1 * (∑ j ∈ Finset.range N, a j ^ 2)
  have h := (summable_xiGaussianImaginaryChannelAtom _ t.1).tsum_le_tsum
    (xiGaussianImaginaryAtom_le_orientation_weight F N a s t)
    (summable_xiThermalOrientationTerm.mul_left C)
  rw [tsum_mul_left] at h
  change _ ≤ C * xiThermalOrientationEnergy at h
  calc
    _ ≤ C * xiThermalOrientationEnergy := h
    _ = _ := by dsimp only [C]; ring

/-- A coefficient-independent full phase ceiling with an explicit adaptive orientation factor. -/
theorem xiGaussianImaginaryChannel_le_orientation_budget
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 q) ≤
        xiGaussianOrientationPhaseBudget F N s t.1 * (∑ j ∈ Finset.range N, a j ^ 2) := by
  have h := xiGaussianImaginaryChannel_le_actual_orientation F N a s t
  have hB := mul_le_mul_of_nonneg_left (xiThermalOrientationEnergy_le_residualOrientationBudget F)
    (mul_nonneg (Real.exp_pos (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F))).le
      (xiGaussianOrientationEnvelope_nonneg N s t.1))
  have hc := mul_le_mul_of_nonneg_right hB
    (show 0 ≤ ∑ j ∈ Finset.range N, a j ^ 2 from Finset.sum_nonneg fun j _ => sq_nonneg (a j))
  exact h.trans hc

def xiGaussianCombinedPhaseBudget (F : Finset XiZeroCopy) (N : ℕ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  min (xiGaussianResidualPhaseBudget F N s t) (xiGaussianOrientationPhaseBudget F N s t)

theorem xiGaussianCombinedPhaseBudget_nonneg (F : Finset XiZeroCopy) (N : ℕ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : 0 ≤ xiGaussianCombinedPhaseBudget F N s t :=
  le_min (xiGaussianResidualPhaseBudget_nonneg F N s t)
    (xiGaussianOrientationPhaseBudget_nonneg F N s t)

/-- The new bound never weakens the previous complete residual-source bound. -/
theorem xiGaussianImaginaryChannel_le_combined_budget
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 q) ≤
        xiGaussianCombinedPhaseBudget F N s t.1 * (∑ j ∈ Finset.range N, a j ^ 2) := by
  unfold xiGaussianCombinedPhaseBudget
  by_cases h : xiGaussianResidualPhaseBudget F N s t.1 ≤ xiGaussianOrientationPhaseBudget F N s t.1
  · rw [min_eq_left h]
    exact xiGaussianImaginaryChannel_le_residual_source F N a s t
  · rw [min_eq_right (le_of_not_ge h)]
    exact xiGaussianImaginaryChannel_le_orientation_budget F N a s t

/-- Half-time anchoring gives the complete phase bound throughout positive heat time. -/
theorem xiGaussianImaginaryChannel_le_combined_budget_allTime
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t q) ≤
        xiGaussianCombinedPhaseBudget F N (xiGaussianHalfHeat t) t *
          (∑ j ∈ Finset.range N, a j ^ 2) :=
  xiGaussianImaginaryChannel_le_combined_budget F N a (xiGaussianHalfHeat t)
    ⟨t, by change (t : ℝ) / 2 ≤ (t : ℝ); linarith only [t.property]⟩

theorem xiHeatHankelForm_ge_realChannel_sub_combined_budget
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianRealChannelEnergy
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t -
        xiGaussianCombinedPhaseBudget F N (xiGaussianHalfHeat t) t *
          (∑ j ∈ Finset.range N, a j ^ 2) ≤ xiHeatHankelForm N a t := by
  have h := xiGaussianImaginaryChannel_le_combined_budget_allTime F N a t
  have he := xiGaussianTrace_eq_realChannel_sub_imaginary
    (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t
  rw [xiPolynomialGaussianHeatTraceReal_rangeSum t.property] at he
  linarith only [h, he]

/-- The independent real-channel floor and the smaller complete phase ceiling apply to every
finite order and all positive heat times. -/
theorem exists_xiHeatHankelForm_allTime_combined_lower (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (F : Finset XiZeroCopy) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        (c * Real.exp (-(L * (t : ℝ))) -
          xiGaussianCombinedPhaseBudget F N (xiGaussianHalfHeat t) t) *
            (∑ j ∈ Finset.range N, a j ^ 2) ≤ xiHeatHankelForm N a t := by
  obtain ⟨c, hc, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor N
  refine ⟨c, hc, L, hL, ?_⟩
  intro F a t
  have hf := hfloor a t
  have hb := xiHeatHankelForm_ge_realChannel_sub_combined_budget F N a t
  nlinarith only [hf, hb]

/-- Complete three-by-three specialization: the total component and every cross term survive. -/
theorem exists_xiHeatThirdQuadratic_allTime_combined_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (F : Finset XiZeroCopy) (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        (c₀ * Real.exp (-(L * (t : ℝ))) -
          xiGaussianCombinedPhaseBudget F 3 (xiGaussianHalfHeat t) t) *
            (a ^ 2 + b ^ 2 + c ^ 2) ≤ xiHeatThirdQuadratic a b c t := by
  obtain ⟨c₀, hc₀, L, hL, hbound⟩ := exists_xiHeatHankelForm_allTime_combined_lower 3
  refine ⟨c₀, hc₀, L, hL, ?_⟩
  intro F a b c t
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [Finset.sum_range_succ] using
    hbound F (fun n => if n = 0 then a else if n = 1 then b else c) t

end RHTower
