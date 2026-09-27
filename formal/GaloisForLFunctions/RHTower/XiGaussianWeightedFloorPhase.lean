import GaloisForLFunctions.RHTower.XiCriticalGaussianWeightedFloor
import GaloisForLFunctions.RHTower.XiGaussianLateOrientationSaving

/-!
# Full Hankel bounds from the paired weighted floor and orientation phase

One actual critical-node family supplies an independent positive floor at
every positive heat time. The full imaginary channel is charged to the
smaller of the two proved source budgets, with the strict late-time saving
available at every finite order. None of the lower brackets is assumed positive.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

/-- The improved independent floor applies to the complete family throughout positive heat time. -/
theorem exists_xiHeatHankelForm_paired_weighted_lower (n : ℕ) :
    ∃ γ : Fin (n + 1) → ℝ,
      (∃ q : Fin (n + 1) → XiZeroCopy,
        ∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      (∀ t : {t : ℝ // 0 < t}, 0 < xiCriticalSamplingHeatFloor γ t) ∧
      ∀ (F : Finset XiZeroCopy) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        (xiCriticalSamplingHeatFloor γ t -
          xiGaussianCombinedPhaseBudget F (n + 1) (xiGaussianHalfHeat t) t) *
            (∑ j ∈ Finset.range (n + 1), a j ^ 2) ≤ xiHeatHankelForm (n + 1) a t := by
  obtain ⟨γ, q, _, _, _, _, hq, _, _, hfloor⟩ :=
    exists_xiGaussianRealChannel_paired_weighted_floor n
  refine ⟨γ, ⟨q, hq⟩, fun t => (hfloor t).1, ?_⟩
  intro F a t
  have hf := (hfloor t).2.2 a
  have hb := xiHeatHankelForm_ge_realChannel_sub_combined_budget F (n + 1) a t
  nlinarith only [hf, hb]

/-- Every finite order has the sharper independent floor and strict late source saving. -/
theorem exists_xiHeatHankelForm_paired_weighted_late_lower (n : ℕ) :
    ∃ γ : Fin (n + 1) → ℝ,
      (∃ q : Fin (n + 1) → XiZeroCopy,
        ∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      (∀ t : {t : ℝ // 0 < t}, 0 < xiCriticalSamplingHeatFloor γ t) ∧
      ∀ (F : Finset XiZeroCopy) (a : ℕ → ℝ)
        (t : {t : {t : ℝ // 0 < t} // xiGaussianOrientationLateTime n ≤ (t : ℝ)}),
        (xiCriticalSamplingHeatFloor γ t.1 -
          (1 / 2 : ℝ) * xiCriticalFourthTraceResidual F *
            Real.exp (-((t.1 : ℝ) * xiCriticalResidualPhaseGap F / 2)) *
              xiGaussianFourthTraceEnvelope (n + 1) (xiGaussianHalfHeat t.1)) *
                (∑ j ∈ Finset.range (n + 1), a j ^ 2) ≤ xiHeatHankelForm (n + 1) a t.1 := by
  obtain ⟨γ, q, _, _, _, _, hq, _, _, hfloor⟩ :=
    exists_xiGaussianRealChannel_paired_weighted_floor n
  refine ⟨γ, ⟨q, hq⟩, fun t => (hfloor t).1, ?_⟩
  intro F a t
  have hf := (hfloor t.1).2.2 a
  have hI := xiGaussianImaginaryChannel_half_late_le_half_source F n a t
  have he := xiGaussianTrace_eq_realChannel_sub_imaginary
    (∑ j ∈ Finset.range (n + 1), Polynomial.C (a j) * Polynomial.X ^ j) t.1
  rw [xiPolynomialGaussianHeatTraceReal_rangeSum t.1.property] at he
  nlinarith only [hf, hI, he]

/-- The complete three-by-three form keeps every diagonal and mixed coefficient term. -/
theorem exists_xiHeatThirdQuadratic_paired_weighted_lower :
    ∃ γ : Fin 3 → ℝ,
      (∃ q : Fin 3 → XiZeroCopy,
        ∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      (∀ t : {t : ℝ // 0 < t}, 0 < xiCriticalSamplingHeatFloor γ t) ∧
      ∀ (F : Finset XiZeroCopy) (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        (xiCriticalSamplingHeatFloor γ t -
          xiGaussianCombinedPhaseBudget F 3 (xiGaussianHalfHeat t) t) *
            (a ^ 2 + b ^ 2 + c ^ 2) ≤ xiHeatThirdQuadratic a b c t := by
  obtain ⟨γ, hq, hpos, hbound⟩ := exists_xiHeatHankelForm_paired_weighted_lower 2
  refine ⟨γ, hq, hpos, ?_⟩
  intro F a b c t
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [Finset.sum_range_succ] using
    hbound F (fun n => if n = 0 then a else if n = 1 then b else c) t

/-- Literal third-order late-time lower bound with the new source coefficient. -/
theorem exists_xiHeatThirdQuadratic_paired_weighted_late_lower :
    ∃ γ : Fin 3 → ℝ,
      (∃ q : Fin 3 → XiZeroCopy,
        ∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      (∀ t : {t : ℝ // 0 < t}, 0 < xiCriticalSamplingHeatFloor γ t) ∧
      ∀ (F : Finset XiZeroCopy) (a b c : ℝ)
        (t : {t : {t : ℝ // 0 < t} // xiGaussianOrientationLateTime 2 ≤ (t : ℝ)}),
        (xiCriticalSamplingHeatFloor γ t.1 -
          (1 / 2 : ℝ) * xiCriticalFourthTraceResidual F *
            Real.exp (-((t.1 : ℝ) * xiCriticalResidualPhaseGap F / 2)) *
              xiGaussianFourthTraceEnvelope 3 (xiGaussianHalfHeat t.1)) *
                (a ^ 2 + b ^ 2 + c ^ 2) ≤ xiHeatThirdQuadratic a b c t.1 := by
  obtain ⟨γ, hq, hpos, hbound⟩ := exists_xiHeatHankelForm_paired_weighted_late_lower 2
  refine ⟨γ, hq, hpos, ?_⟩
  intro F a b c t
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [Finset.sum_range_succ] using
    hbound F (fun n => if n = 0 then a else if n = 1 then b else c) t

end RHTower
