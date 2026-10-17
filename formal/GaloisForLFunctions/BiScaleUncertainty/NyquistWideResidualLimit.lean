import GaloisForLFunctions.BiScaleUncertainty.NyquistWideSourceEnergy
import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightOperator
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual smooth sources attain the residual norm under every energy ceiling -/

open Set Filter Topology MeasureTheory
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistWideResidual (β : ℝ) (m N j : ℕ) : ℝ :=
  ∫ x, nyquistWideCorrelation j x * nyquistWeightKernel β m N x

theorem integrable_nyquistWideResidual {β : ℝ} (hβ : 0 ≤ β) (m N j : ℕ) :
    Integrable (fun x => nyquistWideCorrelation j x * nyquistWeightKernel β m N x) :=
  integrable_compact_mul_nyquistWeightKernel hβ m N
    (continuous_nyquistWideCorrelation j) (hasCompactSupport_nyquistWideCorrelation j)

theorem nyquistWideResidual_nonneg {β : ℝ} (hβ : 0 ≤ β) (m N j : ℕ) :
    0 ≤ nyquistWideResidual β m N j :=
  integral_nonneg (fun x => mul_nonneg (nyquistWideCorrelation_nonneg j x)
    (nyquistWeightKernel_nonneg hβ m N x))

theorem nyquistWideResidual_eq_operator {β : ℝ} (hβ : 0 ≤ β) (m N j : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    nyquistWideResidual β m N j = nyquistWeightOperator hβ m N hlt
      (nyquistWideCorrelationMap j) := rfl

theorem nyquistWideResidual_le_tailMass {β : ℝ} (hβ : 0 ≤ β) (m N j : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    nyquistWideResidual β m N j ≤ nyquistWeightTailMass β m N := by
  have hb := integral_mul_nyquistWeightKernel_le hβ m N hlt (nyquistWideCorrelationMap j)
  change ‖nyquistWideResidual β m N j‖ ≤
    nyquistWeightTailMass β m N * ‖nyquistWideCorrelationMap j‖ at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (nyquistWideResidual_nonneg hβ m N j)] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left (norm_nyquistWideCorrelationMap_le_one j)
    (nyquistWeightTailMass_nonneg hβ m N)).trans_eq (mul_one _))

theorem tendsto_nyquistWideResidual_subcritical {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    Tendsto (nyquistWideResidual β m N) atTop (𝓝 (nyquistWeightTailMass β m N)) := by
  have hi := (integrable_nyquistWeightKernel_iff_nonneg hβ m N).mpr hlt
  have ht := tendsto_integral_of_dominated_convergence (nyquistWeightKernel β m N)
    (fun j => (integrable_nyquistWideResidual hβ m N j).aestronglyMeasurable) hi
    (fun j => Eventually.of_forall fun x => by
      simp only [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (nyquistWeightKernel_nonneg hβ m N x)]
      exact (mul_le_mul_of_nonneg_right (abs_nyquistWideCorrelation_le_one j x)
        (nyquistWeightKernel_nonneg hβ m N x)).trans_eq (one_mul _))
    (Eventually.of_forall fun x => by
      simpa only [one_mul] using
        (tendsto_nyquistWideCorrelation x).mul_const (nyquistWeightKernel β m N x))
  simpa only [nyquistWideResidual, integral_nyquistWeightKernel hβ m N hlt] using ht

theorem exists_nyquistWideResidual_near_norm {β ε C : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) (hε : 0 < ε) (hC : C < nyquistWeightTailMass β m N) :
    ∃ j : ℕ, normalizedArchEnergy (nyquistWideSource j) < ε ∧
      C < nyquistWideResidual β m N j := by
  exact ((tendsto_nyquistWideSource_energy.eventually_lt_const hε).and
    ((tendsto_nyquistWideResidual_subcritical hβ m N hlt).eventually_const_lt hC)).exists

theorem nyquistWideResidual_best_constant {β ε C : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) (hε : 0 < ε) :
    (∀ j : ℕ, normalizedArchEnergy (nyquistWideSource j) ≤ ε →
      nyquistWideResidual β m N j ≤ C) ↔ nyquistWeightTailMass β m N ≤ C := by
  constructor
  · intro h
    by_contra hC
    obtain ⟨j, hj, hjC⟩ := exists_nyquistWideResidual_near_norm hβ m N hlt hε (lt_of_not_ge hC)
    exact (not_lt_of_ge (h j hj.le)) hjC
  · intro hC j _
    exact (nyquistWideResidual_le_tailMass hβ m N j hlt).trans hC

end
end GaloisForLFunctions.BiScaleUncertainty
