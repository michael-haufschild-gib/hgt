import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightProducer
import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightPrefixMass
import GaloisForLFunctions.BiScaleUncertainty.NyquistPolarSourceEscape
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Minimum producer order, actual signed sources, and exact calibrations -/

open Set Filter Topology MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem integrable_nyquistWeightKernel_iff_floor_le {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ) :
    Integrable (nyquistWeightKernel β m N) ↔ ⌊β⌋₊ ≤ m := by
  rw [integrable_nyquistWeightKernel_iff_nonneg hβ m N]
  constructor
  · intro h
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt hβ).mpr
    simpa only [Nat.cast_succ] using h
  · intro h
    have hh := (Nat.floor_lt hβ).mp (Nat.lt_succ_of_le h)
    simpa only [Nat.cast_succ] using hh

theorem integrable_nyquistWeightKernel_minimum_degree {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) :
    Integrable (nyquistWeightKernel β ⌊β⌋₊ N) :=
  (integrable_nyquistWeightKernel_iff_floor_le hβ ⌊β⌋₊ N).mpr le_rfl

theorem LevyEnergySource.nyquistWeightProducer_error {K β : ℝ} (f : LevyEnergySource K)
    (hβ : 0 < β) (m N : ℕ) (hlt : β < (m : ℝ) + 1) :
    |nyquistWeightPolarTail β N f.realCorrelation -
      nyquistWeightProducer β m N f.realCorrelation| ≤ nyquistWeightTailBound β m N := by
  have hbound : 0 ≤ nyquistWeightTailBound β m N :=
    (nyquistWeightTailMass_nonneg hβ.le m N).trans (nyquistWeightTailMass_le hβ m N hlt)
  exact (nyquistWeightProducer_error_le hβ m N hlt f.realCorrelation
    f.hasCompactSupport_realCorrelation).trans
      ((mul_le_mul_of_nonneg_left f.norm_realCorrelation_le_one hbound).trans_eq (mul_one _))

theorem nyquistWeight_half (x : ℝ) : nyquistWeight (1 / 2) x = Real.cosh (x / 2) := by
  unfold nyquistWeight
  congr 1
  ring

theorem nyquistWeightCellResidual_half_zero (k : ℕ) :
    nyquistWeightCellResidual (1 / 2) 0 k = nyquistResidualDensity k := by
  funext x
  simp only [nyquistWeightCellResidual, nyquistWeightTaylorResidual,
    nyquistWeightTaylor_zero, nyquistWeight_half, nyquistResidualDensity,
    nyquistPolarConstant, nyquistResidualNode]

theorem nyquistWeightCellMass_half_zero (k : ℕ) :
    nyquistWeightCellMass (1 / 2) 0 k = nyquistResidualMass k := by
  change (∫ x in nyquistResidualNode k..nyquistResidualNode (k + 1),
    nyquistWeightCellResidual (1 / 2) 0 k x) = _
  rw [nyquistWeightCellResidual_half_zero]
  rfl

theorem nyquistWeightTailMass_half_zero (N : ℕ) :
    nyquistWeightTailMass (1 / 2) 0 N = nyquistResidualTailMass N := by
  simp only [nyquistWeightTailMass, nyquistWeightCellMass_half_zero, nyquistResidualTailMass]

theorem nyquistWeightKernel_half_zero (N : ℕ) :
    nyquistWeightKernel (1 / 2) 0 N = nyquistResidualKernel N := by
  funext x
  simp only [nyquistWeightKernel, nyquistWeightCellResidual_half_zero, nyquistResidualKernel]

theorem nyquistWeightProducedCell_half_zero (H : ℝ →ᵇ ℝ) (k : ℕ) :
    nyquistWeightProducedCell (1 / 2) 0 H k = nyquistPolarCellAverage H k := by
  simp [nyquistWeightProducedCell, nyquistWeightJet_zero, nyquistWeight_half,
    nyquistWeightCellMoment, nyquistPolarCellAverage, nyquistPolarConstant, nyquistResidualNode]

theorem nyquistWeightProducer_half_zero (N : ℕ) (H : ℝ →ᵇ ℝ) :
    nyquistWeightProducer (1 / 2) 0 N H = nyquistPolarProducer N H := by
  simp only [nyquistWeightProducer, nyquistWeightProducedCell_half_zero, nyquistPolarProducer]

theorem nyquistWeightPolarTail_half (N : ℕ) (H : ℝ →ᵇ ℝ) :
    nyquistWeightPolarTail (1 / 2) N H = nyquistPolarTail N H := by
  simp only [nyquistWeightPolarTail, nyquistWeight_half, nyquistPolarTail]

theorem tendsto_nyquistWeightTailMass_half_zero :
    Tendsto (fun N => nyquistWeightTailMass (1 / 2) 0 N /
      ((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 (1 / 4 : ℝ)) := by
  convert tendsto_nyquistWeightTailMass_normalized (β := (1 / 2 : ℝ))
    (by norm_num) 0 (by norm_num) using 1 <;> norm_num [nyquistWeightCellConstant]

theorem tendsto_nyquistResidualTailMass_sharp :
    Tendsto (fun N => nyquistResidualTailMass N / nyquistResidualTailScale N)
      atTop (𝓝 (1 / 4 : ℝ)) := by
  have he (N : ℕ) : ((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = nyquistResidualTailScale N := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
    simp only [nyquistResidualTailScale, one_div]
  simpa only [nyquistWeightTailMass_half_zero, he] using tendsto_nyquistWeightTailMass_half_zero

theorem tendsto_nyquistWeightPrefixMass_one_zero (N : ℕ) :
    Tendsto (fun M => nyquistWeightPrefixMass 1 0 N M / nyquistResidualNode M)
      atTop (𝓝 (1 / 4 : ℝ)) := by
  simpa [nyquistWeightCellConstant] using tendsto_nyquistWeightPrefixMass_critical 0 N

theorem tendsto_nyquistWeightTailMass_one_one :
    Tendsto (fun N => nyquistWeightTailMass 1 1 N / ((N + 1 : ℕ) : ℝ) ^ (-1 : ℝ))
      atTop (𝓝 (1 / 12 : ℝ)) := by
  convert tendsto_nyquistWeightTailMass_normalized (β := (1 : ℝ))
    (by norm_num) 1 (by norm_num) using 1 <;> norm_num [nyquistWeightCellConstant]

end
end GaloisForLFunctions.BiScaleUncertainty
