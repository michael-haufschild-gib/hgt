import GaloisForLFunctions.RHTower.PrimeBurnolLevySymbol
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! An actual-prime finite control measure whose positive jump measure has infinite mass. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

def primeLevyJumpSize (p : Nat.Primes) : ℝ≥0 := ⟨1 / (p : ℝ), by positivity⟩

def primeLevyControlWeight (p : Nat.Primes) : ℝ≥0 :=
  ⟨1 / ((p : ℝ) * ((p : ℝ) + 1)), by positivity⟩

theorem primeLevyJumpSize_pos (p : Nat.Primes) : 0 < primeLevyJumpSize p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  change 0 < 1 / (p : ℝ)
  positivity

theorem summable_primeLevyControlWeight : Summable primeLevyControlWeight := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply NNReal.summable_coe.mp
  refine (hs.subtype Nat.Prime).of_nonneg_of_le (fun p => (primeLevyControlWeight p).coe_nonneg) ?_
  intro p
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  change 1 / ((p : ℝ) * ((p : ℝ) + 1)) ≤ 1 / (p : ℝ) ^ 2
  exact one_div_le_one_div_of_le (sq_pos_of_pos hp) (by nlinarith)

def primeLevyControlMeasure : Measure ℝ≥0 :=
  Measure.sum (fun p : Nat.Primes =>
    (primeLevyControlWeight p : ℝ≥0∞) • Measure.dirac (primeLevyJumpSize p))

instance : IsFiniteMeasure primeLevyControlMeasure where
  measure_univ_lt_top := by
    have h := lt_top_iff_ne_top.mpr
      (ENNReal.tsum_coe_ne_top_iff_summable.mpr summable_primeLevyControlWeight)
    simpa only [primeLevyControlMeasure, Measure.sum_apply _ MeasurableSet.univ,
      Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using h

theorem primeLevyControlMeasure_zero_atom : primeLevyControlMeasure {0} = 0 := by
  rw [primeLevyControlMeasure, Measure.sum_apply _ (measurableSet_singleton 0)]
  apply ENNReal.tsum_eq_zero.mpr
  intro p
  simp [Measure.smul_apply, (primeLevyJumpSize_pos p).ne']

theorem primeLevy_control_coefficient (p : Nat.Primes) :
    (primeLevyControlWeight p : ℝ) *
      ((1 + (primeLevyJumpSize p : ℝ)) / (primeLevyJumpSize p : ℝ)) = 1 / (p : ℝ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hp1 : (p : ℝ) + 1 ≠ 0 := ne_of_gt (by linarith)
  change (1 / ((p : ℝ) * ((p : ℝ) + 1))) * ((1 + 1 / (p : ℝ)) / (1 / (p : ℝ))) = _
  field_simp

def primeLevyData : BurnolLevyData where
  control := primeLevyControlMeasure
  finite := inferInstance
  zero_atom := primeLevyControlMeasure_zero_atom
  killing := 0
  drift := 0

theorem primeLevyData_exponent (z : ℂ) :
    primeLevyData.exponent z =
      ∑' p : Nat.Primes, (1 - Complex.exp (-z / (p : ℂ))) / (p : ℂ) := by
  simp only [BurnolLevyData.exponent, primeLevyData, NNReal.coe_zero, Complex.ofReal_zero,
    zero_mul, add_zero, zero_add, levyLaplaceJump, primeLevyControlMeasure]
  rw [integral_sum_dirac (fun _ => ENNReal.coe_ne_top)]
  apply tsum_congr
  intro p
  have hc : ((primeLevyControlWeight p : ℝ) : ℂ) *
      (((1 + (primeLevyJumpSize p : ℝ)) / (primeLevyJumpSize p : ℝ) : ℝ) : ℂ) =
      ((1 / (p : ℝ) : ℝ) : ℂ) := by exact_mod_cast primeLevy_control_coefficient p
  rw [ENNReal.coe_toReal, Complex.real_smul, levyLaplaceKernel,
    if_neg (primeLevyJumpSize_pos p).ne', ← mul_assoc, hc]
  change ((1 / (p : ℝ) : ℝ) : ℂ) *
    (1 - Complex.exp (-z * ((1 / (p : ℝ) : ℝ) : ℂ))) = _
  push_cast
  simp only [div_eq_mul_inv, one_mul]
  ring

/-- The untruncated jump measure, in the standard Lévy coordinates. -/
def primeLevyJumpMeasure : Measure ℝ≥0 :=
  primeLevyControlMeasure.withDensity (fun h => (((1 + h) / h : ℝ≥0) : ℝ≥0∞))

theorem primeLevyJumpMeasure_infinite_mass : primeLevyJumpMeasure univ = ∞ := by
  rw [primeLevyJumpMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, primeLevyControlMeasure, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have hc (p : Nat.Primes) : (primeLevyControlWeight p : ℝ≥0∞) *
      (((1 + primeLevyJumpSize p) / primeLevyJumpSize p : ℝ≥0) : ℝ≥0∞) =
      (primeLevyJumpSize p : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul]
    apply congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    apply NNReal.coe_injective
    simpa [primeLevyJumpSize] using! primeLevy_control_coefficient p
  simp_rw [hc]
  by_contra h
  have hs := NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp h)
  exact Nat.Primes.not_summable_one_div hs

end RHTower
