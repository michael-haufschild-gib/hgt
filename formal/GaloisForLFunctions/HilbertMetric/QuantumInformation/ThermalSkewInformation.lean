import GaloisForLFunctions.HilbertMetric.QuantumInformation.SandwichedVariance
import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-!
# Thermal variance deflation

The finite KMS Wightman quadratic form is the geometric-mean form in the
order-two sandwiched variance formula. Its deficit from symmetrized thermal
noise is exactly skew information. The deficit vanishes precisely on
transitions joining equal Gibbs populations.
-/

open scoped BigOperators NNReal
namespace GaloisForLFunctions.HilbertMetric.QuantumInformation
open _root_.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Gibbs populations as nonnegative scalars. -/
def thermalPopulation (β : ℝ) (E : ι → ℝ) : ι → ℝ≥0 :=
  fun i => ⟨finiteGibbsStateWeight β E i, (finiteGibbsStateWeight_pos β E i).le⟩

/-- The Wightman weight is the square root of the population product. -/
theorem thermalPopulation_sqrt_mul (β : ℝ) (E : ι → ℝ) (i j : ι) :
    Real.sqrt (thermalPopulation β E i) * Real.sqrt (thermalPopulation β E j) =
      finiteKMSWightmanWeight β E i j := by
  change Real.sqrt (finiteGibbsStateWeight β E i) *
      Real.sqrt (finiteGibbsStateWeight β E j) = _
  rw [← Real.sqrt_mul (finiteGibbsStateWeight_pos β E i).le,
    ← finiteKMSWightmanWeight_sq, Real.sqrt_sq (finiteKMSWightmanWeight_pos β E i j).le]

/-- Order-two spectral noise is exactly thermal Wightman intensity. -/
theorem sandwichedQuadratic_thermal_eq (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℂ) :
    sandwichedQuadratic (thermalPopulation β E) A =
      ∑ i, ∑ j, finiteKMSWightmanTransitionIntensity β E A i j := by
  unfold sandwichedQuadratic
  simp_rw [thermalPopulation_sqrt_mul]
  rfl

/-- Exact quantum deflation of thermal transition noise. -/
theorem thermal_born_sub_wightman_eq_skew (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℂ) :
    bornQuadratic (thermalPopulation β E) A -
        (∑ i, ∑ j, finiteKMSWightmanTransitionIntensity β E A i j) =
      skewInformation (thermalPopulation β E) A := by
  rw [← sandwichedQuadratic_thermal_eq, born_sub_sandwiched_eq_skewInformation]

/-- Wightman fluctuations never exceed symmetrized Born fluctuations. -/
theorem thermal_wightman_le_born (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℂ) :
    (∑ i, ∑ j, finiteKMSWightmanTransitionIntensity β E A i j) ≤
      bornQuadratic (thermalPopulation β E) A := by
  rw [← sandwichedQuadratic_thermal_eq]
  exact sandwichedQuadratic_le_born _ _

/-- Gibbs degeneracy is exactly zero inverse temperature or energy degeneracy. -/
theorem thermalPopulation_eq_iff (β : ℝ) (E : ι → ℝ) (i j : ι) :
    thermalPopulation β E i = thermalPopulation β E j ↔ β = 0 ∨ E i = E j := by
  rw [← NNReal.coe_inj]
  change Real.exp (-β * E i) / finiteGibbsPartition β E =
    Real.exp (-β * E j) / finiteGibbsPartition β E ↔ _
  rw [div_left_inj' (finiteGibbsPartition_pos β E).ne', Real.exp_eq_exp]
  constructor
  · intro h
    have hz : β * (E i - E j) = 0 := by linarith
    simpa only [mul_eq_zero, sub_eq_zero] using hz
  · rintro (rfl | h)
    · simp only [neg_zero, zero_mul]
    · rw [h]

/-- Thermal skew information is zero exactly on energy-preserving transitions,
with the maximally mixed zero-inverse-temperature state included. -/
theorem thermal_skew_eq_zero_iff (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℂ) :
    skewInformation (thermalPopulation β E) A = 0 ↔
      ∀ i j, β = 0 ∨ E i = E j ∨ A i j = 0 := by
  rw [skewInformation_eq_zero_iff]
  simp only [thermalPopulation_eq_iff, or_assoc]

/-- Strict quantum deflation requires a populated, nonzero-energy transition. -/
theorem thermal_wightman_lt_born_iff (β : ℝ) (E : ι → ℝ) (A : ι → ι → ℂ) :
    (∑ i, ∑ j, finiteKMSWightmanTransitionIntensity β E A i j) <
        bornQuadratic (thermalPopulation β E) A ↔
      ∃ i j, β ≠ 0 ∧ E i ≠ E j ∧ A i j ≠ 0 := by
  rw [← sandwichedQuadratic_thermal_eq, sandwichedQuadratic_lt_born_iff]
  simp only [ne_eq, thermalPopulation_eq_iff, not_or, and_assoc]

end
end GaloisForLFunctions.HilbertMetric.QuantumInformation
