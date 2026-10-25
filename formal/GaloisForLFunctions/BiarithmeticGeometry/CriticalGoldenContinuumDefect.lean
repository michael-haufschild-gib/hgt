import GaloisForLFunctions.BiarithmeticGeometry.CriticalGoldenPaymentQuotients
import GaloisForLFunctions.BiarithmeticGeometry.PowerTailWienerFamily
import GaloisForLFunctions.BiarithmeticGeometry.PowerTailIndependence
import GaloisForLFunctions.ArithmeticOrientationTheory.WienerCoefficientEvaluation

/-!
# Continuum-dimensional actual critical golden payment defect

Power-tail kernels in the unpaid exponent interval lie in the actual payment
closure. Their classes are complex-linearly independent: a finite relation
would have square-summable coefficient partial sums, contradicting the
dominant-exponent lower bound. Ambient Wiener cardinality gives equality
for both the closure defect and the unreduced quotient.
-/

noncomputable section
open Finset
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The open interval of positive unpaid tail exponents. -/
abbrev CriticalPowerExponent := Set.Ioo (0 : ℝ) (1 / 2)

/-- The actual power-tail class in the unreduced payment quotient. -/
def criticalGoldenPowerClass (α : CriticalPowerExponent) : CriticalGoldenPaymentQuotient :=
  criticalGoldenPaidSubmodule.mkQ (powerTailWiener α α.property.1)

/-- The same actual kernel as a class in the payment closure defect. -/
def criticalGoldenPowerDefectClass (α : CriticalPowerExponent) : CriticalGoldenPaymentClosureDefect :=
  criticalGoldenClosurePaid.mkQ
    ⟨powerTailWiener α α.property.1, powerTailWiener_mem_closure_paidIdeal α α.property.1⟩

private theorem coefficient_sum_powerTailWiener (s : Finset CriticalPowerExponent)
    (c : CriticalPowerExponent → ℂ) (n : ℕ) :
    (∑ α ∈ s, c α • powerTailWiener α α.property.1).toFn n =
      ∑ α ∈ s, c α * (powerTailWiener α α.property.1).toFn n := by
  change WienerAlgebraAt.coefficientLinear (1 / 2) n
    (∑ α ∈ s, c α • powerTailWiener α α.property.1) = _
  simp only [map_sum, map_smul, WienerAlgebraAt.coefficientLinear_apply, smul_eq_mul]

private theorem normalized_sum_powerTailWiener (s : Finset CriticalPowerExponent)
    (c : CriticalPowerExponent → ℂ) (r : ℕ) :
    (∑ α ∈ s, c α • powerTailWiener α α.property.1).toFn (5 ^ r) / (Real.sqrt 5 : ℂ) ^ r =
      ∑ α ∈ s, c α * (criticalPowerCoeff (α : ℝ) r : ℂ) := by
  have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  rw [coefficient_sum_powerTailWiener, div_eq_mul_inv, Finset.sum_mul]
  apply sum_congr rfl
  intro α _
  rw [powerTailWiener_pow]
  field_simp [hs]

/-- The actual unpaid power-tail classes are complex-linearly independent. -/
theorem criticalGoldenPowerClass_linearIndependent :
    LinearIndependent ℂ criticalGoldenPowerClass := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum α hα
  let k : WienerAlgebraAt (1 / 2) := ∑ β ∈ s, c β • powerTailWiener β β.property.1
  have hclass : criticalGoldenPaidSubmodule.mkQ k = 0 := by
    simpa only [k, map_sum, map_smul, criticalGoldenPowerClass] using hsum
  have hk : k ∈ criticalGoldenPaidSubmodule := by
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hclass
  have hsupp (n : ℕ) (hn : n ∉ Set.range (fun r : ℕ => 5 ^ r)) : k.toFn n = 0 := by
    change (∑ β ∈ s, c β • powerTailWiener β β.property.1).toFn n = 0
    rw [coefficient_sum_powerTailWiener]
    simp only [powerTailWiener_off_support _ _ n hn, mul_zero, sum_const_zero]
  have hp := (mem_paidIdeal_golden_critical_fiveTower_iff k hsupp).mp hk
  have henergy : Summable (fun M : ℕ => ‖∑ r ∈ range (M + 1),
      ∑ β ∈ s, c β * (criticalPowerCoeff (β : ℝ) r : ℂ)‖ ^ 2) := by
    simpa only [k, normalized_sum_powerTailWiener] using hp
  exact criticalPowerCoeff_interval_independent_mod_squareSums s c henergy α hα

/-- Independence survives already inside the closure defect. -/
theorem criticalGoldenPowerDefectClass_linearIndependent :
    LinearIndependent ℂ criticalGoldenPowerDefectClass := by
  apply LinearIndependent.of_comp criticalGoldenDefectToQuotient
  have hcomp : criticalGoldenDefectToQuotient ∘ criticalGoldenPowerDefectClass =
      criticalGoldenPowerClass := by
    funext α
    exact criticalGoldenDefectToQuotient_mk
      ⟨powerTailWiener α α.property.1, powerTailWiener_mem_closure_paidIdeal α α.property.1⟩
  rw [hcomp]
  exact criticalGoldenPowerClass_linearIndependent

/-- The full unreduced actual critical golden quotient has complex Hamel dimension continuum. -/
theorem rank_criticalGoldenPaymentQuotient_eq_continuum :
    Module.rank ℂ CriticalGoldenPaymentQuotient = Cardinal.continuum := by
  apply le_antisymm rank_criticalGoldenPaymentQuotient_le_continuum
  have h := criticalGoldenPowerClass_linearIndependent.cardinal_le_rank
  change Cardinal.mk (Set.Ioo (0 : ℝ) (1 / 2)) ≤ _ at h
  rwa [Cardinal.mk_Ioo_real (by norm_num : (0 : ℝ) < 1 / 2)] at h

/-- The closure defect itself has complex Hamel dimension exactly continuum. -/
theorem rank_criticalGoldenPaymentClosureDefect_eq_continuum :
    Module.rank ℂ CriticalGoldenPaymentClosureDefect = Cardinal.continuum := by
  apply le_antisymm rank_criticalGoldenPaymentClosureDefect_le_continuum
  have h := criticalGoldenPowerDefectClass_linearIndependent.cardinal_le_rank
  change Cardinal.mk (Set.Ioo (0 : ℝ) (1 / 2)) ≤ _ at h
  rwa [Cardinal.mk_Ioo_real (by norm_num : (0 : ℝ) < 1 / 2)] at h

end GaloisForLFunctions.BiarithmeticGeometry

