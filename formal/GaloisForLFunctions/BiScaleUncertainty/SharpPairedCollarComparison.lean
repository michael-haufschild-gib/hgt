import GaloisForLFunctions.BiScaleUncertainty.ConcentratedPairedCollarPenalty
import GaloisForLFunctions.BiScaleUncertainty.SharpCollarCutoffComparison
import GaloisForLFunctions.BiScaleUncertainty.ProductCoupledCollarHierarchy

/-!
# Sharp paired cutoff comparison

Actual concentrated extension and retraction lose an inverse-cutoff radial
budget. Optimization therefore retains the full leading physical tail mass.
-/

set_option autoImplicit false
open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
namespace PhysicalCollarPartition
variable {n m : ℕ}

theorem integral_concentratedExtend_pairedPenalty_le (ρ : PhysicalCollarPartition n)
    (hm : n ≤ m) (hn : 6 ≤ n) :
    (∫ y in Ioo 0 logarithmicCollarRadius, (ρ.concentratedExtend hm).pairedRadialPenalty y) -
      (∫ y in Ioo 0 logarithmicCollarRadius, ρ.pairedRadialPenalty y) ≤
      8192 / ((n + 2 : ℕ) : ℝ) := by
  have h := integral_le_constant_of_small_support
    ((ρ.concentratedExtend hm).integrableOn_pairedRadialPenalty.sub ρ.integrableOn_pairedRadialPenalty)
    (by positivity : 0 ≤ 1 / ((n + 2 : ℕ) : ℝ)) (by norm_num : (0 : ℝ) ≤ 8192)
    (fun y hy => ρ.concentratedExtend_pairedPenalty_le hm hn hy)
  change (∫ y in Ioo 0 logarithmicCollarRadius,
    ((ρ.concentratedExtend hm).pairedRadialPenalty y - ρ.pairedRadialPenalty y)) ≤
    8192 * (1 / ((n + 2 : ℕ) : ℝ)) at h
  rw [integral_sub (ρ.concentratedExtend hm).integrableOn_pairedRadialPenalty
    ρ.integrableOn_pairedRadialPenalty] at h
  convert h using 1
  ring

theorem integral_concentratedRetract_pairedPenalty_le (η : PhysicalCollarPartition m)
    (hm : n ≤ m) (hn : 6 ≤ n) :
    (∫ y in Ioo 0 logarithmicCollarRadius, (η.concentratedRetract hm).pairedRadialPenalty y) -
      (∫ y in Ioo 0 logarithmicCollarRadius, η.pairedRadialPenalty y) ≤
      12288 / ((n + 2 : ℕ) : ℝ) := by
  have h := integral_le_constant_of_small_support
    ((η.concentratedRetract hm).integrableOn_pairedRadialPenalty.sub η.integrableOn_pairedRadialPenalty)
    (by positivity : 0 ≤ 2 / ((n + 2 : ℕ) : ℝ)) (by norm_num : (0 : ℝ) ≤ 6144)
    (fun y hy => η.concentratedRetract_pairedPenalty_le hm hn hy)
  change (∫ y in Ioo 0 logarithmicCollarRadius,
    ((η.concentratedRetract hm).pairedRadialPenalty y - η.pairedRadialPenalty y)) ≤
    6144 * (2 / ((n + 2 : ℕ) : ℝ)) at h
  rw [integral_sub (η.concentratedRetract hm).integrableOn_pairedRadialPenalty
    η.integrableOn_pairedRadialPenalty] at h
  convert h using 1
  ring

theorem concentratedExtend_pairedCoefficient_lower (ρ : PhysicalCollarPartition n)
    (hm : n ≤ m) (hn : 6 ≤ n) :
    ρ.pairedCoefficient + collarEndpointTailMass n - collarEndpointTailMass m -
      8192 / ((n + 2 : ℕ) : ℝ) ≤ (ρ.concentratedExtend hm).pairedCoefficient := by
  have h := ρ.integral_concentratedExtend_pairedPenalty_le hm hn
  rw [ρ.pairedCoefficient_eq_mass_sub_penalty,
    (ρ.concentratedExtend hm).pairedCoefficient_eq_mass_sub_penalty,
    physicalMass_eq_tail_sub_endpoint, physicalMass_eq_tail_sub_endpoint]
  linarith

theorem concentratedRetract_pairedCoefficient_upper (η : PhysicalCollarPartition m)
    (hm : n ≤ m) (hn : 6 ≤ n) :
    η.pairedCoefficient ≤ (η.concentratedRetract hm).pairedCoefficient +
      collarEndpointTailMass n - collarEndpointTailMass m + 12288 / ((n + 2 : ℕ) : ℝ) := by
  have h := η.integral_concentratedRetract_pairedPenalty_le hm hn
  rw [η.pairedCoefficient_eq_mass_sub_penalty,
    (η.concentratedRetract hm).pairedCoefficient_eq_mass_sub_penalty,
    physicalMass_eq_tail_sub_endpoint, physicalMass_eq_tail_sub_endpoint]
  linarith

/-- The finite optimum follows physical tail mass up to an inverse-cutoff error. -/
theorem pairedOptimalCoefficient_sharp_cutoff_comparison (hm : n ≤ m) (hn : 6 ≤ n) :
    collarEndpointTailMass n - collarEndpointTailMass m - 8192 / ((n + 2 : ℕ) : ℝ) ≤
      pairedOptimalCoefficient m - pairedOptimalCoefficient n ∧
    pairedOptimalCoefficient m - pairedOptimalCoefficient n ≤
      collarEndpointTailMass n - collarEndpointTailMass m + 12288 / ((n + 2 : ℕ) : ℝ) := by
  have hlo : pairedOptimalCoefficient n ≤ pairedOptimalCoefficient m -
      (collarEndpointTailMass n - collarEndpointTailMass m) + 8192 / ((n + 2 : ℕ) : ℝ) := by
    apply csSup_le
    · exact ⟨(equalMultiplicity n).pairedCoefficient, equalMultiplicity n, rfl⟩
    · rintro c ⟨ρ, rfl⟩
      have h := ρ.concentratedExtend_pairedCoefficient_lower hm hn
      have hb := le_csSup (pairedCoefficient_range_bddAbove m) ⟨ρ.concentratedExtend hm, rfl⟩
      change (ρ.concentratedExtend hm).pairedCoefficient ≤ pairedOptimalCoefficient m at hb
      linarith
  have hhi : pairedOptimalCoefficient m ≤ pairedOptimalCoefficient n +
      (collarEndpointTailMass n - collarEndpointTailMass m) + 12288 / ((n + 2 : ℕ) : ℝ) := by
    apply csSup_le
    · exact ⟨(equalMultiplicity m).pairedCoefficient, equalMultiplicity m, rfl⟩
    · rintro c ⟨η, rfl⟩
      have h := η.concentratedRetract_pairedCoefficient_upper hm hn
      have hb := le_csSup (pairedCoefficient_range_bddAbove n) ⟨η.concentratedRetract hm, rfl⟩
      change (η.concentratedRetract hm).pairedCoefficient ≤ pairedOptimalCoefficient n at hb
      linarith
  constructor <;> linarith

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
