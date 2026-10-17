import GaloisForLFunctions.BiScaleUncertainty.ConcentratedCollarPenalty
import GaloisForLFunctions.BiScaleUncertainty.CollarEndpointTailMass

/-!
# Sharp finite-cutoff comparison of the allocation optimum

Explicit extension and retraction lose only an inverse-cutoff radial budget.
The entire leading physical tail survives optimization; no maximizing physical
partition is assumed to exist.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

theorem integral_le_constant_of_small_support {F : ℝ → ℝ} {r C : ℝ}
    (hF : IntegrableOn F (Ioo 0 logarithmicCollarRadius))
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ y ∈ Ioo 0 logarithmicCollarRadius, F y ≤ if y ≤ r then C else 0) :
    (∫ y in Ioo 0 logarithmicCollarRadius, F y) ≤ C * r := by
  have hconst : IntegrableOn (fun _ : ℝ => C) (Ioc 0 r) := by
    apply integrableOn_const
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hm := integral_mono_ae (hF.integrable_indicator measurableSet_Ioo)
    (hconst.integrable_indicator measurableSet_Ioc) (Filter.Eventually.of_forall (fun y => by
      by_cases hy : y ∈ Ioo 0 logarithmicCollarRadius
      · rw [indicator_of_mem hy]
        by_cases hyr : y ≤ r
        · rw [indicator_of_mem (show y ∈ Ioc 0 r from ⟨hy.1, hyr⟩)]
          simpa only [if_pos hyr] using hbound y hy
        · rw [indicator_of_notMem (show y ∉ Ioc 0 r from fun h => hyr h.2)]
          simpa only [if_neg hyr] using hbound y hy
      · rw [indicator_of_notMem hy]
        exact indicator_nonneg (fun _ _ => hC) y))
  rw [integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ioc] at hm
  have hc : (∫ _ : ℝ in Ioc 0 r, C) = C * r := by
    simp only [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hr, smul_eq_mul]
    ring
  rw [hc] at hm
  exact hm

namespace PhysicalCollarPartition
variable {n m : ℕ}

theorem integral_concentratedExtend_penalty_le (ρ : PhysicalCollarPartition n)
    (hm : n ≤ m) (hn : 6 ≤ n) :
    (∫ y in Ioo 0 logarithmicCollarRadius, (ρ.concentratedExtend hm).radialPenalty y) -
      (∫ y in Ioo 0 logarithmicCollarRadius, ρ.radialPenalty y) ≤
      8192 / ((n + 2 : ℕ) : ℝ) := by
  have h := integral_le_constant_of_small_support
    ((ρ.concentratedExtend hm).integrableOn_radialPenalty.sub ρ.integrableOn_radialPenalty)
    (by positivity : 0 ≤ 1 / ((n + 2 : ℕ) : ℝ)) (by norm_num : (0 : ℝ) ≤ 8192)
    (fun y hy => ρ.concentratedExtend_penalty_le hm hn hy)
  rw [integral_sub (ρ.concentratedExtend hm).integrableOn_radialPenalty
    ρ.integrableOn_radialPenalty] at h
  convert h using 1 <;> ring

theorem integral_concentratedRetract_penalty_le (η : PhysicalCollarPartition m)
    (hm : n ≤ m) (hn : 6 ≤ n) :
    (∫ y in Ioo 0 logarithmicCollarRadius, (η.concentratedRetract hm).radialPenalty y) -
      (∫ y in Ioo 0 logarithmicCollarRadius, η.radialPenalty y) ≤
      12288 / ((n + 2 : ℕ) : ℝ) := by
  have h := integral_le_constant_of_small_support
    ((η.concentratedRetract hm).integrableOn_radialPenalty.sub η.integrableOn_radialPenalty)
    (by positivity : 0 ≤ 2 / ((n + 2 : ℕ) : ℝ)) (by norm_num : (0 : ℝ) ≤ 6144)
    (fun y hy => η.concentratedRetract_penalty_le hm hn hy)
  rw [integral_sub (η.concentratedRetract hm).integrableOn_radialPenalty
    η.integrableOn_radialPenalty] at h
  convert h using 1 <;> ring

theorem concentratedExtend_coefficient_lower (ρ : PhysicalCollarPartition n)
    (hm : n ≤ m) (hn : 6 ≤ n) :
    ρ.coefficient + collarEndpointTailMass n - collarEndpointTailMass m -
      8192 / ((n + 2 : ℕ) : ℝ) ≤ (ρ.concentratedExtend hm).coefficient := by
  have h := ρ.integral_concentratedExtend_penalty_le hm hn
  rw [ρ.coefficient_eq_mass_sub_penalty,
    (ρ.concentratedExtend hm).coefficient_eq_mass_sub_penalty,
    physicalMass_eq_tail_sub_endpoint, physicalMass_eq_tail_sub_endpoint]
  linarith

theorem concentratedRetract_coefficient_upper (η : PhysicalCollarPartition m)
    (hm : n ≤ m) (hn : 6 ≤ n) :
    η.coefficient ≤ (η.concentratedRetract hm).coefficient +
      collarEndpointTailMass n - collarEndpointTailMass m + 12288 / ((n + 2 : ℕ) : ℝ) := by
  have h := η.integral_concentratedRetract_penalty_le hm hn
  rw [η.coefficient_eq_mass_sub_penalty,
    (η.concentratedRetract hm).coefficient_eq_mass_sub_penalty,
    physicalMass_eq_tail_sub_endpoint, physicalMass_eq_tail_sub_endpoint]
  linarith

/-- The finite optimum follows physical tail mass up to an inverse-cutoff error. -/
theorem optimalCoefficient_sharp_cutoff_comparison (hm : n ≤ m) (hn : 6 ≤ n) :
    collarEndpointTailMass n - collarEndpointTailMass m - 8192 / ((n + 2 : ℕ) : ℝ) ≤
      optimalCoefficient m - optimalCoefficient n ∧
    optimalCoefficient m - optimalCoefficient n ≤
      collarEndpointTailMass n - collarEndpointTailMass m + 12288 / ((n + 2 : ℕ) : ℝ) := by
  have hlo : optimalCoefficient n ≤ optimalCoefficient m -
      (collarEndpointTailMass n - collarEndpointTailMass m) + 8192 / ((n + 2 : ℕ) : ℝ) := by
    apply csSup_le
    · exact ⟨(equalMultiplicity n).coefficient, equalMultiplicity n, rfl⟩
    · rintro c ⟨ρ, rfl⟩
      have h := ρ.concentratedExtend_coefficient_lower hm hn
      have hb := le_csSup (coefficient_range_bddAbove m) ⟨ρ.concentratedExtend hm, rfl⟩
      change (ρ.concentratedExtend hm).coefficient ≤ optimalCoefficient m at hb
      linarith
  have hhi : optimalCoefficient m ≤ optimalCoefficient n +
      (collarEndpointTailMass n - collarEndpointTailMass m) + 12288 / ((n + 2 : ℕ) : ℝ) := by
    apply csSup_le
    · exact ⟨(equalMultiplicity m).coefficient, equalMultiplicity m, rfl⟩
    · rintro c ⟨η, rfl⟩
      have h := η.concentratedRetract_coefficient_upper hm hn
      have hb := le_csSup (coefficient_range_bddAbove n) ⟨η.concentratedRetract hm, rfl⟩
      change (η.concentratedRetract hm).coefficient ≤ optimalCoefficient n at hb
      linarith
  constructor <;> linarith

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
