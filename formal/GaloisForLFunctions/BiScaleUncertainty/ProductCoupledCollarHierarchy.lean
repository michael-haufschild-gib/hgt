import GaloisForLFunctions.BiScaleUncertainty.SignedCosetProductCoupling
import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarCutoffMonotonicity

/-!
# Monotone source certificates with signed product coupling

At cutoff `N`, use every physical collar grid through `K` with `K² ≤ N`.
Optimize its paired-coset coefficient over physical partitions and combine the
result with the independent-coset cutoff certificate. This gives positive,
monotone, bounded source-energy certificates without optimizer attainment.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

namespace PhysicalCollarPartition
variable {n : ℕ}

theorem pairedCoefficient_le_physical_mass (ρ : PhysicalCollarPartition n) :
    ρ.pairedCoefficient ≤
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x := by
  rw [← ρ.integral_mass]
  apply integral_mono_ae ρ.integrableOn_pairedKernel ρ.integrableOn_mass
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact (ρ.pairedKernel_bounds hy.1.le).2

/-- Supremum over physical allocations for the paired signed-coset relaxation. -/
def pairedOptimalCoefficient (n : ℕ) : ℝ :=
  sSup (Set.range (fun ρ : PhysicalCollarPartition n => ρ.pairedCoefficient))

theorem pairedCoefficient_range_bddAbove (n : ℕ) :
    BddAbove (Set.range (fun ρ : PhysicalCollarPartition n => ρ.pairedCoefficient)) := by
  refine ⟨∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x, ?_⟩
  rintro c ⟨ρ, rfl⟩
  exact ρ.pairedCoefficient_le_physical_mass

theorem pairedCoefficient_le_optimal (ρ : PhysicalCollarPartition n) :
    ρ.pairedCoefficient ≤ pairedOptimalCoefficient n :=
  le_csSup (pairedCoefficient_range_bddAbove n) ⟨ρ, rfl⟩

theorem optimalCoefficient_le_pairedOptimalCoefficient (n : ℕ) :
    optimalCoefficient n ≤ pairedOptimalCoefficient n := by
  apply csSup_le
  · exact ⟨(equalMultiplicity n).coefficient, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact ρ.coefficient_le_pairedCoefficient.trans ρ.pairedCoefficient_le_optimal

theorem pairedOptimalCoefficient_pos (n : ℕ) : 0 < pairedOptimalCoefficient n :=
  (optimalCoefficient_pos n).trans_le (optimalCoefficient_le_pairedOptimalCoefficient n)

/-- The optimized paired certificate applies to actual sources, including infinite energy. -/
theorem pairedOptimalCoefficient_source_energy {n m : ℕ} (f : LogarithmicGridSource m)
    (hcut : (n + 2) ^ 2 ≤ m + 2) :
    ENNReal.ofReal (pairedOptimalCoefficient n * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  let E := ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
    continuousArchIncrementDensity (compactAutocorrKernel f.1) x
  change ENNReal.ofReal (pairedOptimalCoefficient n * autocorr f.1 0) ≤ E
  by_cases hE : E = ∞
  · rw [hE]
    exact le_top
  by_cases hR : autocorr f.1 0 = 0
  · simp [hR]
  have hRp : 0 < autocorr f.1 0 := lt_of_le_of_ne (autocorr_zero_nonneg f.1) (Ne.symm hR)
  apply (ENNReal.ofReal_le_iff_le_toReal hE).2
  apply (le_div_iff₀ hRp).1
  apply csSup_le
  · exact ⟨(equalMultiplicity n).pairedCoefficient, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (le_div_iff₀ hRp).2
      ((ENNReal.ofReal_le_iff_le_toReal hE).1 (ρ.pairedCoefficient_source_energy f hcut))

theorem pairedOptimalCoefficient_le_normalized_energy {n m : ℕ}
    (f : SmoothLogarithmicGridSource m) (hcut : (n + 2) ^ 2 ≤ m + 2) :
    pairedOptimalCoefficient n ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 := by
  apply csSup_le
  · exact ⟨(equalMultiplicity n).pairedCoefficient, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact ρ.pairedCoefficient_le_normalized_energy f hcut

theorem pairedOptimalCoefficient_le_collarTailMass (n : ℕ) :
    pairedOptimalCoefficient n ≤ collarTailMass := by
  apply csSup_le
  · exact ⟨(equalMultiplicity n).pairedCoefficient, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    refine ρ.pairedCoefficient_le_physical_mass.trans ?_
    apply setIntegral_mono_set integrableOn_archWeight_collar_tail
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx)).le
    · exact Filter.Eventually.of_forall fun _ hx => hx.1

end PhysicalCollarPartition

/-- Admit a coupled collar certificate exactly when all its cross products are pinned. -/
def productAdmittedCoefficient (n k : ℕ) : ℝ :=
  if (k + 2) ^ 2 ≤ n + 2 then PhysicalCollarPartition.pairedOptimalCoefficient k else 0

theorem productAdmittedCoefficient_nonneg (n k : ℕ) : 0 ≤ productAdmittedCoefficient n k := by
  unfold productAdmittedCoefficient
  split_ifs
  · exact (PhysicalCollarPartition.pairedOptimalCoefficient_pos k).le
  · exact le_rfl

theorem productAdmittedCoefficient_monotone (k : ℕ) :
    Monotone (fun n => productAdmittedCoefficient n k) := by
  intro n m hnm
  by_cases h : (k + 2) ^ 2 ≤ n + 2
  · have hm : (k + 2) ^ 2 ≤ m + 2 := by omega
    simp only [productAdmittedCoefficient, if_pos h, if_pos hm, le_refl]
  · simpa only [productAdmittedCoefficient, if_neg h] using productAdmittedCoefficient_nonneg m k

/-- Best certificate from the full independent grid and every admitted paired grid. -/
def productCoupledCollarCoefficient (n : ℕ) : ℝ :=
  max (PhysicalCollarPartition.optimalCoefficient n)
    ((Finset.range (n + 1)).sup' ⟨0, by simp⟩ (productAdmittedCoefficient n))

theorem optimalCoefficient_le_productCoupled (n : ℕ) :
    PhysicalCollarPartition.optimalCoefficient n ≤ productCoupledCollarCoefficient n := le_max_left _ _

theorem pairedOptimalCoefficient_le_productCoupled {n k : ℕ} (hcut : (k + 2) ^ 2 ≤ n + 2) :
    PhysicalCollarPartition.pairedOptimalCoefficient k ≤ productCoupledCollarCoefficient n := by
  have hk : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by nlinarith)
  have h := Finset.le_sup' (productAdmittedCoefficient n) hk
  rw [productAdmittedCoefficient, if_pos hcut] at h
  exact h.trans (le_max_right _ _)

theorem productCoupledCollarCoefficient_pos (n : ℕ) : 0 < productCoupledCollarCoefficient n :=
  (PhysicalCollarPartition.optimalCoefficient_pos n).trans_le (optimalCoefficient_le_productCoupled n)

theorem productCoupledCollarCoefficient_monotone : Monotone productCoupledCollarCoefficient := by
  intro n m hnm
  apply max_le_max (PhysicalCollarPartition.optimalCoefficient_monotone hnm)
  apply Finset.sup'_le
  intro k hk
  refine (productAdmittedCoefficient_monotone k hnm).trans
    (Finset.le_sup' (productAdmittedCoefficient m) ?_)
  apply Finset.mem_range.mpr
  have hk' := Finset.mem_range.mp hk
  omega

/-- An unconditional monotone coupled bound for the normalized energy of each grid source. -/
theorem productCoupledCollarCoefficient_le_normalized_energy (n : ℕ)
    (f : SmoothLogarithmicGridSource n) :
    productCoupledCollarCoefficient n ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 := by
  apply max_le (optimalCoefficient_le_normalized_energy n f)
  apply Finset.sup'_le
  intro k _
  unfold productAdmittedCoefficient
  split_ifs with hcut
  · exact PhysicalCollarPartition.pairedOptimalCoefficient_le_normalized_energy f hcut
  · exact div_nonneg (biScaleLevyEnergy_nonneg f.1.1.hasCompactSupport f.1.1.continuous) f.2.2.le

theorem productCoupledCollarCoefficient_le_collarTailMass (n : ℕ) :
    productCoupledCollarCoefficient n ≤ collarTailMass := by
  apply max_le (optimalCoefficient_le_collarTailMass n)
  apply Finset.sup'_le
  intro k _
  unfold productAdmittedCoefficient
  split_ifs
  · exact PhysicalCollarPartition.pairedOptimalCoefficient_le_collarTailMass k
  · exact ((PhysicalCollarPartition.optimalCoefficient_pos 0).trans_le
      (optimalCoefficient_le_collarTailMass 0)).le

theorem productCoupledCollarCoefficient_bddAbove :
    BddAbove (Set.range productCoupledCollarCoefficient) :=
  ⟨collarTailMass, by rintro c ⟨n, rfl⟩; exact productCoupledCollarCoefficient_le_collarTailMass n⟩

/-- Finite limit of the product-coupled source certificates. -/
def limitingProductCoupledCoefficient : ℝ := ⨆ n, productCoupledCollarCoefficient n

theorem limitingProductCoupledCoefficient_bounds :
    0 < limitingProductCoupledCoefficient ∧ limitingProductCoupledCoefficient ≤ collarTailMass := by
  constructor
  · exact (productCoupledCollarCoefficient_pos 0).trans_le
      (le_ciSup productCoupledCollarCoefficient_bddAbove 0)
  · exact ciSup_le (fun n => productCoupledCollarCoefficient_le_collarTailMass n)

theorem productCoupledCollarCoefficient_tendsto :
    Filter.Tendsto productCoupledCollarCoefficient Filter.atTop (nhds limitingProductCoupledCoefficient) :=
  tendsto_atTop_ciSup productCoupledCollarCoefficient_monotone productCoupledCollarCoefficient_bddAbove

end
end GaloisForLFunctions.BiScaleUncertainty
