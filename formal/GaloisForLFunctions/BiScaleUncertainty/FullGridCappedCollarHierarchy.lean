import GaloisForLFunctions.BiScaleUncertainty.CappedCollarCutoffComparison

/-!
# Monotone full-grid capped certificates and quantitative saturation

Optimizing full physical collars with a product-admitted low cutoff improves the
previous truncated paired hierarchy. Extension and constraint growth prove actual
monotonicity. The all-low endpoint supplies the matching upper comparison, so the
new hierarchy has the same finite limit and an explicit fourth-root cutoff error.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

namespace PhysicalCollarPartition

def cappedOptimalCoefficient (n k : ℕ) : ℝ :=
  sSup (Set.range (fun ρ : PhysicalCollarPartition n => ρ.cappedCoefficient k))

theorem cappedCoefficient_range_bddAbove {n k : ℕ} (hk : k ≤ n) :
    BddAbove (Set.range (fun ρ : PhysicalCollarPartition n => ρ.cappedCoefficient k)) := by
  refine ⟨pairedOptimalCoefficient n, ?_⟩
  rintro c ⟨ρ, rfl⟩
  exact (ρ.cappedCoefficient_le_pairedCoefficient hk).trans ρ.pairedCoefficient_le_optimal

theorem cappedCoefficient_le_optimal {n k : ℕ} (ρ : PhysicalCollarPartition n) (hk : k ≤ n) :
    ρ.cappedCoefficient k ≤ cappedOptimalCoefficient n k :=
  le_csSup (cappedCoefficient_range_bddAbove hk) ⟨ρ, rfl⟩

theorem optimalCoefficient_le_cappedOptimalCoefficient {n k : ℕ} (hk : k ≤ n) :
    optimalCoefficient n ≤ cappedOptimalCoefficient n k := by
  apply csSup_le
  · exact ⟨(equalMultiplicity n).coefficient, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (ρ.coefficient_le_cappedCoefficient hk).trans (ρ.cappedCoefficient_le_optimal hk)

theorem cappedOptimalCoefficient_le_pairedOptimalCoefficient {n k : ℕ} (hk : k ≤ n) :
    cappedOptimalCoefficient n k ≤ pairedOptimalCoefficient n := by
  apply csSup_le
  · exact ⟨(equalMultiplicity n).cappedCoefficient k, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (ρ.cappedCoefficient_le_pairedCoefficient hk).trans ρ.pairedCoefficient_le_optimal

/-- The optimized full grid includes every extended all-low partition. -/
theorem pairedOptimalCoefficient_le_cappedOptimalCoefficient {n k : ℕ} (hk : k ≤ n) :
    pairedOptimalCoefficient k ≤ cappedOptimalCoefficient n k := by
  apply csSup_le
  · exact ⟨(equalMultiplicity k).pairedCoefficient, equalMultiplicity k, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    change ρ.pairedCoefficient ≤ cappedOptimalCoefficient n k
    rw [← ρ.cappedCoefficient_all_low]
    exact (ρ.cappedCoefficient_le_extend hk le_rfl le_rfl hk).trans
      ((ρ.extend hk).cappedCoefficient_le_optimal hk)

/-- Both physical endpoint growth and constraint growth improve the actual optimum. -/
theorem cappedOptimalCoefficient_monotone_cutoffs {n m k l : ℕ}
    (hnm : n ≤ m) (hk : k ≤ n) (hkl : k ≤ l) (hlm : l ≤ m) :
    cappedOptimalCoefficient n k ≤ cappedOptimalCoefficient m l := by
  apply csSup_le
  · exact ⟨(equalMultiplicity n).cappedCoefficient k, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (ρ.cappedCoefficient_le_extend hnm hk hkl hlm).trans
      ((ρ.extend hnm).cappedCoefficient_le_optimal hlm)

/-- Supremum transfer retains the full physical interval and infinite-energy cases. -/
theorem cappedOptimalCoefficient_source_energy {n k : ℕ} (f : LogarithmicGridSource n)
    (hcut : (k + 2) ^ 2 ≤ n + 2) :
    ENNReal.ofReal (cappedOptimalCoefficient n k * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  let E := ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
    continuousArchIncrementDensity (compactAutocorrKernel f.1) x
  change ENNReal.ofReal (cappedOptimalCoefficient n k * autocorr f.1 0) ≤ E
  by_cases hE : E = ∞
  · rw [hE]
    exact le_top
  by_cases hR : autocorr f.1 0 = 0
  · simp [hR]
  have hRp : 0 < autocorr f.1 0 := lt_of_le_of_ne (autocorr_zero_nonneg f.1) (Ne.symm hR)
  apply (ENNReal.ofReal_le_iff_le_toReal hE).2
  apply (le_div_iff₀ hRp).1
  apply csSup_le
  · exact ⟨(equalMultiplicity n).cappedCoefficient k, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (le_div_iff₀ hRp).2
      ((ENNReal.ofReal_le_iff_le_toReal hE).1 (ρ.cappedCoefficient_source_energy f hcut))

theorem cappedOptimalCoefficient_le_normalized_energy {n k : ℕ}
    (f : SmoothLogarithmicGridSource n) (hcut : (k + 2) ^ 2 ≤ n + 2) :
    cappedOptimalCoefficient n k ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 := by
  apply csSup_le
  · exact ⟨(equalMultiplicity n).cappedCoefficient k, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact ρ.cappedCoefficient_le_normalized_energy f hcut

end PhysicalCollarPartition

theorem productAdmittedCutoff_le (n : ℕ) : productAdmittedCutoff n ≤ n := by
  have h := Nat.sqrt_le_self (n + 2)
  unfold productAdmittedCutoff
  omega

theorem productAdmittedCutoff_monotone : Monotone productAdmittedCutoff := by
  intro n m hnm
  have h := Nat.sqrt_le_sqrt (show n + 2 ≤ m + 2 by omega)
  unfold productAdmittedCutoff
  omega

/-- Largest admitted low cutoff with every physical collar retained. Before any
product pair is admitted, use the independent full-grid coefficient. -/
def fullGridCappedCollarCoefficient (n : ℕ) : ℝ :=
  if 2 ≤ n then PhysicalCollarPartition.cappedOptimalCoefficient n (productAdmittedCutoff n)
  else PhysicalCollarPartition.optimalCoefficient n

theorem optimalCoefficient_le_fullGridCapped (n : ℕ) :
    PhysicalCollarPartition.optimalCoefficient n ≤ fullGridCappedCollarCoefficient n := by
  unfold fullGridCappedCollarCoefficient
  split_ifs
  · exact PhysicalCollarPartition.optimalCoefficient_le_cappedOptimalCoefficient (productAdmittedCutoff_le n)
  · exact le_rfl

theorem fullGridCappedCollarCoefficient_le_pairedOptimal (n : ℕ) :
    fullGridCappedCollarCoefficient n ≤ PhysicalCollarPartition.pairedOptimalCoefficient n := by
  unfold fullGridCappedCollarCoefficient
  split_ifs
  · exact PhysicalCollarPartition.cappedOptimalCoefficient_le_pairedOptimalCoefficient (productAdmittedCutoff_le n)
  · exact PhysicalCollarPartition.optimalCoefficient_le_pairedOptimalCoefficient n

/-- The full-grid certificate dominates the entire previous paired hierarchy. -/
theorem productCoupled_le_fullGridCapped (n : ℕ) :
    productCoupledCollarCoefficient n ≤ fullGridCappedCollarCoefficient n := by
  by_cases hn : 2 ≤ n
  · rw [productCoupledCollarCoefficient_eq_max hn, fullGridCappedCollarCoefficient, if_pos hn]
    exact max_le
      (PhysicalCollarPartition.optimalCoefficient_le_cappedOptimalCoefficient (productAdmittedCutoff_le n))
      (PhysicalCollarPartition.pairedOptimalCoefficient_le_cappedOptimalCoefficient (productAdmittedCutoff_le n))
  · have hnot (k : ℕ) : ¬(k + 2) ^ 2 ≤ n + 2 := by
      have hn1 : n ≤ 1 := by omega
      intro h
      nlinarith [Nat.zero_le k, Nat.zero_le (k ^ 2)]
    rw [fullGridCappedCollarCoefficient, if_neg hn]
    apply max_le le_rfl
    apply Finset.sup'_le
    intro k _
    rw [productAdmittedCoefficient, if_neg (hnot k)]
    exact (PhysicalCollarPartition.optimalCoefficient_pos n).le

theorem fullGridCappedCollarCoefficient_pos (n : ℕ) : 0 < fullGridCappedCollarCoefficient n :=
  (PhysicalCollarPartition.optimalCoefficient_pos n).trans_le (optimalCoefficient_le_fullGridCapped n)

theorem fullGridCappedCollarCoefficient_monotone : Monotone fullGridCappedCollarCoefficient := by
  intro n m hnm
  by_cases hn : 2 ≤ n
  · have hm : 2 ≤ m := hn.trans hnm
    simp only [fullGridCappedCollarCoefficient, if_pos hn, if_pos hm]
    exact PhysicalCollarPartition.cappedOptimalCoefficient_monotone_cutoffs hnm
      (productAdmittedCutoff_le n) (productAdmittedCutoff_monotone hnm) (productAdmittedCutoff_le m)
  · by_cases hm : 2 ≤ m
    · rw [fullGridCappedCollarCoefficient, if_neg hn]
      exact (PhysicalCollarPartition.optimalCoefficient_monotone hnm).trans
        (optimalCoefficient_le_fullGridCapped m)
    · simp only [fullGridCappedCollarCoefficient, if_neg hn, if_neg hm]
      exact PhysicalCollarPartition.optimalCoefficient_monotone hnm

theorem fullGridCappedCollarCoefficient_source_energy {n : ℕ} (f : LogarithmicGridSource n) :
    ENNReal.ofReal (fullGridCappedCollarCoefficient n * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  unfold fullGridCappedCollarCoefficient
  split_ifs with hn
  · exact PhysicalCollarPartition.cappedOptimalCoefficient_source_energy f (productAdmittedCutoff_admitted hn)
  · exact PhysicalCollarPartition.optimalCoefficient_source_energy f

theorem fullGridCappedCollarCoefficient_le_normalized_energy (n : ℕ)
    (f : SmoothLogarithmicGridSource n) :
    fullGridCappedCollarCoefficient n ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 := by
  unfold fullGridCappedCollarCoefficient
  split_ifs with hn
  · exact PhysicalCollarPartition.cappedOptimalCoefficient_le_normalized_energy f (productAdmittedCutoff_admitted hn)
  · exact optimalCoefficient_le_normalized_energy n f

theorem fullGridCappedCollarCoefficient_le_limit (n : ℕ) :
    fullGridCappedCollarCoefficient n ≤ limitingProductCoupledCoefficient := by
  apply (fullGridCappedCollarCoefficient_le_pairedOptimal n).trans
  rw [limitingProductCoupledCoefficient_eq_iSup_paired]
  exact le_ciSup PhysicalCollarPartition.pairedOptimalCoefficient_bddAbove n

theorem fullGridCappedCollarCoefficient_bddAbove :
    BddAbove (Set.range fullGridCappedCollarCoefficient) :=
  ⟨limitingProductCoupledCoefficient,
    by rintro c ⟨n, rfl⟩; exact fullGridCappedCollarCoefficient_le_limit n⟩

theorem iSup_fullGridCappedCollarCoefficient_eq :
    (⨆ n, fullGridCappedCollarCoefficient n) = limitingProductCoupledCoefficient := by
  apply le_antisymm
  · exact ciSup_le fullGridCappedCollarCoefficient_le_limit
  · unfold limitingProductCoupledCoefficient
    apply ciSup_le
    intro n
    exact (productCoupled_le_fullGridCapped n).trans
      (le_ciSup fullGridCappedCollarCoefficient_bddAbove n)

theorem fullGridCappedCollarCoefficient_tendsto :
    Filter.Tendsto fullGridCappedCollarCoefficient Filter.atTop (nhds limitingProductCoupledCoefficient) := by
  have h := tendsto_atTop_ciSup fullGridCappedCollarCoefficient_monotone fullGridCappedCollarCoefficient_bddAbove
  simpa only [iSup_fullGridCappedCollarCoefficient_eq] using h

theorem fullGridCapped_quantitative_saturation_floor {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ limitingProductCoupledCoefficient - fullGridCappedCollarCoefficient n ∧
      limitingProductCoupledCoefficient - fullGridCappedCollarCoefficient n ≤
        4 * Real.exp (logarithmicCollarRadius / 2) /
          (Real.sqrt (Nat.sqrt (n + 2) : ℝ) * (1 - 2 / ((Nat.sqrt (n + 2) : ℝ) ^ 2))) := by
  have h := productCoupled_quantitative_saturation_floor hn
  constructor <;> linarith [h.2, fullGridCappedCollarCoefficient_le_limit n, productCoupled_le_fullGridCapped n]

theorem fullGridCapped_quantitative_saturation {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ limitingProductCoupledCoefficient - fullGridCappedCollarCoefficient n ∧
      limitingProductCoupledCoefficient - fullGridCappedCollarCoefficient n ≤
        16 * Real.exp (logarithmicCollarRadius / 2) / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) := by
  have h := productCoupled_quantitative_saturation hn
  constructor <;> linarith [h.2, fullGridCappedCollarCoefficient_le_limit n, productCoupled_le_fullGridCapped n]

/-- A stronger finite certificate with the same explicit limiting error, for the
actual source domain and without any source-energy interface premise. -/
theorem fullGridCapped_quantitative_source_certificate {n : ℕ} (hn : 2 ≤ n)
    (f : SmoothLogarithmicGridSource n) :
    (0 ≤ limitingProductCoupledCoefficient - fullGridCappedCollarCoefficient n ∧
      limitingProductCoupledCoefficient - fullGridCappedCollarCoefficient n ≤
        16 * Real.exp (logarithmicCollarRadius / 2) / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ))) ∧
      fullGridCappedCollarCoefficient n ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 :=
  ⟨fullGridCapped_quantitative_saturation hn, fullGridCappedCollarCoefficient_le_normalized_energy n f⟩

end
end GaloisForLFunctions.BiScaleUncertainty
