import GaloisForLFunctions.BiScaleUncertainty.UniformPairedCollarGain
import GaloisForLFunctions.BiScaleUncertainty.PairedCollarCutoffStability
import GaloisForLFunctions.BiScaleUncertainty.SharpCollarAsymptotics

/-!
# Strict separation of independent and paired allocation limits

The unavoidable first-collar gain survives both optimization and cutoff limits.
Consequently the delayed product-coupled hierarchy eventually selects its paired
branch and gives actual grid-source bounds above the independent limiting optimum.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

theorem PhysicalCollarPartition.optimalCoefficient_add_uniformGap_le_paired {n : ℕ}
    (hn : 1 ≤ n) :
    PhysicalCollarPartition.optimalCoefficient n + uniformPairedCollarGap ≤
      PhysicalCollarPartition.pairedOptimalCoefficient n := by
  have h : PhysicalCollarPartition.optimalCoefficient n ≤
      PhysicalCollarPartition.pairedOptimalCoefficient n - uniformPairedCollarGap := by
    apply csSup_le
    · exact ⟨(PhysicalCollarPartition.equalMultiplicity n).coefficient,
        PhysicalCollarPartition.equalMultiplicity n, rfl⟩
    · rintro c ⟨ρ, rfl⟩
      have hg := ρ.coefficient_add_uniformGap_le_paired hn
      have ho := ρ.pairedCoefficient_le_optimal
      linarith
  linarith

theorem limitingCollarCoefficient_add_uniformGap_le_product :
    limitingCollarCoefficient + uniformPairedCollarGap ≤ limitingProductCoupledCoefficient := by
  have hp : Tendsto (fun n => PhysicalCollarPartition.optimalCoefficient n + uniformPairedCollarGap)
      atTop (𝓝 (limitingCollarCoefficient + uniformPairedCollarGap)) :=
    optimalCoefficient_tendsto.add tendsto_const_nhds
  apply le_of_tendsto_of_tendsto hp pairedOptimalCoefficient_tendsto
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact PhysicalCollarPartition.optimalCoefficient_add_uniformGap_le_paired hn

/-- Coupling opposite signed cosets strictly improves the limiting optimum. -/
theorem limitingCollarCoefficient_lt_limitingProductCoupled :
    limitingCollarCoefficient < limitingProductCoupledCoefficient := by
  linarith [limitingCollarCoefficient_add_uniformGap_le_product, uniformPairedCollarGap_pos]

theorem eventually_productCoupled_gt_independent_limit :
    ∀ᶠ n : ℕ in atTop,
      limitingCollarCoefficient + uniformPairedCollarGap / 2 < productCoupledCollarCoefficient n := by
  apply (tendsto_order.mp productCoupledCollarCoefficient_tendsto).1
  linarith [limitingCollarCoefficient_add_uniformGap_le_product, uniformPairedCollarGap_pos]

/-- After a finite cutoff, the independent branch never wins the product-admitted maximum. -/
theorem eventually_productCoupled_eq_paired :
    ∀ᶠ n : ℕ in atTop, productCoupledCollarCoefficient n =
      PhysicalCollarPartition.pairedOptimalCoefficient (productAdmittedCutoff n) := by
  filter_upwards [eventually_productCoupled_gt_independent_limit, eventually_ge_atTop 2] with n hg hn
  have hp : PhysicalCollarPartition.optimalCoefficient n ≤ limitingCollarCoefficient :=
    sub_nonneg.mp (limitingCollarCoefficient_sub_bounds n).1
  have hs : PhysicalCollarPartition.optimalCoefficient n < productCoupledCollarCoefficient n := by
    linarith [uniformPairedCollarGap_pos]
  have he := productCoupledCollarCoefficient_eq_max hn
  have hpair : PhysicalCollarPartition.optimalCoefficient n ≤
      PhysicalCollarPartition.pairedOptimalCoefficient (productAdmittedCutoff n) := by
    by_contra h
    have hq := (lt_of_not_ge h).le
    have hc : productCoupledCollarCoefficient n ≤ PhysicalCollarPartition.optimalCoefficient n := by
      rw [he]
      exact max_le le_rfl hq
    linarith
  rw [he, max_eq_right hpair]

/-- An explicit admitted physical frame improves the independent limit certificate. -/
theorem uniformPaired_source_lower_bound {n m : ℕ} (hn : 6 ≤ n)
    (f : SmoothLogarithmicGridSource m) (hcut : (n + 2) ^ 2 ≤ m + 2) :
    limitingCollarCoefficient + uniformPairedCollarGap - 4 / Real.sqrt ((n + 2 : ℕ) : ℝ) -
      12289 / ((n + 2 : ℕ) : ℝ) ≤
      biScaleLevyEnergy f.1.1 / RHTower.ArchimedeanAnomaly.autocorr f.1.1 0 := by
  have hp := (abs_le.mp (optimalCoefficient_sharp_leading_error hn)).2
  have hg := PhysicalCollarPartition.optimalCoefficient_add_uniformGap_le_paired
    (show 1 ≤ n by omega)
  have hf := PhysicalCollarPartition.pairedOptimalCoefficient_le_normalized_energy f hcut
  linarith

/-- The uniform gain persists after accounting for the delayed source cutoff. -/
theorem uniformPaired_source_fourth_root_bound {n : ℕ} (hn : 2 ≤ n)
    (f : SmoothLogarithmicGridSource n) :
    limitingCollarCoefficient + uniformPairedCollarGap -
      16 * Real.exp (logarithmicCollarRadius / 2) /
        Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) ≤
      biScaleLevyEnergy f.1.1 / RHTower.ArchimedeanAnomaly.autocorr f.1.1 0 := by
  have hg := limitingCollarCoefficient_add_uniformGap_le_product
  have ht := (productCoupled_quantitative_saturation hn).2
  have hf := productCoupledCollarCoefficient_le_normalized_energy n f
  linarith

theorem eventually_source_energy_gt_independent_limit :
    ∀ᶠ n : ℕ in atTop, ∀ f : SmoothLogarithmicGridSource n,
      limitingCollarCoefficient + uniformPairedCollarGap / 2 <
        biScaleLevyEnergy f.1.1 / RHTower.ArchimedeanAnomaly.autocorr f.1.1 0 := by
  filter_upwards [eventually_productCoupled_gt_independent_limit] with n hn
  intro f
  exact hn.trans_le (productCoupledCollarCoefficient_le_normalized_energy n f)

end
end GaloisForLFunctions.BiScaleUncertainty
