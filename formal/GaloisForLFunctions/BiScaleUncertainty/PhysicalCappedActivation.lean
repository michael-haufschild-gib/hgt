import GaloisForLFunctions.BiScaleUncertainty.CappedSupportActivation
import GaloisForLFunctions.BiScaleUncertainty.FullGridCappedCollarHierarchy

/-!
# Activation and exact gain of full physical capped collars

The maximum low fractions decide pointwise activation. The rationalized gain
is integrable for every actual physical partition; its integral is zero exactly
when coupling is inactive almost everywhere. Actual source-energy certificates
retain this gain without a source-energy or optimizer premise.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
namespace PhysicalCollarPartition
variable {n : ℕ}

/-- Largest fraction of low-node weight on either physical sign. -/
def maxLowFraction (ρ : PhysicalCollarPartition n) (k : ℕ) (y : ℝ) (σ : Bool) : ℝ :=
  cappedSignLowFraction (logarithmicOddCosets n) (logarithmicOddCosets_nonempty n)
    (ρ.lowBlockSize k y) (ρ.highBlockSize k y) σ

/-- Coupling is inactive exactly when this index is at most one. -/
def cappedActivationIndex (ρ : PhysicalCollarPartition n) (k : ℕ) (y : ℝ) : ℝ :=
  ρ.maxLowFraction k y false ^ 2 + ρ.maxLowFraction k y true ^ 2

theorem maxLowFraction_mem (ρ : PhysicalCollarPartition n) (k : ℕ) (y : ℝ) (σ : Bool) :
    ρ.maxLowFraction k y σ ∈ Icc (0 : ℝ) 1 :=
  cappedSignLowFraction_mem _ _ _ _ (fun _ _ _ => Real.sqrt_nonneg _) σ

theorem cappedAngularSupport_eq_blockNorm_iff (ρ : PhysicalCollarPartition n)
    {k : ℕ} (hk : k ≤ n) (y : ℝ) :
    ρ.cappedAngularSupport k y = ρ.blockNorm y ↔ ρ.cappedActivationIndex k y ≤ 1 := by
  have he := cappedCosetSupport_eq_independent_iff (logarithmicOddCosets n)
    (logarithmicOddCosets_nonempty n) (ρ.lowBlockSize k y) (ρ.highBlockSize k y)
    (fun _ _ _ => Real.sqrt_nonneg _) (fun _ _ _ => Real.sqrt_nonneg _)
  have hs : (∑ σ : Bool, ∑ p ∈ logarithmicOddCosets n,
      Real.sqrt (ρ.lowBlockSize k y σ p ^ 2 + ρ.highBlockSize k y σ p ^ 2)) =
      ρ.blockNorm y := by
    simp_rw [ρ.low_high_blockSize_sq hk]
    rw [ρ.blockNorm_eq_signBlockNorm_add]
    simp only [Fintype.sum_bool, signBlockNorm, blockWeightNorm, add_comm]
  rw [hs] at he
  exact he

theorem cappedKernel_eq_kernel_iff (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) (y : ℝ) :
    ρ.cappedKernel k y = ρ.kernel y ↔ ρ.cappedActivationIndex k y ≤ 1 := by
  rw [← ρ.cappedAngularSupport_eq_blockNorm_iff hk y]
  constructor
  · intro he
    have hs : Real.sqrt (archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2) =
        Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2) := by
      unfold cappedKernel kernel at he
      linarith
    have hsq := (Real.sqrt_inj (by positivity) (by positivity)).1 hs
    nlinarith [ρ.cappedAngularSupport_nonneg k y, ρ.blockNorm_nonneg y]
  · intro he
    unfold cappedKernel kernel
    rw [he]

theorem kernel_lt_cappedKernel_iff (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) (y : ℝ) :
    ρ.kernel y < ρ.cappedKernel k y ↔ 1 < ρ.cappedActivationIndex k y := by
  constructor
  · intro hlt
    by_contra hn
    exact (ne_of_lt hlt) ((ρ.cappedKernel_eq_kernel_iff hk y).2 (le_of_not_gt hn)).symm
  · intro hlt
    exact lt_of_le_of_ne (ρ.kernel_le_cappedKernel hk y)
      (fun he => (not_le_of_gt hlt) ((ρ.cappedKernel_eq_kernel_iff hk y).1 he.symm))

/-- Exact rationalized gain over the independent physical kernel. -/
def cappedCouplingGain (ρ : PhysicalCollarPartition n) (k : ℕ) (y : ℝ) : ℝ :=
  (ρ.blockNorm y ^ 2 - ρ.cappedAngularSupport k y ^ 2) /
    (Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2) +
      Real.sqrt (archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2))

theorem cappedCouplingGain_eq_sub (ρ : PhysicalCollarPartition n) (k : ℕ)
    {y : ℝ} (hy : 0 < y) :
    ρ.cappedCouplingGain k y = ρ.cappedKernel k y - ρ.kernel y := by
  have hw := archLevySinhWeight_pos hy
  have ha : 0 < Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [sq_nonneg (ρ.blockNorm y)])
  have hb := Real.sqrt_nonneg (archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2)
  have hden : Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2) +
      Real.sqrt (archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2) ≠ 0 := by linarith
  have hasq := Real.sq_sqrt (show 0 ≤ archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2 by positivity)
  have hbsq := Real.sq_sqrt (show 0 ≤ archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2 by positivity)
  unfold cappedCouplingGain cappedKernel kernel
  apply (div_eq_iff hden).2
  nlinarith

theorem cappedCouplingGain_nonneg (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) {y : ℝ} (hy : 0 < y) : 0 ≤ ρ.cappedCouplingGain k y := by
  rw [ρ.cappedCouplingGain_eq_sub k hy]
  exact sub_nonneg.mpr (ρ.kernel_le_cappedKernel hk y)

theorem cappedCouplingGain_eq_zero_iff (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) {y : ℝ} (hy : 0 < y) :
    ρ.cappedCouplingGain k y = 0 ↔ ρ.cappedActivationIndex k y ≤ 1 := by
  rw [ρ.cappedCouplingGain_eq_sub k hy, sub_eq_zero, ρ.cappedKernel_eq_kernel_iff hk]

theorem cappedCouplingGain_pos_iff (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) {y : ℝ} (hy : 0 < y) :
    0 < ρ.cappedCouplingGain k y ↔ 1 < ρ.cappedActivationIndex k y := by
  rw [ρ.cappedCouplingGain_eq_sub k hy, sub_pos, ρ.kernel_lt_cappedKernel_iff hk]

theorem measurable_cappedCouplingGain (ρ : PhysicalCollarPartition n) (k : ℕ) :
    Measurable (ρ.cappedCouplingGain k) :=
  ((ρ.measurable_blockNorm.pow_const 2).sub ((ρ.measurable_cappedAngularSupport k).pow_const 2)).div
    ((Real.continuous_sqrt.measurable.comp
      ((measurable_archLevySinhWeight.pow_const 2).add (ρ.measurable_blockNorm.pow_const 2))).add
      (Real.continuous_sqrt.measurable.comp
        ((measurable_archLevySinhWeight.pow_const 2).add ((ρ.measurable_cappedAngularSupport k).pow_const 2))))

theorem integrableOn_cappedCouplingGain (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) : IntegrableOn (ρ.cappedCouplingGain k) (Ioo 0 logarithmicCollarRadius) := by
  apply ((ρ.integrableOn_cappedKernel hk).sub ρ.integrableOn_kernel).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact (ρ.cappedCouplingGain_eq_sub k hy.1).symm

theorem coefficient_add_cappedCouplingGain (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) :
    ρ.coefficient + (∫ y in Ioo 0 logarithmicCollarRadius, ρ.cappedCouplingGain k y) =
      ρ.cappedCoefficient k := by
  have he : (∫ y in Ioo 0 logarithmicCollarRadius, ρ.cappedCouplingGain k y) =
      ∫ y in Ioo 0 logarithmicCollarRadius, (ρ.cappedKernel k y - ρ.kernel y) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact ρ.cappedCouplingGain_eq_sub k hy.1
  rw [he, integral_sub (ρ.integrableOn_cappedKernel hk) ρ.integrableOn_kernel]
  unfold coefficient cappedCoefficient
  ring

/-- No gain exactly when the finite geometric activation test fails almost everywhere. -/
theorem integral_cappedCouplingGain_eq_zero_iff (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) :
    (∫ y in Ioo 0 logarithmicCollarRadius, ρ.cappedCouplingGain k y) = 0 ↔
      ∀ᵐ y ∂volume.restrict (Ioo 0 logarithmicCollarRadius), ρ.cappedActivationIndex k y ≤ 1 := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 logarithmicCollarRadius)] ρ.cappedCouplingGain k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact ρ.cappedCouplingGain_nonneg hk hy.1
  rw [integral_eq_zero_iff_of_nonneg_ae hn (ρ.integrableOn_cappedCouplingGain hk)]
  constructor
  · intro he
    filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with y he hy
    exact (ρ.cappedCouplingGain_eq_zero_iff hk hy.1).1 he
  · intro he
    filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with y he hy
    exact (ρ.cappedCouplingGain_eq_zero_iff hk hy.1).2 he

theorem cappedCoefficient_eq_coefficient_iff (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) : ρ.cappedCoefficient k = ρ.coefficient ↔
      ∀ᵐ y ∂volume.restrict (Ioo 0 logarithmicCollarRadius), ρ.cappedActivationIndex k y ≤ 1 := by
  rw [← ρ.integral_cappedCouplingGain_eq_zero_iff hk]
  have he := ρ.coefficient_add_cappedCouplingGain hk
  constructor <;> intro h <;> linarith

theorem coefficient_lt_cappedCoefficient_iff (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) : ρ.coefficient < ρ.cappedCoefficient k ↔
      ¬∀ᵐ y ∂volume.restrict (Ioo 0 logarithmicCollarRadius), ρ.cappedActivationIndex k y ≤ 1 := by
  constructor
  · intro hlt he
    exact (ne_of_lt hlt) ((ρ.cappedCoefficient_eq_coefficient_iff hk).2 he).symm
  · intro hn
    exact lt_of_le_of_ne (ρ.coefficient_le_cappedCoefficient hk)
      (fun he => hn ((ρ.cappedCoefficient_eq_coefficient_iff hk).1 he.symm))

/-- Extended-energy certificate on the full physical interval, including zero and
infinite-energy sources. The gain is constructed from the actual partition. -/
theorem cappedCouplingGain_source_energy (ρ : PhysicalCollarPartition n) {k : ℕ}
    (f : LogarithmicGridSource n) (hcut : (k + 2) ^ 2 ≤ n + 2) :
    ENNReal.ofReal ((ρ.coefficient +
      ∫ y in Ioo 0 logarithmicCollarRadius, ρ.cappedCouplingGain k y) * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  have hk : k ≤ n := by nlinarith
  rw [ρ.coefficient_add_cappedCouplingGain hk]
  exact ρ.cappedCoefficient_source_energy f hcut

/-- Actual-source gain certificate and its exact inactivity classification at the
largest product-admitted low cutoff. No analytic interface is supplied. -/
theorem fullGrid_activation_source_certificate (hn : 2 ≤ n)
    (ρ : PhysicalCollarPartition n) (f : SmoothLogarithmicGridSource n) :
    (ρ.coefficient + (∫ y in Ioo 0 logarithmicCollarRadius,
      ρ.cappedCouplingGain (productAdmittedCutoff n) y) ≤
        biScaleLevyEnergy f.1.1 / autocorr f.1.1 0) ∧
      (ρ.cappedCoefficient (productAdmittedCutoff n) = ρ.coefficient ↔
        ∀ᵐ y ∂volume.restrict (Ioo 0 logarithmicCollarRadius),
          ρ.cappedActivationIndex (productAdmittedCutoff n) y ≤ 1) := by
  refine ⟨?_, ρ.cappedCoefficient_eq_coefficient_iff (productAdmittedCutoff_le n)⟩
  rw [ρ.coefficient_add_cappedCouplingGain (productAdmittedCutoff_le n)]
  exact ρ.cappedCoefficient_le_normalized_energy f (productAdmittedCutoff_admitted hn)

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
