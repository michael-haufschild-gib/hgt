import GaloisForLFunctions.BiScaleUncertainty.RegularizedGramGeometry
import GaloisForLFunctions.BiScaleUncertainty.PhysicalPriceResponse
import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarMixture

/-!
# Regularized physical full-Gram coefficients

The regularization error is uniformly integrable despite the singular origin
anchor. Actual packet prices define bounded measurable physical prices. Exact
mass and cost transport expose the regularized comparison remainder.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section
variable {n : ℕ}

def regularizedGramKernel (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (ε y : ℝ) : ℝ :=
  AnchoredGram.regularizedKernel f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
    signedGramShift (archLevySinhWeight y) ε

def regularizedGramCoefficient (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (ε : ℝ) : ℝ :=
  ∫ y in Ioo 0 logarithmicCollarRadius, ρ.regularizedGramKernel f ε y

theorem regularizedGramKernel_error (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) (y : ℝ) :
    0 ≤ ρ.signedGramKernel f y - ρ.regularizedGramKernel f ε y ∧
    ρ.signedGramKernel f y - ρ.regularizedGramKernel f ε y ≤ ε * autocorr f 0 :=
  AnchoredGram.regularizedKernel_error f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
    signedGramShift (archLevySinhWeight y) hε

theorem measurable_regularizedGramKernel (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (ε : ℝ) :
    Measurable (ρ.regularizedGramKernel f ε) := by
  have hs := AnchoredGram.measurable_regularizedScale f (signedGramNodes n)
    (fun y p => ρ.weight p.1 p.2 y) signedGramShift archLevySinhWeight ε
    (fun p => ρ.measurable_weight p.1 p.2) measurable_archLevySinhWeight
  have he : ρ.regularizedGramKernel f ε = fun y =>
      autocorr f 0 * (archLevySinhWeight y + ρ.mass y) -
        AnchoredGram.regularizedScale f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
          signedGramShift (archLevySinhWeight y) ε := by
    funext y
    simp only [regularizedGramKernel, AnchoredGram.regularizedKernel, ρ.signedGram_mass]
  rw [he]
  exact ((measurable_archLevySinhWeight.add ρ.measurable_mass).const_mul _).sub hs

theorem integrableOn_regularizedGramKernel (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) : IntegrableOn (ρ.regularizedGramKernel f ε) (Ioo 0 logarithmicCollarRadius) := by
  apply volume.integrableOn_of_bounded (M := 2 * autocorr f 0 * fibreMassBound n + ε * autocorr f 0)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    (ρ.measurable_regularizedGramKernel f ε).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have he := ρ.regularizedGramKernel_error f hε y
  have hk := ρ.signedGramKernel_bounds f hy.1.le
  have hm := mul_le_mul_of_nonneg_left (ρ.mass_le_bound y)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (autocorr_zero_nonneg f))
  change 2 * autocorr f 0 * ρ.mass y ≤ 2 * autocorr f 0 * fibreMassBound n at hm
  have hc := mul_nonneg hε (autocorr_zero_nonneg f)
  have hM := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (autocorr_zero_nonneg f))
    (fibreMassBound_pos n).le
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith only [he.1, he.2, hk.1, hk.2, hm, hc, hM]

/-- The regularization costs at most `ε R` times the fixed collar radius. -/
theorem regularizedGramCoefficient_error (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ ρ.signedGramCoefficient f - ρ.regularizedGramCoefficient f ε ∧
    ρ.signedGramCoefficient f - ρ.regularizedGramCoefficient f ε ≤
      ε * logarithmicCollarRadius * autocorr f 0 := by
  have hi := (ρ.integrableOn_signedGramKernel f).sub (ρ.integrableOn_regularizedGramKernel f hε)
  have hc : IntegrableOn (fun _ : ℝ => ε * autocorr f 0) (Ioo 0 logarithmicCollarRadius) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hn := integral_nonneg
    (f := fun y : ℝ => ρ.signedGramKernel f y - ρ.regularizedGramKernel f ε y)
    (μ := volume.restrict (Ioo 0 logarithmicCollarRadius))
    (fun y => (ρ.regularizedGramKernel_error f hε y).1)
  have hu := integral_mono_ae hi hc
    (Filter.Eventually.of_forall fun y => (ρ.regularizedGramKernel_error f hε y).2)
  rw [integral_sub (ρ.integrableOn_signedGramKernel f)
    (ρ.integrableOn_regularizedGramKernel f hε)] at hn hu
  rw [setIntegral_const, measureReal_def, Real.volume_Ioo, sub_zero,
    ENNReal.toReal_ofReal logarithmicCollarRadius_pos.le, smul_eq_mul] at hu
  exact ⟨hn, by simpa only [regularizedGramCoefficient, signedGramCoefficient, mul_comm,
    mul_left_comm, mul_assoc] using hu⟩

def regularizedGramDualPrice (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (ε : ℝ) (σ : Bool) (k : ℕ) (y : ℝ) : ℝ :=
  AnchoredGram.regularizedPrice f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
    signedGramShift (archLevySinhWeight y) ε (signedGramShift (σ, k))

theorem measurable_regularizedGramDualPrice (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (ε : ℝ) (σ : Bool) (k : ℕ) : Measurable (ρ.regularizedGramDualPrice f ε σ k) :=
  AnchoredGram.measurable_regularizedPrice f (signedGramNodes n) (fun y p => ρ.weight p.1 p.2 y)
    signedGramShift archLevySinhWeight ε (signedGramShift (σ, k))
    (fun p => ρ.measurable_weight p.1 p.2) measurable_archLevySinhWeight

theorem regularizedGramDualPrice_bounds (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (ε : ℝ) (σ : Bool) (k : ℕ) (y : ℝ) :
    0 ≤ ρ.regularizedGramDualPrice f ε σ k y ∧ ρ.regularizedGramDualPrice f ε σ k y ≤ 1 :=
  AnchoredGram.regularizedPrice_bounds f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
    signedGramShift (archLevySinhWeight y) ε (signedGramShift (σ, k))

def regularizedGramPrice (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (ε : ℝ) : CollarPrice where
  value k x := if x < logarithmicCollarNode k then
    ρ.regularizedGramDualPrice f ε false k (logarithmicCollarNode k - x)
    else ρ.regularizedGramDualPrice f ε true k (x - logarithmicCollarNode k)
  measurable_value k := Measurable.ite measurableSet_Iio
    ((ρ.measurable_regularizedGramDualPrice f ε false k).comp (measurable_const.sub measurable_id))
    ((ρ.measurable_regularizedGramDualPrice f ε true k).comp (measurable_id.sub measurable_const))
  bounds := by
    intro k x
    split_ifs <;> exact ρ.regularizedGramDualPrice_bounds f ε _ _ _

theorem regularizedGramPrice_left (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (ε : ℝ) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    (ρ.regularizedGramPrice f ε).value k (logarithmicCollarNode k - y) =
      ρ.regularizedGramDualPrice f ε false k y := by
  change (if _ then _ else _) = _
  rw [if_pos (by linarith)]
  congr 1
  ring

theorem regularizedGramPrice_right (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (ε : ℝ) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    (ρ.regularizedGramPrice f ε).value k (logarithmicCollarNode k + y) =
      ρ.regularizedGramDualPrice f ε true k y := by
  change (if _ then _ else _) = _
  rw [if_neg (by linarith)]
  congr 1
  ring

theorem regularizedGram_fibreCost (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (ε : ℝ) {y : ℝ} (hy : 0 < y) :
    (ρ.regularizedGramPrice f ε).fibreCost η y = ∑ p ∈ signedGramNodes n,
      η.weight p.1 p.2 y * AnchoredGram.regularizedPrice f (signedGramNodes n)
        (fun q => ρ.weight q.1 q.2 y) signedGramShift (archLevySinhWeight y) ε (signedGramShift p) := by
  unfold CollarPrice.fibreCost
  simp_rw [ρ.regularizedGramPrice_left f ε _ hy, ρ.regularizedGramPrice_right f ε _ hy]
  simp [regularizedGramDualPrice, signedGramNodes, Finset.sum_product, Finset.sum_add_distrib, add_comm]

def regularizedGramRemainder (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (ε y : ℝ) : ℝ :=
  ρ.regularizedGramKernel f ε y - η.regularizedGramKernel f ε y +
    2 * autocorr f 0 * (η.mass y - ρ.mass y) -
    2 * autocorr f 0 * ((ρ.regularizedGramPrice f ε).fibreCost η y -
      (ρ.regularizedGramPrice f ε).fibreCost ρ y)

theorem regularizedGramRemainder_eq (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (ε : ℝ) {y : ℝ} (hy : 0 < y) :
    ρ.regularizedGramRemainder η f ε y = AnchoredGram.regularizedRemainder f (signedGramNodes n)
      (fun p => ρ.weight p.1 p.2 y) (fun p => η.weight p.1 p.2 y)
      signedGramShift (archLevySinhWeight y) ε := by
  rw [AnchoredGram.regularizedRemainder_eq_combined, ρ.signedGram_mass, η.signedGram_mass,
    ← ρ.regularizedGram_fibreCost η f ε hy, ← ρ.regularizedGram_fibreCost ρ f ε hy]
  rfl

theorem regularizedGramRemainder_nonneg (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (ε : ℝ) {y : ℝ} (hy : 0 < y) : 0 ≤ ρ.regularizedGramRemainder η f ε y := by
  rw [ρ.regularizedGramRemainder_eq η f ε hy]
  exact AnchoredGram.regularizedRemainder_nonneg f (signedGramNodes n) _ _ _ _ ε

theorem integrableOn_regularizedGramRemainder (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) : IntegrableOn (ρ.regularizedGramRemainder η f ε) (Ioo 0 logarithmicCollarRadius) :=
  (((ρ.integrableOn_regularizedGramKernel f hε).sub (η.integrableOn_regularizedGramKernel f hε)).add
    ((η.integrableOn_mass.sub ρ.integrableOn_mass).const_mul _)).sub
      (((ρ.regularizedGramPrice f ε).integrableOn_fibreCost η).sub
        ((ρ.regularizedGramPrice f ε).integrableOn_fibreCost ρ) |>.const_mul _)

theorem integral_regularizedGramRemainder_nonneg (ρ η : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) (ε : ℝ) :
    0 ≤ ∫ y in Ioo 0 logarithmicCollarRadius, ρ.regularizedGramRemainder η f ε y :=
  setIntegral_nonneg measurableSet_Ioo fun _y hy => ρ.regularizedGramRemainder_nonneg η f ε hy.1

theorem integral_regularizedGramRemainder (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ y in Ioo 0 logarithmicCollarRadius, ρ.regularizedGramRemainder η f ε y) =
      ρ.regularizedGramCoefficient f ε - η.regularizedGramCoefficient f ε -
        2 * autocorr f 0 * ((ρ.regularizedGramPrice f ε).linearCost η -
          (ρ.regularizedGramPrice f ε).linearCost ρ) := by
  unfold regularizedGramRemainder
  rw [integral_sub
    (f := fun y => ρ.regularizedGramKernel f ε y - η.regularizedGramKernel f ε y +
      2 * autocorr f 0 * (η.mass y - ρ.mass y))
    (g := fun y => 2 * autocorr f 0 * ((ρ.regularizedGramPrice f ε).fibreCost η y -
      (ρ.regularizedGramPrice f ε).fibreCost ρ y))
    (((ρ.integrableOn_regularizedGramKernel f hε).sub (η.integrableOn_regularizedGramKernel f hε)).add
      ((η.integrableOn_mass.sub ρ.integrableOn_mass).const_mul _))
    ((((ρ.regularizedGramPrice f ε).integrableOn_fibreCost η).sub
      ((ρ.regularizedGramPrice f ε).integrableOn_fibreCost ρ)).const_mul _),
    integral_add
      (f := fun y => ρ.regularizedGramKernel f ε y - η.regularizedGramKernel f ε y)
      (g := fun y => 2 * autocorr f 0 * (η.mass y - ρ.mass y))
      ((ρ.integrableOn_regularizedGramKernel f hε).sub (η.integrableOn_regularizedGramKernel f hε))
      ((η.integrableOn_mass.sub ρ.integrableOn_mass).const_mul _),
    integral_sub (ρ.integrableOn_regularizedGramKernel f hε) (η.integrableOn_regularizedGramKernel f hε),
    integral_const_mul, integral_const_mul, integral_sub η.integrableOn_mass ρ.integrableOn_mass,
    integral_sub ((ρ.regularizedGramPrice f ε).integrableOn_fibreCost η)
      ((ρ.regularizedGramPrice f ε).integrableOn_fibreCost ρ),
    η.integral_mass, ρ.integral_mass, sub_self, mul_zero, add_zero,
    (ρ.regularizedGramPrice f ε).integral_fibreCost η, (ρ.regularizedGramPrice f ε).integral_fibreCost ρ]
  rfl

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
