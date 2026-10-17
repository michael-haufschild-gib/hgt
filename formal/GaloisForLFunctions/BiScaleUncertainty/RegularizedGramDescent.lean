import GaloisForLFunctions.BiScaleUncertainty.RegularizedPhysicalGram

/-!
# Quantitative damped minimum-price responses

The regularized full-Gram objective has a uniform integrated quadratic
remainder on actual physical partitions. A measurable minimum-price response
therefore yields a certified damped ascent step without Gram coercivity.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

namespace CollarPrice
variable {n : ℕ}
open PhysicalCollarPartition

theorem linearCost_mixture (Q : CollarPrice) (ρ η : PhysicalCollarPartition n) (τ : Icc (0 : ℝ) 1) :
    Q.linearCost (ρ.mixture η τ) = (1 - (τ : ℝ)) * Q.linearCost ρ + (τ : ℝ) * Q.linearCost η := by
  have he : Q.physicalCost (ρ.mixture η τ) = fun x =>
      (1 - (τ : ℝ)) * Q.physicalCost ρ x + (τ : ℝ) * Q.physicalCost η x := by
    funext x
    simp only [physicalCost, mixture_density, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold linearCost
  rw [he, integral_add ((Q.integrable_physicalCost ρ).integrableOn.const_mul _)
    ((Q.integrable_physicalCost η).integrableOn.const_mul _), integral_const_mul, integral_const_mul]

end CollarPrice

namespace PhysicalCollarPartition
variable {n : ℕ}

def regularizedCurvature (f : C_c(ℝ, ℝ)) (n : ℕ) (ε : ℝ) : ℝ :=
  2 * autocorr f 0 * fibreMassBound n * transportedMass n / ε

theorem regularizedCurvature_nonneg (f : C_c(ℝ, ℝ)) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ regularizedCurvature f n ε := by
  unfold regularizedCurvature
  positivity [autocorr_zero_nonneg f, fibreMassBound_pos n, transportedMass_nonneg n]

theorem regularizedGramRemainder_mixture_le (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {ε : ℝ} (hε : 0 < ε) (τ : Icc (0 : ℝ) 1) {y : ℝ} (hy : 0 < y) :
    ρ.regularizedGramRemainder (ρ.mixture η τ) f ε y ≤
      (autocorr f 0 * fibreMassBound n / ε * (τ : ℝ) ^ 2) * (ρ.mass y + η.mass y) := by
  have hr := AnchoredGram.regularizedRemainder_le f (signedGramNodes n)
    (fun p => ρ.weight p.1 p.2 y) (fun p => (ρ.mixture η τ).weight p.1 p.2 y)
    signedGramShift (archLevySinhWeight y) hε
  rw [← ρ.regularizedGramRemainder_eq (ρ.mixture η τ) f ε hy] at hr
  change ρ.regularizedGramRemainder (ρ.mixture η τ) f ε y ≤
    ‖ρ.gramPacket f y - (ρ.mixture η τ).gramPacket f y‖ ^ 2 / (2 * ε) at hr
  rw [ρ.mixture_gramPacket_displacement_sq η f τ y] at hr
  calc
    _ ≤ (τ : ℝ) ^ 2 * ‖ρ.gramPacket f y - η.gramPacket f y‖ ^ 2 / (2 * ε) := hr
    _ ≤ (τ : ℝ) ^ 2 * (2 * autocorr f 0 * fibreMassBound n * (ρ.mass y + η.mass y)) / (2 * ε) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (ρ.gramPacket_displacement_sq_le η f y)
        (sq_nonneg _)) (by positivity)
    _ = _ := by field_simp; ring

/-- The integrated curvature is explicit in physical mass and smoothing scale. -/
theorem integral_regularizedGramRemainder_mixture_le (ρ η : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε) (τ : Icc (0 : ℝ) 1) :
    (∫ y in Ioo 0 logarithmicCollarRadius, ρ.regularizedGramRemainder (ρ.mixture η τ) f ε y) ≤
      regularizedCurvature f n ε * (τ : ℝ) ^ 2 := by
  have h := integral_mono_ae (ρ.integrableOn_regularizedGramRemainder (ρ.mixture η τ) f hε.le)
    ((ρ.integrableOn_mass.add η.integrableOn_mass).const_mul
      (autocorr f 0 * fibreMassBound n / ε * (τ : ℝ) ^ 2)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      exact ρ.regularizedGramRemainder_mixture_le η f hε τ hy.1)
  rw [integral_const_mul, integral_add ρ.integrableOn_mass η.integrableOn_mass,
    ρ.integral_mass, η.integral_mass] at h
  calc
    _ ≤ (autocorr f 0 * fibreMassBound n / ε * (τ : ℝ) ^ 2) *
        (transportedMass n + transportedMass n) := h
    _ = _ := by unfold regularizedCurvature; ring

def regularizedMinimumResponse (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (ε : ℝ) :
    PhysicalCollarPartition n := (ρ.regularizedGramPrice f ε).minimumResponse n

def regularizedGramGap (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (ε : ℝ) : ℝ :=
  2 * autocorr f 0 * ((ρ.regularizedGramPrice f ε).linearCost ρ -
    (ρ.regularizedGramPrice f ε).linearCost (ρ.regularizedMinimumResponse f ε))

theorem regularizedGramGap_nonneg (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (ε : ℝ) :
    0 ≤ ρ.regularizedGramGap f ε :=
  mul_nonneg (mul_nonneg (by norm_num) (autocorr_zero_nonneg f))
    (sub_nonneg.mpr ((ρ.regularizedGramPrice f ε).linearCost_minimumResponse_le ρ))

/-- Every actual competitor is controlled by the produced linear response. -/
theorem regularizedGram_comparison (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    η.regularizedGramCoefficient f ε - ρ.regularizedGramCoefficient f ε ≤ ρ.regularizedGramGap f ε := by
  have he := ρ.integral_regularizedGramRemainder η f hε
  have hn := ρ.integral_regularizedGramRemainder_nonneg η f ε
  have hc := mul_le_mul_of_nonneg_left ((ρ.regularizedGramPrice f ε).linearCost_minimumResponse_le η)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (autocorr_zero_nonneg f))
  change 2 * autocorr f 0 * (ρ.regularizedGramPrice f ε).linearCost (ρ.regularizedMinimumResponse f ε) ≤ _ at hc
  unfold regularizedGramGap
  nlinarith only [he, hn, hc]

/-- An actual damped response has a source-uniform quadratic error bound. -/
theorem regularizedGram_damped_gain (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {ε : ℝ} (hε : 0 < ε) (τ : Icc (0 : ℝ) 1) :
    (τ : ℝ) * ρ.regularizedGramGap f ε - regularizedCurvature f n ε * (τ : ℝ) ^ 2 ≤
      (ρ.mixture (ρ.regularizedMinimumResponse f ε) τ).regularizedGramCoefficient f ε -
        ρ.regularizedGramCoefficient f ε := by
  have he := ρ.integral_regularizedGramRemainder (ρ.mixture (ρ.regularizedMinimumResponse f ε) τ) f hε.le
  have hu := ρ.integral_regularizedGramRemainder_mixture_le (ρ.regularizedMinimumResponse f ε) f hε τ
  rw [(ρ.regularizedGramPrice f ε).linearCost_mixture] at he
  unfold regularizedGramGap
  nlinarith only [he, hu]

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
