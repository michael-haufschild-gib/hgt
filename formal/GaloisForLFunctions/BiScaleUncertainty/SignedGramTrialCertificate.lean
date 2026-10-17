import GaloisForLFunctions.BiScaleUncertainty.SignedGramPhysicalPrices
import GaloisForLFunctions.BiScaleUncertainty.SignedGramCutoffHierarchy

/-!
# Exact trial certificates for full signed-Gram collar optimization

The physical price slack and packet norm remainder give an exact comparison
identity for any two partitions and any actual compact continuous source. A
trial's dual gap bounds all finite allocation improvement. The signed-Gram
cutoff theorem then certifies the limiting optimum with a separate explicit
tail error. No optimizer, packet positivity, or zero-grid premise is assumed.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section
variable {n : ℕ}

def gramFloorCost (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (x : ℝ) : ℝ :=
  archLevySinhWeight x * ρ.gramPriceFloor f x

theorem integrableOn_gramFloorCost (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    IntegrableOn (ρ.gramFloorCost f) (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) := by
  apply volume.integrableOn_of_bounded (M := logarithmicCollarWeightBound n)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    (measurable_archLevySinhWeight.mul (ρ.measurable_gramPriceFloor f)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hw := (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx.1)).le
  change ‖archLevySinhWeight x * ρ.gramPriceFloor f x‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (ρ.gramPriceFloor_nonneg f x))]
  exact (mul_le_of_le_one_right hw (ρ.gramPriceFloor_le_one f x)).trans (archWeight_le_physical_bound hx)

theorem gramPhysicalSlack_eq_sum (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    ρ.gramPhysicalCost η f x - ρ.gramFloorCost f x = ∑ k ∈ Finset.range (n + 1),
      η.density k x * (ρ.gramPhysicalPrice f k x - ρ.gramPriceFloor f x) := by
  have hm : (∑ k ∈ Finset.range (n + 1), η.density k x) = archLevySinhWeight x := by
    simp only [density, ← Finset.sum_mul, η.partition, indicator_of_mem hx, one_mul]
  simp only [gramPhysicalCost, gramFloorCost, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hm]

theorem gramPhysicalSlack_term_nonneg (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (k : ℕ) (hk : k ∈ Finset.range (n + 1)) (x : ℝ) :
    0 ≤ η.density k x * (ρ.gramPhysicalPrice f k x - ρ.gramPriceFloor f x) := by
  by_cases hxk : x ∈ logarithmicPhysicalCollar n k
  · exact mul_nonneg (η.density_nonneg k x) (sub_nonneg.mpr (ρ.gramPriceFloor_le_active f k hk hxk))
  · simp [density, η.supported k x hxk]

theorem gramPhysicalSlack_nonneg (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    0 ≤ ρ.gramPhysicalCost η f x - ρ.gramFloorCost f x := by
  rw [ρ.gramPhysicalSlack_eq_sum η f hx]
  exact Finset.sum_nonneg fun k hk => ρ.gramPhysicalSlack_term_nonneg η f k hk x

def gramSlack (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) : ℝ :=
  ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n),
    ρ.gramPhysicalCost η f x - ρ.gramFloorCost f x

def gramGap (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) : ℝ :=
  2 * autocorr f 0 * ρ.gramSlack ρ f

theorem gramSlack_nonneg (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    0 ≤ ρ.gramSlack η f :=
  setIntegral_nonneg measurableSet_Ioo fun _ hx => ρ.gramPhysicalSlack_nonneg η f hx

theorem gramGap_nonneg (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) : 0 ≤ ρ.gramGap f :=
  mul_nonneg (mul_nonneg (by norm_num) (autocorr_zero_nonneg f)) (ρ.gramSlack_nonneg ρ f)

theorem gramSlack_self_eq_zero_iff (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.gramSlack ρ f = 0 ↔
      ∀ᵐ x ∂volume.restrict (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)),
        ∀ k ∈ Finset.range (n + 1), 0 < ρ.share k x → ρ.gramPhysicalPrice f k x = ρ.gramPriceFloor f x := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n))]
      (fun x => ρ.gramPhysicalCost ρ f x - ρ.gramFloorCost f x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ρ.gramPhysicalSlack_nonneg ρ f hx
  have hi := (ρ.integrable_gramPhysicalCost ρ f).integrableOn.sub (ρ.integrableOn_gramFloorCost f)
  rw [gramSlack, integral_eq_zero_iff_of_nonneg_ae hn hi]
  constructor
  · intro hz
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioo] with x hxzero hx
    intro k hk hshare
    have hsum : (∑ j ∈ Finset.range (n + 1),
        ρ.density j x * (ρ.gramPhysicalPrice f j x - ρ.gramPriceFloor f x)) = 0 :=
      (ρ.gramPhysicalSlack_eq_sum ρ f hx).symm.trans hxzero
    have hle := Finset.single_le_sum
      (f := fun j => ρ.density j x * (ρ.gramPhysicalPrice f j x - ρ.gramPriceFloor f x))
      (fun j hj => ρ.gramPhysicalSlack_term_nonneg ρ f j hj x) hk
    rw [hsum] at hle
    have hp : 0 < ρ.density k x :=
      mul_pos hshare (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx.1))
    have hprod := le_antisymm hle (ρ.gramPhysicalSlack_term_nonneg ρ f k hk x)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hp.ne')
  · intro hcomp
    filter_upwards [hcomp, ae_restrict_mem measurableSet_Ioo] with x hc hx
    change ρ.gramPhysicalCost ρ f x - ρ.gramFloorCost f x = 0
    rw [ρ.gramPhysicalSlack_eq_sum ρ f hx]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hz : ρ.share k x = 0
    · simp [density, hz]
    · have hp : 0 < ρ.share k x := lt_of_le_of_ne (ρ.nonneg k x) (Ne.symm hz)
      simp [hc k hk hp]

/-- Zero-gap factorization with zero source energy displayed explicitly. -/
theorem gramGap_eq_zero_iff (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.gramGap f = 0 ↔ autocorr f 0 = 0 ∨
      ∀ᵐ x ∂volume.restrict (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)),
        ∀ k ∈ Finset.range (n + 1), 0 < ρ.share k x → ρ.gramPhysicalPrice f k x = ρ.gramPriceFloor f x := by
  rw [gramGap, mul_eq_zero, mul_eq_zero, ρ.gramSlack_self_eq_zero_iff f]
  norm_num

def gramRemainder (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) : ℝ :=
  AnchoredGram.dualRemainder f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
    (fun p => η.weight p.1 p.2 y) signedGramShift (archLevySinhWeight y)

theorem gramRemainder_nonneg (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    0 ≤ ρ.gramRemainder η f y :=
  AnchoredGram.dualRemainder_nonneg f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
    (fun p => η.weight p.1 p.2 y) signedGramShift (archLevySinhWeight y)

theorem gramRemainder_eq_combined (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    ρ.gramRemainder η f y = ρ.signedGramKernel f y - η.signedGramKernel f y +
      2 * autocorr f 0 * (η.mass y - ρ.mass y) -
      2 * autocorr f 0 * (ρ.gramFibreCost η f y - ρ.gramFibreCost ρ f y) := by
  unfold gramRemainder
  rw [AnchoredGram.dualRemainder_eq_combined, ρ.signedGram_mass, η.signedGram_mass,
    ← ρ.gramFibreCost_eq_signed_sum η f y, ← ρ.gramFibreCost_eq_signed_sum ρ f y]
  rfl

theorem integrableOn_gramRemainder (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    IntegrableOn (ρ.gramRemainder η f) (Ioo 0 logarithmicCollarRadius) := by
  have he : ρ.gramRemainder η f = fun y => ρ.signedGramKernel f y - η.signedGramKernel f y +
      2 * autocorr f 0 * (η.mass y - ρ.mass y) -
      2 * autocorr f 0 * (ρ.gramFibreCost η f y - ρ.gramFibreCost ρ f y) :=
    funext (ρ.gramRemainder_eq_combined η f)
  rw [he]
  exact (((ρ.integrableOn_signedGramKernel f).sub (η.integrableOn_signedGramKernel f)).add
    ((η.integrableOn_mass.sub ρ.integrableOn_mass).const_mul _)).sub
      (((ρ.integrableOn_gramFibreCost η f).sub (ρ.integrableOn_gramFibreCost ρ f)).const_mul _)

theorem integral_gramRemainder_nonneg (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    0 ≤ ∫ y in Ioo 0 logarithmicCollarRadius, ρ.gramRemainder η f y :=
  integral_nonneg (ρ.gramRemainder_nonneg η f)

theorem integral_gramRemainder (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    (∫ y in Ioo 0 logarithmicCollarRadius, ρ.gramRemainder η f y) =
      ρ.signedGramCoefficient f - η.signedGramCoefficient f - 2 * autocorr f 0 *
        ((∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), ρ.gramPhysicalCost η f x) -
         (∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), ρ.gramPhysicalCost ρ f x)) := by
  simp_rw [ρ.gramRemainder_eq_combined η f]
  rw [integral_sub
    (f := fun y => ρ.signedGramKernel f y - η.signedGramKernel f y + 2 * autocorr f 0 * (η.mass y - ρ.mass y))
    (g := fun y => 2 * autocorr f 0 * (ρ.gramFibreCost η f y - ρ.gramFibreCost ρ f y))
    (((ρ.integrableOn_signedGramKernel f).sub (η.integrableOn_signedGramKernel f)).add
      ((η.integrableOn_mass.sub ρ.integrableOn_mass).const_mul _))
    (((ρ.integrableOn_gramFibreCost η f).sub (ρ.integrableOn_gramFibreCost ρ f)).const_mul _),
    integral_add
      (f := fun y => ρ.signedGramKernel f y - η.signedGramKernel f y)
      (g := fun y => 2 * autocorr f 0 * (η.mass y - ρ.mass y))
      ((ρ.integrableOn_signedGramKernel f).sub (η.integrableOn_signedGramKernel f))
      ((η.integrableOn_mass.sub ρ.integrableOn_mass).const_mul _),
    integral_sub (ρ.integrableOn_signedGramKernel f) (η.integrableOn_signedGramKernel f),
    integral_const_mul, integral_const_mul,
    integral_sub η.integrableOn_mass ρ.integrableOn_mass,
    integral_sub (ρ.integrableOn_gramFibreCost η f) (ρ.integrableOn_gramFibreCost ρ f),
    η.integral_mass, ρ.integral_mass, sub_self, mul_zero, add_zero,
    ρ.integral_gramFibreCost η f, ρ.integral_gramFibreCost ρ f]
  rfl

/-- Exact physical duality for actual sources, retaining every measured Gram entry. -/
theorem signedGram_exact_dual_gap (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.signedGramCoefficient f + ρ.gramGap f - η.signedGramCoefficient f =
      2 * autocorr f 0 * ρ.gramSlack η f +
        ∫ y in Ioo 0 logarithmicCollarRadius, ρ.gramRemainder η f y := by
  have h := ρ.integral_gramRemainder η f
  unfold gramGap gramSlack
  rw [integral_sub (ρ.integrable_gramPhysicalCost ρ f).integrableOn (ρ.integrableOn_gramFloorCost f),
    integral_sub (ρ.integrable_gramPhysicalCost η f).integrableOn (ρ.integrableOn_gramFloorCost f)]
  nlinarith only [h]

theorem signedGramCoefficient_le_dual_bound (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    η.signedGramCoefficient f ≤ ρ.signedGramCoefficient f + ρ.gramGap f := by
  have h := ρ.signedGram_exact_dual_gap η f
  have hs : 0 ≤ 2 * autocorr f 0 * ρ.gramSlack η f :=
    mul_nonneg (mul_nonneg (by norm_num) (autocorr_zero_nonneg f)) (ρ.gramSlack_nonneg η f)
  have hr := ρ.integral_gramRemainder_nonneg η f
  linarith only [h, hs, hr]

theorem signedGramOptimalCoefficient_gap_bounds (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    0 ≤ signedGramOptimalCoefficient f n - ρ.signedGramCoefficient f ∧
      signedGramOptimalCoefficient f n - ρ.signedGramCoefficient f ≤ ρ.gramGap f := by
  have hl := ρ.signedGramCoefficient_le_optimal f
  have hu : signedGramOptimalCoefficient f n ≤ ρ.signedGramCoefficient f + ρ.gramGap f := by
    apply csSup_le
    · exact ⟨ρ.signedGramCoefficient f, ρ, rfl⟩
    · rintro c ⟨η, rfl⟩
      exact ρ.signedGramCoefficient_le_dual_bound η f
  constructor <;> linarith only [hl, hu]

theorem signedGram_optimal_of_gap_zero (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (h : ρ.gramGap f = 0) : ρ.signedGramCoefficient f = signedGramOptimalCoefficient f n := by
  have hb := ρ.signedGramOptimalCoefficient_gap_bounds f
  linarith only [hb.1, hb.2, h]

/-- Allocation error and physical cutoff error are certified separately by any trial. -/
theorem limitingSignedGramCoefficient_trial_bounds (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    0 ≤ limitingSignedGramCoefficient f - ρ.signedGramCoefficient f ∧
      limitingSignedGramCoefficient f - ρ.signedGramCoefficient f ≤
        ρ.gramGap f + 2 * autocorr f 0 * collarCutoffTailMass n := by
  have hg := ρ.signedGramOptimalCoefficient_gap_bounds f
  have ht := limitingSignedGramCoefficient_sub_bounds f n
  constructor <;> linarith only [hg.1, hg.2, ht.1, ht.2]

theorem limitingSignedGramNormalized_trial_bounds (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    0 ≤ limitingSignedGramCoefficient f / autocorr f 0 - ρ.signedGramCoefficient f / autocorr f 0 ∧
      limitingSignedGramCoefficient f / autocorr f 0 - ρ.signedGramCoefficient f / autocorr f 0 ≤
        ρ.gramGap f / autocorr f 0 + 8 * Real.exp (logarithmicCollarRadius / 2) /
          (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2))) := by
  have hg := ρ.signedGramOptimalCoefficient_gap_bounds f
  have hgn := div_nonneg hg.1 (autocorr_zero_nonneg f)
  have hgu := div_le_div_of_nonneg_right hg.2 (autocorr_zero_nonneg f)
  rw [sub_div] at hgn hgu
  have ht := signedGramNormalizedCoefficient_quantitative_saturation f n
  constructor <;> linarith only [hgn, hgu, ht.1, ht.2]

/-- A concrete trial lower bound, its limiting error certificate, and actual source energy. -/
theorem signedGram_trial_source_certificate (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ENNReal.ofReal (ρ.signedGramCoefficient f) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n), continuousArchIncrementDensity (compactAutocorrKernel f) x ∧
    0 ≤ limitingSignedGramCoefficient f - ρ.signedGramCoefficient f ∧
    limitingSignedGramCoefficient f - ρ.signedGramCoefficient f ≤
      ρ.gramGap f + 2 * autocorr f 0 * collarCutoffTailMass n :=
  ⟨ρ.signedGramCoefficient_source_energy f, ρ.limitingSignedGramCoefficient_trial_bounds f⟩

/-- Normalized actual energy and a quantitative certificate for any finite trial. -/
theorem signedGram_trial_normalized_source_certificate (ρ : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    ρ.signedGramCoefficient f / autocorr f 0 ≤ limitingSignedGramCoefficient f / autocorr f 0 ∧
    limitingSignedGramCoefficient f / autocorr f 0 ≤ biScaleLevyEnergy f / autocorr f 0 ∧
    limitingSignedGramCoefficient f / autocorr f 0 - ρ.signedGramCoefficient f / autocorr f 0 ≤
      ρ.gramGap f / autocorr f 0 + 8 * Real.exp (logarithmicCollarRadius / 2) /
        (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2))) := by
  have ht := ρ.limitingSignedGramNormalized_trial_bounds f
  exact ⟨sub_nonneg.mp ht.1, (signedGram_actual_source_certificate f hf n).2, ht.2⟩

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
