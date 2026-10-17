import GaloisForLFunctions.BiScaleUncertainty.SignedGramMinimumResponse
import GaloisForLFunctions.BiScaleUncertainty.SignedGramTrialCertificate

/-!
# Attained physical linear minimum and exact response gain

The minimum-price response attains the incumbent's physical linear minimum.
All equality cases allocate only to active minimum-price collars almost
everywhere. The full measured-Gram gap is the attained greatest linearized
gain, while the actual response gain subtracts the exact norm remainder.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section
variable {n : ℕ}

theorem gramPhysicalCost_minimumResponse (ρ : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    ρ.gramPhysicalCost (ρ.gramMinimumResponse f) f x = ρ.gramFloorCost f x := by
  apply sub_eq_zero.mp
  rw [ρ.gramPhysicalSlack_eq_sum (ρ.gramMinimumResponse f) f hx]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hz : (ρ.gramMinimumResponse f).share k x = 0
  · simp [density, hz]
  · have hp : 0 < (ρ.gramMinimumResponse f).share k x :=
      lt_of_le_of_ne ((ρ.gramMinimumResponse f).nonneg k x) (Ne.symm hz)
    rw [ρ.gramMinimumResponse_price f k x hp, sub_self, mul_zero]

theorem gramPhysicalCost_minimumResponse_le (ρ η : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    ρ.gramPhysicalCost (ρ.gramMinimumResponse f) f x ≤ ρ.gramPhysicalCost η f x := by
  rw [ρ.gramPhysicalCost_minimumResponse f hx]
  exact sub_nonneg.mp (ρ.gramPhysicalSlack_nonneg η f hx)

def gramLinearCost (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) : ℝ :=
  ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), ρ.gramPhysicalCost η f x

theorem gramLinearCost_minimumResponse (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.gramLinearCost (ρ.gramMinimumResponse f) f =
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), ρ.gramFloorCost f x := by
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  exact ρ.gramPhysicalCost_minimumResponse f hx

/-- Cross-slack is precisely the excess over an attained physical linear minimum. -/
theorem gramSlack_eq_linearCost_sub_minimumResponse (ρ η : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) :
    ρ.gramSlack η f = ρ.gramLinearCost η f - ρ.gramLinearCost (ρ.gramMinimumResponse f) f := by
  rw [ρ.gramLinearCost_minimumResponse f]
  exact integral_sub (ρ.integrable_gramPhysicalCost η f).integrableOn
    (ρ.integrableOn_gramFloorCost f)

theorem gramSlack_minimumResponse (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.gramSlack (ρ.gramMinimumResponse f) f = 0 := by
  rw [ρ.gramSlack_eq_linearCost_sub_minimumResponse, sub_self]

theorem gramLinearCost_minimumResponse_le (ρ η : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) :
    ρ.gramLinearCost (ρ.gramMinimumResponse f) f ≤ ρ.gramLinearCost η f := by
  have h := ρ.gramSlack_nonneg η f
  rw [ρ.gramSlack_eq_linearCost_sub_minimumResponse] at h
  exact sub_nonneg.mp h

/-- All minimizing partitions, including fractional allocations among tied collars. -/
theorem gramSlack_eq_zero_iff (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.gramSlack η f = 0 ↔
      ∀ᵐ x ∂volume.restrict (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)),
        ∀ k ∈ Finset.range (n + 1), 0 < η.share k x →
          ρ.gramPhysicalPrice f k x = ρ.gramPriceFloor f x := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n))]
      (fun x => ρ.gramPhysicalCost η f x - ρ.gramFloorCost f x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ρ.gramPhysicalSlack_nonneg η f hx
  have hi := (ρ.integrable_gramPhysicalCost η f).integrableOn.sub (ρ.integrableOn_gramFloorCost f)
  rw [gramSlack, integral_eq_zero_iff_of_nonneg_ae hn hi]
  constructor
  · intro hz
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioo] with x hxzero hx
    intro k hk hshare
    have hsum : (∑ j ∈ Finset.range (n + 1),
        η.density j x * (ρ.gramPhysicalPrice f j x - ρ.gramPriceFloor f x)) = 0 :=
      (ρ.gramPhysicalSlack_eq_sum η f hx).symm.trans hxzero
    have hle := Finset.single_le_sum
      (f := fun j => η.density j x * (ρ.gramPhysicalPrice f j x - ρ.gramPriceFloor f x))
      (fun j hj => ρ.gramPhysicalSlack_term_nonneg η f j hj x) hk
    rw [hsum] at hle
    have hp : 0 < η.density k x :=
      mul_pos hshare (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx.1))
    have hprod := le_antisymm hle (ρ.gramPhysicalSlack_term_nonneg η f k hk x)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hp.ne')
  · intro hcomp
    filter_upwards [hcomp, ae_restrict_mem measurableSet_Ioo] with x hc hx
    change ρ.gramPhysicalCost η f x - ρ.gramFloorCost f x = 0
    rw [ρ.gramPhysicalSlack_eq_sum η f hx]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hz : η.share k x = 0
    · simp [density, hz]
    · have hp : 0 < η.share k x := lt_of_le_of_ne (η.nonneg k x) (Ne.symm hz)
      simp [hc k hk hp]

theorem gramLinearCost_minimum_iff (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.gramLinearCost η f = ρ.gramLinearCost (ρ.gramMinimumResponse f) f ↔
      ∀ᵐ x ∂volume.restrict (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)),
        ∀ k ∈ Finset.range (n + 1), 0 < η.share k x →
          ρ.gramPhysicalPrice f k x = ρ.gramPriceFloor f x := by
  rw [← sub_eq_zero, ← ρ.gramSlack_eq_linearCost_sub_minimumResponse η f]
  exact ρ.gramSlack_eq_zero_iff η f

def gramLinearizedGain (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) : ℝ :=
  2 * autocorr f 0 * (ρ.gramLinearCost ρ f - ρ.gramLinearCost η f)

theorem gramGap_sub_linearizedGain (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.gramGap f - ρ.gramLinearizedGain η f = 2 * autocorr f 0 * ρ.gramSlack η f := by
  rw [gramGap, gramLinearizedGain]
  simp only [gramSlack_eq_linearCost_sub_minimumResponse]
  ring

theorem gramLinearizedGain_le_gap (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.gramLinearizedGain η f ≤ ρ.gramGap f := by
  have h : 0 ≤ 2 * autocorr f 0 * ρ.gramSlack η f :=
    mul_nonneg (mul_nonneg (by norm_num) (autocorr_zero_nonneg f)) (ρ.gramSlack_nonneg η f)
  rw [← ρ.gramGap_sub_linearizedGain η f] at h
  exact sub_nonneg.mp h

theorem gramLinearizedGain_minimumResponse (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.gramLinearizedGain (ρ.gramMinimumResponse f) f = ρ.gramGap f := by
  have h := ρ.gramGap_sub_linearizedGain (ρ.gramMinimumResponse f) f
  rw [ρ.gramSlack_minimumResponse f, mul_zero] at h
  exact (sub_eq_zero.mp h).symm

/-- The gap is an attained maximum over actual feasible physical responses. -/
theorem gramGap_isGreatest_linearizedGain (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    IsGreatest (Set.range (fun η : PhysicalCollarPartition n => ρ.gramLinearizedGain η f))
      (ρ.gramGap f) := by
  constructor
  · exact ⟨ρ.gramMinimumResponse f, ρ.gramLinearizedGain_minimumResponse f⟩
  · rintro c ⟨η, rfl⟩
    exact ρ.gramLinearizedGain_le_gap η f

/-- Actual response gain subtracts its exact, integrable full-Gram curvature remainder. -/
theorem gramMinimumResponse_exact_gain (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    (ρ.gramMinimumResponse f).signedGramCoefficient f - ρ.signedGramCoefficient f =
      ρ.gramGap f - ∫ y in Ioo 0 logarithmicCollarRadius,
        ρ.gramRemainder (ρ.gramMinimumResponse f) f y := by
  have h := ρ.signedGram_exact_dual_gap (ρ.gramMinimumResponse f) f
  rw [ρ.gramSlack_minimumResponse f, mul_zero, zero_add] at h
  linarith only [h]

theorem gramMinimumResponse_improves_iff (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.signedGramCoefficient f < (ρ.gramMinimumResponse f).signedGramCoefficient f ↔
      (∫ y in Ioo 0 logarithmicCollarRadius, ρ.gramRemainder (ρ.gramMinimumResponse f) f y) <
        ρ.gramGap f := by
  have h := ρ.gramMinimumResponse_exact_gain f
  constructor <;> intro hlt <;> linarith only [h, hlt]

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
