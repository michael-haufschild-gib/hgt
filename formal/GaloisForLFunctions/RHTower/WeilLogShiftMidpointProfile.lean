import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalMassProfile
import GaloisForLFunctions.RHTower.WeilLogShiftMomentFiber

/-! The actual midpoint probability is the normalized absolute raw-weight profile. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilCanonicalMixture_midpoint_abs (r k : ℕ) (i : Fin (r + 2)) :
    finiteWeilCanonicalMixture r k (1 / 2) i =
      |finiteWeilCanonicalCluster r k i| / finiteWeilAbsMass (finiteWeilCanonicalCluster r k) := by
  unfold finiteWeilCanonicalMixture finiteWeilCanonicalPositiveProfile
    finiteWeilCanonicalNegativeProfile finiteWeilPositiveProfile finiteWeilNegativeProfile
  ring

theorem finiteWeilCanonicalMixture_midpoint_raw (r k : ℕ) (i : Fin (r + 2)) :
    finiteWeilCanonicalMixture r k (1 / 2) i =
      |finiteWeilMomentWeights (finiteWeilClusterLogNodes r k) i| /
        finiteWeilAbsMass (finiteWeilMomentWeights (finiteWeilClusterLogNodes r k)) := by
  let W := finiteWeilMomentWeights (finiteWeilClusterLogNodes r k)
  have hW : 0 < ‖W‖ := finiteWeilMomentWeights_norm_pos _
    (finiteWeilClusterLogNodes_injective r k)
  rw [finiteWeilCanonicalMixture_midpoint_abs, finiteWeilCanonicalCluster,
    finiteWeilNormalizedMomentDual_abs_mass _ (finiteWeilClusterLogNodes_injective r k)]
  change |‖W‖⁻¹ * W i| / (finiteWeilAbsMass W / ‖W‖) = |W i| / finiteWeilAbsMass W
  rw [abs_mul, abs_of_pos (inv_pos.mpr hW),
    div_eq_mul_inv (finiteWeilAbsMass W) ‖W‖, mul_comm (finiteWeilAbsMass W)]
  exact mul_div_mul_left _ _ (inv_ne_zero hW.ne')

theorem finiteWeilCanonicalMixture_midpoint_profile (r k : ℕ) (i : Fin (r + 2)) :
    finiteWeilCanonicalMixture r k (1 / 2) i =
      finiteWeilCanonicalMassProfile r k i / (∑ j, finiteWeilCanonicalMassProfile r k j) := by
  let B := ‖finiteWeilMomentWeights (finiteWeilArithmeticNodes r)‖ *
    finiteWeilCanonicalRawDistortion r k (finiteWeilArithmeticCenter r)
  have hB : 0 < B := mul_pos
    (finiteWeilMomentWeights_norm_pos _ (finiteWeilArithmeticNodes_injective r))
    (finiteWeilCanonicalRawDistortion_pos r k _)
  rw [finiteWeilCanonicalMixture_midpoint_raw]
  simp only [finiteWeilCanonicalMassProfile_eq_raw, Pi.smul_apply, smul_eq_mul,
    Pi.abs_apply, ← Finset.mul_sum]
  change _ = (B⁻¹ * |finiteWeilMomentWeights (finiteWeilClusterLogNodes r k) i|) /
    (B⁻¹ * finiteWeilAbsMass (finiteWeilMomentWeights (finiteWeilClusterLogNodes r k)))
  exact (mul_div_mul_left _ _ (inv_ne_zero hB.ne')).symm

theorem finiteWeilArithmeticAbsProfile_normalized (r : ℕ) (i : Fin (r + 2)) :
    finiteWeilArithmeticAbsProfile r i / finiteWeilArithmeticMass r =
      ((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1) := by
  have hC : 0 < ((r + 1).choose ((r + 1) / 2) : ℝ) := by
    rw [← finiteWeilBinomialDual_norm]
    exact finiteWeilBinomialDual_norm_pos r
  rw [finiteWeilArithmeticAbsProfile_eq_binomial, finiteWeilArithmeticMass_eq_binomial]
  field_simp

end RHTower
