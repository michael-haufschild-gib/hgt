import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticConcentration
import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalDistortionModulus

/-! Rescaling at the central arithmetic weight separates shape from normalization. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilCanonicalRawDistortion_pos (r k : ℕ) (i : Fin (r + 2)) :
    0 < finiteWeilCanonicalRawDistortion r k i :=
  finiteWeilLogNodalDistortion_pos _ (finiteWeilClusterPositiveNodes_pos r k)
    (finiteWeilClusterPositiveNodes_injective r k) i

def finiteWeilCanonicalMassProfile (r k : ℕ) (i : Fin (r + 2)) : ℝ :=
  finiteWeilArithmeticAbsProfile r i *
    (finiteWeilCanonicalRawDistortion r k i /
      finiteWeilCanonicalRawDistortion r k (finiteWeilArithmeticCenter r))

theorem finiteWeilCanonicalMassProfile_pos (r k : ℕ) (i : Fin (r + 2)) :
    0 < finiteWeilCanonicalMassProfile r k i :=
  mul_pos (finiteWeilArithmeticAbsProfile_pos r i)
    (div_pos (finiteWeilCanonicalRawDistortion_pos r k i)
      (finiteWeilCanonicalRawDistortion_pos r k _))

theorem finiteWeilCanonicalMassProfile_center (r k : ℕ) :
    finiteWeilCanonicalMassProfile r k (finiteWeilArithmeticCenter r) = 1 := by
  rw [finiteWeilCanonicalMassProfile, finiteWeilArithmeticAbsProfile_center,
    div_self (finiteWeilCanonicalRawDistortion_pos r k _).ne', one_mul]

theorem finiteWeilCanonicalMassProfile_norm_ge_one (r k : ℕ) :
    1 ≤ ‖finiteWeilCanonicalMassProfile r k‖ := by
  have h := norm_le_pi_norm (finiteWeilCanonicalMassProfile r k) (finiteWeilArithmeticCenter r)
  simpa only [finiteWeilCanonicalMassProfile_center, norm_one] using h

theorem finiteWeilCanonicalMassProfile_eq_raw (r k : ℕ) :
    finiteWeilCanonicalMassProfile r k =
      (‖finiteWeilMomentWeights (finiteWeilArithmeticNodes r)‖ *
        finiteWeilCanonicalRawDistortion r k (finiteWeilArithmeticCenter r))⁻¹ •
          |finiteWeilMomentWeights (finiteWeilClusterLogNodes r k)| := by
  have hN := finiteWeilMomentWeights_norm_pos _ (finiteWeilArithmeticNodes_injective r)
  have ha := finiteWeilCanonicalRawDistortion_pos r k (finiteWeilArithmeticCenter r)
  funext i
  have hi := abs_pos.mpr (finiteWeilMomentWeights_ne_zero _
    (finiteWeilArithmeticNodes_injective r) i)
  simp only [finiteWeilCanonicalMassProfile, finiteWeilArithmeticAbsProfile,
    finiteWeilNormalizedMomentDual, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr hN)]
  rw [finiteWeilCanonicalRawDistortion_eq_weight_ratio r k i]
  change _ = _ * |finiteWeilMomentWeights (finiteWeilClusterLogNodes r k) i|
  field_simp

/-- The canonical mass is exactly the sum of the perturbed profile divided by its maximum. -/
theorem finiteWeilCanonicalCluster_mass_eq_profile (r k : ℕ) :
    finiteWeilAbsMass (finiteWeilCanonicalCluster r k) =
      (∑ i, finiteWeilCanonicalMassProfile r k i) / ‖finiteWeilCanonicalMassProfile r k‖ := by
  let B := ‖finiteWeilMomentWeights (finiteWeilArithmeticNodes r)‖ *
    finiteWeilCanonicalRawDistortion r k (finiteWeilArithmeticCenter r)
  have hB : 0 < B := mul_pos
    (finiteWeilMomentWeights_norm_pos _ (finiteWeilArithmeticNodes_injective r))
    (finiteWeilCanonicalRawDistortion_pos r k _)
  let W := finiteWeilMomentWeights (finiteWeilClusterLogNodes r k)
  have hW : 0 < ‖W‖ := finiteWeilMomentWeights_norm_pos _
    (finiteWeilClusterLogNodes_injective r k)
  have habsnorm : ‖|W|‖ = ‖W‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg W)).mpr
      intro i
      simpa only [Real.norm_eq_abs, Pi.abs_apply, abs_abs] using norm_le_pi_norm W i
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg |W|)).mpr
      intro i
      simpa only [Real.norm_eq_abs, Pi.abs_apply, abs_abs] using norm_le_pi_norm |W| i
  rw [finiteWeilCanonicalCluster, finiteWeilNormalizedMomentDual_abs_mass _
    (finiteWeilClusterLogNodes_injective r k)]
  simp only [finiteWeilCanonicalMassProfile_eq_raw, norm_smul, Real.norm_eq_abs,
    Pi.smul_apply, smul_eq_mul, Pi.abs_apply, ← Finset.mul_sum]
  change finiteWeilAbsMass W / ‖W‖ = (B⁻¹ * finiteWeilAbsMass W) / (|B⁻¹| * ‖|W|‖)
  rw [abs_of_pos (inv_pos.mpr hB), habsnorm]
  field_simp

theorem finiteWeilCanonicalMassProfile_error (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) (i : Fin (r + 2)) :
    |finiteWeilCanonicalMassProfile r k i - finiteWeilArithmeticAbsProfile r i| ≤
      (finiteWeilArithmeticAbsProfile r i *
        |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)|) /
          ((r + 1 : ℕ) : ℝ) := by
  have hm := finiteWeilCanonicalRawDistortion_index_modulus r k hwidth i
    (finiteWeilArithmeticCenter r)
  calc
    _ = finiteWeilArithmeticAbsProfile r i *
        |finiteWeilCanonicalRawDistortion r k i /
          finiteWeilCanonicalRawDistortion r k (finiteWeilArithmeticCenter r) - 1| := by
      rw [finiteWeilCanonicalMassProfile, ← mul_sub_one, abs_mul,
        abs_of_pos (finiteWeilArithmeticAbsProfile_pos r i)]
    _ ≤ _ := by
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left hm (finiteWeilArithmeticAbsProfile_pos r i).le

end RHTower
