import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarFreeShift
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaCoalescingCovarianceTangent
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaMovableCompletedCovarianceCCMBridge

/-!
# Uniform control of the actual even source at the matched pole anchor

At anchor `1/2`, the even source is the cosh vector of the literal polar
operator. The actual shift remains coercive after deleting that operator.
Reflection then identifies its polar energy with twice the square of its
Riesz source energy. The resulting estimate is uniform in aperture.

This does not estimate the odd source or the complete cofinal Wronskian.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The actual completed form response to the matched even pole source. -/
def suzukiMatchedEvenFormResponse (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a :=
  suzukiTaToFormCLM a (suzukiTaRawCoalescingEven a (1 / 2))

private theorem physical_response (a : SuzukiPositiveAperture) :
    ccmArchimedeanFormToAperture a (suzukiMatchedEvenFormResponse a) =
      suzukiApertureL2Equiv a
        (suzukiTaPhysicalEmbedding a (suzukiTaRawCoalescingEven a (1 / 2))) := by
  change _ = (suzukiApertureL2Equiv a)
    ((suzukiApertureL2Equiv a).symm
      (ccmArchimedeanFormToAperture a (suzukiMatchedEvenFormResponse a)))
  rw [(suzukiApertureL2Equiv a).apply_symm_apply]

private theorem even_response_reflection (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiWeilIntervalReflection a
      (suzukiTaPhysicalEmbedding a (suzukiTaRawCoalescingEven a c)) =
        suzukiTaPhysicalEmbedding a (suzukiTaRawCoalescingEven a c) := by
  rw [suzukiTaRawCoalescingEven, map_smul, map_add, map_smul, map_add,
    ← suzukiTaPhysicalEmbedding_rawDeficiency_reflection,
    ← suzukiTaPhysicalEmbedding_rawDeficiency_reflection]
  rw [neg_neg, add_comm]

/-- Both pole charges of the selected even response equal its actual source energy. -/
theorem suzukiMatchedEvenFormResponse_pole_charges (a : SuzukiPositiveAperture) :
    let f := ccmArchimedeanFormToAperture a (suzukiMatchedEvenFormResponse a)
    inner ℂ (ccmPolarApertureVector a (1 / 2)) f =
        (suzukiTaCoalescingEvenEnergy a (1 / 2) : ℂ) ∧
      inner ℂ (ccmPolarApertureVector a (-1 / 2)) f =
        (suzukiTaCoalescingEvenEnergy a (1 / 2) : ℂ) := by
  let w := suzukiTaRawCoalescingEven a (1 / 2)
  let v := suzukiTaPhysicalEmbedding a w
  have htransport (s : ℝ) :
      inner ℂ (ccmPolarApertureVector a s)
          (ccmArchimedeanFormToAperture a (suzukiMatchedEvenFormResponse a)) =
        inner ℂ (suzukiTaExponentialL2 a s) v := by
    have hp : suzukiApertureL2Equiv a (suzukiTaExponentialL2 a s) =
        ccmPolarApertureVector a s := by
      apply Subtype.ext
      exact suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector a s
    rw [physical_response, ← hp]
    exact (suzukiApertureL2Equiv a).inner_map_map _ _
  have hsame : inner ℂ (suzukiTaExponentialL2 a (-1 / 2)) v =
      inner ℂ (suzukiTaExponentialL2 a (1 / 2)) v := by
    have h := (suzukiWeilIntervalReflection a).inner_map_map
      (suzukiTaExponentialL2 a (1 / 2)) v
    rw [suzukiWeilIntervalReflection_exponential,
      even_response_reflection a (1 / 2)] at h
    simpa only [neg_div, neg_one_mul] using h
  have hsum : inner ℂ (suzukiTaExponentialL2 a (1 / 2)) v +
      inner ℂ (suzukiTaExponentialL2 a (-1 / 2)) v =
        2 * (suzukiTaCoalescingEvenEnergy a (1 / 2) : ℂ) := by
    have he : inner ℂ ((suzukiApertureCoordinate a.2.le).coshVecC (1 / 2)) v =
        (suzukiTaCoalescingEvenEnergy a (1 / 2) : ℂ) := by
      dsimp only [v, w]
      rw [← suzukiTaRawCoalescingEven_inner, suzukiTaCoalescingEvenEnergy_eq_norm_sq,
        inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [suzukiTaExponentialL2_eq_cosh_add_sinh,
      show (-1 / 2 : ℝ) = -(1 / 2) by ring,
      suzukiTaExponentialL2_neg_eq_cosh_sub_sinh,
      inner_add_left, inner_sub_left, he]
    ring
  dsimp only
  rw [htransport, htransport]
  constructor
  · linear_combination (hsum - hsame) / 2
  · linear_combination (hsum + hsame) / 2

/-- The complete polar energy of the selected source, with both charges retained. -/
theorem suzukiMatchedEvenFormResponse_polar_energy (a : SuzukiPositiveAperture) :
    let f := ccmArchimedeanFormToAperture a (suzukiMatchedEvenFormResponse a)
    (inner ℂ (ccmPolarOperator a f) f).re =
      2 * (suzukiTaCoalescingEvenEnergy a (1 / 2)) ^ 2 := by
  obtain ⟨hp, hm⟩ := suzukiMatchedEvenFormResponse_pole_charges a
  dsimp only at hp hm ⊢
  rw [inner_ccmPolarOperator, hp, hm, Complex.conj_ofReal]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

private theorem remainder_norm_le_interval (a : SuzukiPositiveAperture) :
    ‖ccmRestrictedWeilBoundedRemainder a‖ ≤
      ‖suzukiWeilIntervalBoundedRemainder a‖ := by
  apply (ccmRestrictedWeilBoundedRemainder a).opNorm_le_bound (norm_nonneg _)
  intro f
  let e := suzukiApertureL2Equiv a
  have hmap : e.symm (ccmRestrictedWeilBoundedRemainder a f) =
      suzukiWeilIntervalBoundedRemainder a (e.symm f) := by
    change e.symm (ccmRestrictedWeilBoundedRemainder a f) =
      e.symm (ccmRestrictedWeilBoundedRemainder a (e (e.symm f)))
    rw [e.apply_symm_apply]
  calc
    _ = ‖e.symm (ccmRestrictedWeilBoundedRemainder a f)‖ := (e.symm.norm_map _).symm
    _ = ‖suzukiWeilIntervalBoundedRemainder a (e.symm f)‖ := congrArg norm hmap
    _ ≤ ‖suzukiWeilIntervalBoundedRemainder a‖ * ‖e.symm f‖ :=
      (suzukiWeilIntervalBoundedRemainder a).le_opNorm _
    _ = _ := by rw [e.symm.norm_map]

/-- The actual shifted energy pays both norms even after its polar term is removed. -/
theorem suzukiTa_energy_sub_polar_ge (a : SuzukiPositiveAperture)
    (w : SuzukiTaHilbert a) :
    let u := suzukiTaToFormCLM a w
    let f := ccmArchimedeanFormToAperture a u
    ‖u‖ ^ 2 + ‖f‖ ^ 2 ≤ ‖w‖ ^ 2 - (inner ℂ (ccmPolarOperator a f) f).re := by
  let u := suzukiTaToFormCLM a w
  let f := ccmArchimedeanFormToAperture a u
  have hb := (abs_le.mp (abs_ccmPolarFreeRemainderQuadratic_le a f)).1
  have hn := mul_le_mul_of_nonneg_right (remainder_norm_le_interval a) (sq_nonneg ‖f‖)
  have hphys : ‖suzukiTaPhysicalEmbedding a w‖ = ‖f‖ := by
    exact (suzukiApertureL2Equiv a).symm.norm_map f
  have he := congrArg Complex.re (inner_suzukiTa_eq a w w)
  rw [suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm] at he
  change (inner ℂ w w).re =
    (inner ℂ u u + inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f +
      (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
        inner ℂ (suzukiTaPhysicalEmbedding a w) (suzukiTaPhysicalEmbedding a w)).re at he
  rw [inner_ccmRestrictedWeilBoundedRemainder] at he
  have hw : (inner ℂ w w).re = ‖w‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) w).symm
  have hu : (inner ℂ u u).re = ‖u‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  have hv : (inner ℂ (suzukiTaPhysicalEmbedding a w)
      (suzukiTaPhysicalEmbedding a w)).re = ‖suzukiTaPhysicalEmbedding a w‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (suzukiTaPhysicalEmbedding a w)).symm
  simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul,
    hw, hu, hv, hphys, boundedPerturbedFormShift] at he
  dsimp only at hb ⊢
  rw [Complex.sub_re] at hb
  change ‖u‖ ^ 2 + ‖f‖ ^ 2 ≤ ‖w‖ ^ 2 - (inner ℂ (ccmPolarOperator a f) f).re
  linarith

/-- Uniform bound for the literal even covariance energy at the matched pole anchor. -/
theorem suzukiTaCoalescingEvenEnergy_half_le (a : SuzukiPositiveAperture) :
    suzukiTaCoalescingEvenEnergy a (1 / 2) ≤ 1 / 2 := by
  have h := suzukiTa_energy_sub_polar_ge a (suzukiTaRawCoalescingEven a (1 / 2))
  have hp := suzukiMatchedEvenFormResponse_polar_energy a
  dsimp only [suzukiMatchedEvenFormResponse] at hp
  dsimp only at h
  rw [hp, ← suzukiTaCoalescingEvenEnergy_eq_norm_sq] at h
  nlinarith [sq_nonneg ‖suzukiTaToFormCLM a (suzukiTaRawCoalescingEven a (1 / 2))‖,
    sq_nonneg ‖ccmArchimedeanFormToAperture a
      (suzukiTaToFormCLM a (suzukiTaRawCoalescingEven a (1 / 2)))‖]

/-- Uniform control of the complete form norm and physical mass of the actual even response. -/
theorem suzukiMatchedEvenFormResponse_uniform_bound (a : SuzukiPositiveAperture) :
    ‖suzukiMatchedEvenFormResponse a‖ ^ 2 +
      ‖ccmArchimedeanFormToAperture a (suzukiMatchedEvenFormResponse a)‖ ^ 2 ≤ 1 / 8 := by
  have h := suzukiTa_energy_sub_polar_ge a (suzukiTaRawCoalescingEven a (1 / 2))
  change ‖suzukiMatchedEvenFormResponse a‖ ^ 2 +
      ‖ccmArchimedeanFormToAperture a (suzukiMatchedEvenFormResponse a)‖ ^ 2 ≤
    ‖suzukiTaRawCoalescingEven a (1 / 2)‖ ^ 2 - _ at h
  have hp := suzukiMatchedEvenFormResponse_polar_energy a
  dsimp only [suzukiMatchedEvenFormResponse] at hp
  rw [hp, ← suzukiTaCoalescingEvenEnergy_eq_norm_sq] at h
  nlinarith [sq_nonneg (suzukiTaCoalescingEvenEnergy a (1 / 2) - 1 / 4)]

end RHTower
