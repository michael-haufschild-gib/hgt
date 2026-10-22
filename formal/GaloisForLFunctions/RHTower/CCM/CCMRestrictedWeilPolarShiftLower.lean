import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarFreeShift
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarSourceCancellation
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaMovableCompletedCovarianceCCMBridge

/-!
# The prescribed shift pays the physical pole scale

Finite-prime recurrence bounds the scalar-minus-prime quadratic by the norm
of the full bounded remainder. Applying this and the ordinary operator
bound to the even pole vector forces that norm to dominate `sinh a + a`.
Consequently the actual prescribed shift pays `exp a / 2` at every aperture.
This is the normalization needed for iterating the bounded remainder; it
does not bound the odd response or remove the shift from the Weil form.
-/

open Complex
open scoped InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The actual bounded remainder must retain at least half the even polar
eigenvalue, despite prime-polar cancellation on smooth source vectors. -/
theorem sinh_add_aperture_le_norm_ccmRestrictedWeilBoundedRemainder
    (a : SuzukiPositiveAperture) :
    Real.sinh a.1 + a.1 ≤ ‖ccmRestrictedWeilBoundedRemainder a‖ := by
  let p := ccmPolarApertureVector a (1 / 2)
  let m := ccmPolarApertureVector a (-1 / 2)
  let f := p + m
  have hpp : inner ℂ p p = ((2 * Real.sinh a.1 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) p]
    convert congrArg (fun r : ℝ => (r : ℂ))
      (norm_sq_ccmPolarApertureVector_half a) using 1
    simp only [Complex.ofReal_pow]
    rfl
  have hmm : inner ℂ m m = ((2 * Real.sinh a.1 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) m]
    convert congrArg (fun r : ℝ => (r : ℂ))
      (norm_sq_ccmPolarApertureVector_neg_half a) using 1
    simp only [Complex.ofReal_pow]
    rfl
  have hpm : inner ℂ p m = ((2 * a.1 : ℝ) : ℂ) := by
    simpa only [p, m, neg_neg, neg_div] using
      inner_ccmPolarApertureVector_opposite a (-1 / 2)
  have hmp : inner ℂ m p = ((2 * a.1 : ℝ) : ℂ) := by
    simpa only [p, m, neg_div] using
      inner_ccmPolarApertureVector_opposite a (1 / 2)
  have hf : ‖f‖ ^ 2 = 4 * (Real.sinh a.1 + a.1) := by
    rw [show f = p + m from rfl, norm_add_sq (𝕜 := ℂ), hpm]
    change ‖ccmPolarApertureVector a (1 / 2)‖ ^ 2 +
      2 * (((2 * a.1 : ℝ) : ℂ)).re +
      ‖ccmPolarApertureVector a (-1 / 2)‖ ^ 2 = _
    rw [norm_sq_ccmPolarApertureVector_half, norm_sq_ccmPolarApertureVector_neg_half]
    simp only [Complex.ofReal_re]
    ring
  have hp : (inner ℂ (ccmPolarOperator a f) f).re =
      8 * (Real.sinh a.1 + a.1) ^ 2 := by
    rw [inner_ccmPolarOperator]
    change ((starRingEnd ℂ) (inner ℂ m f) * inner ℂ p f +
      (starRingEnd ℂ) (inner ℂ p f) * inner ℂ m f).re = _
    rw [show f = p + m from rfl]
    simp only [inner_add_right, hpp, hmm, hpm, hmp, map_add,
      Complex.conj_ofReal, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.add_im, Complex.ofReal_im, zero_add, zero_mul, sub_zero]
    ring
  have hb : |(inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re| ≤
      ‖ccmRestrictedWeilBoundedRemainder a‖ * ‖f‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖ccmRestrictedWeilBoundedRemainder a f‖ * ‖f‖ :=
        norm_inner_le_norm (ccmRestrictedWeilBoundedRemainder a f) f
      _ ≤ (‖ccmRestrictedWeilBoundedRemainder a‖ * ‖f‖) * ‖f‖ :=
        mul_le_mul_of_nonneg_right
          ((ccmRestrictedWeilBoundedRemainder a).le_opNorm f) (norm_nonneg f)
      _ = _ := by ring
  have hfree := abs_le.mp (abs_ccmPolarFreeRemainderQuadratic_le a f)
  have hsplit := congrArg Complex.re (inner_ccmRestrictedWeilBoundedRemainder a f)
  simp only [Complex.add_re, Complex.sub_re] at hsplit hfree
  have hpolar : (inner ℂ (ccmPolarOperator a f) f).re ≤
      2 * ‖ccmRestrictedWeilBoundedRemainder a‖ * ‖f‖ ^ 2 := by
    linarith [(abs_le.mp hb).2, hfree.1]
  rw [hp, hf] at hpolar
  have hd : 0 < Real.sinh a.1 + a.1 :=
    add_pos (Real.sinh_pos_iff.mpr a.2) a.2
  nlinarith

/-- The physical remainder normalization pays the exponential source scale. -/
theorem exp_aperture_le_twice_ccmRestrictedWeilShift (a : SuzukiPositiveAperture) :
    Real.exp a.1 ≤ 2 * (‖ccmRestrictedWeilBoundedRemainder a‖ + 1) := by
  have h := sinh_add_aperture_le_norm_ccmRestrictedWeilBoundedRemainder a
  have he : Real.exp (-a.1) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show -a.1 ≤ 0 by linarith [a.2])
  rw [Real.sinh_eq] at h
  linarith [a.2]

/-- The same scale is paid by the literal interval shift used in Suzuki's
completed Riesz equation, without an additional choice of normalization. -/
theorem exp_aperture_le_twice_suzukiWeilIntervalShift (a : SuzukiPositiveAperture) :
    Real.exp a.1 ≤ 2 * boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) := by
  have hn : ‖ccmRestrictedWeilBoundedRemainder a‖ ≤
      ‖suzukiWeilIntervalBoundedRemainder a‖ := by
    apply (ccmRestrictedWeilBoundedRemainder a).opNorm_le_bound (norm_nonneg _)
    intro f
    let e := suzukiApertureL2Equiv a
    have hm : e.symm (ccmRestrictedWeilBoundedRemainder a f) =
        suzukiWeilIntervalBoundedRemainder a (e.symm f) := by
      change e.symm (ccmRestrictedWeilBoundedRemainder a f) =
        e.symm (ccmRestrictedWeilBoundedRemainder a (e (e.symm f)))
      rw [e.apply_symm_apply]
    calc
      _ = ‖e.symm (ccmRestrictedWeilBoundedRemainder a f)‖ := (e.symm.norm_map _).symm
      _ = ‖suzukiWeilIntervalBoundedRemainder a (e.symm f)‖ := congrArg norm hm
      _ ≤ ‖suzukiWeilIntervalBoundedRemainder a‖ * ‖e.symm f‖ :=
        (suzukiWeilIntervalBoundedRemainder a).le_opNorm _
      _ = _ := by rw [e.symm.norm_map]
  unfold boundedPerturbedFormShift
  linarith [exp_aperture_le_twice_ccmRestrictedWeilShift a]

end RHTower
