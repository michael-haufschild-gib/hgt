import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilZeroSeries
import GaloisForLFunctions.RHTower.XiZeroSumDivergence
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewWeilIdentity

/-!
# The zero-time velocity boundary of Suzuki's Xi-zero series

Suzuki's divisor series `P_t(z)` is absolutely summable because every summand has two divisor
denominators.  Its literal complex-time derivative at `t = 0` loses one of them.  This module
proves two complementary facts:

* that unpaired velocity is not absolutely summable at any base point off the Xi divisor; and
* that reflection pairs have the exact, absolutely summable reciprocal-square form.

Thus divisor reflection identifies the only canonical zero-time summable datum.  This is a
convergence boundary, not a replacement for the literal prime--polar source or its triangular
window.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Complex-time velocity of one literal `P_t` divisor summand at `t = 0`. -/
def suzukiPtZeroVelocityTerm (z : ℂ) (q : XiZeroCopy) : ℂ :=
  -Complex.I / (z - xiSpectralPoint q)

/-- Complex-time extension of one literal `P_t` divisor summand. -/
def suzukiPtZeroTermComplex (t z : ℂ) (q : XiZeroCopy) : ℂ :=
  (Complex.exp (-(Complex.I * xiSpectralPoint q * t)) - 1) /
    (xiSpectralPoint q * (z - xiSpectralPoint q))

/-- The exact zero-time derivative of one `P_t` divisor summand. -/
theorem hasDerivAt_suzukiPtZeroTermComplex_zero (z : ℂ) (q : XiZeroCopy) :
    HasDerivAt (fun t : ℂ => suzukiPtZeroTermComplex t z q)
      (suzukiPtZeroVelocityTerm z q) 0 := by
  have hlinear : HasDerivAt
      (fun t : ℂ => -(Complex.I * t * xiSpectralPoint q))
      (-(Complex.I * xiSpectralPoint q)) 0 := by
    have hraw : HasDerivAt
        (fun t : ℂ => Complex.I * t * xiSpectralPoint q)
        (Complex.I * xiSpectralPoint q) 0 := by
      simpa using (((hasDerivAt_id (0 : ℂ)).const_mul Complex.I).mul_const
        (xiSpectralPoint q))
    exact hraw.neg
  have hcomp : HasDerivAt
      (fun t : ℂ => Complex.exp (-(Complex.I * t * xiSpectralPoint q)))
      (Complex.exp (-(Complex.I * (0 : ℂ) * xiSpectralPoint q)) *
        (-(Complex.I * xiSpectralPoint q))) 0 := by
    simpa using hlinear.cexp
  have hfunction : (fun t : ℂ => suzukiPtZeroTermComplex t z q) =
      fun t : ℂ => (Complex.exp (-(Complex.I * t * xiSpectralPoint q)) - 1) /
        (xiSpectralPoint q * (z - xiSpectralPoint q)) := by
    funext t
    unfold suzukiPtZeroTermComplex
    congr 3
    all_goals ring
  have hgamma : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hderivative :
      Complex.exp (-(Complex.I * (0 : ℂ) * xiSpectralPoint q)) *
          (-(Complex.I * xiSpectralPoint q)) /
        (xiSpectralPoint q * (z - xiSpectralPoint q)) =
      suzukiPtZeroVelocityTerm z q := by
    unfold suzukiPtZeroVelocityTerm
    simp
    field_simp [hgamma]
  rw [hfunction]
  simpa only [hderivative] using
    (hcomp.sub_const 1).div_const (xiSpectralPoint q * (z - xiSpectralPoint q))

/-- No off-divisor base point makes the literal `P_t` velocity absolutely summable. -/
theorem not_summable_norm_suzukiPtZeroVelocityTerm
    (z : ℂ) (hz : XiC z ≠ 0) :
    ¬ Summable (fun q : XiZeroCopy => ‖suzukiPtZeroVelocityTerm z q‖) := by
  intro hnorm
  have hvelocity : Summable (suzukiPtZeroVelocityTerm z) :=
    summable_norm_iff.mp hnorm
  have hshift : Summable (fun q : XiZeroCopy => (xiSpectralPoint q - z)⁻¹) := by
    refine (hvelocity.mul_left (-Complex.I)).congr fun q => ?_
    unfold suzukiPtZeroVelocityTerm
    rw [div_eq_mul_inv,
      show z - xiSpectralPoint q = -(xiSpectralPoint q - z) by ring,
      inv_neg]
    calc
      -Complex.I * (-Complex.I * -(xiSpectralPoint q - z)⁻¹) =
          (Complex.I * Complex.I) * -(xiSpectralPoint q - z)⁻¹ := by ring
      _ = (xiSpectralPoint q - z)⁻¹ := by rw [Complex.I_mul_I]; ring
  have hrelative : Summable (xiRelativeResolventTerm z) :=
    summable_xiRelativeResolventTerm hz
  have hinv : Summable (fun q : XiZeroCopy => (xiSpectralPoint q)⁻¹) := by
    refine (hrelative.add hshift).congr fun q => ?_
    rw [xiRelativeResolventTerm]
    ring
  have hnormInv : Summable (fun q : XiZeroCopy => ‖(xiSpectralPoint q)⁻¹‖) :=
    summable_norm_iff.mpr hinv
  apply not_summable_inv_norm_xiSpectralPoint
  refine hnormInv.congr fun q => ?_
  simp only [norm_inv, one_div]

/-- Reflection-paired zero-time velocity, retaining the divisor's multiplicity and involution. -/
def suzukiPtZeroReflectionVelocity (z : ℂ) (q : XiZeroCopy) : ℂ :=
  suzukiPtZeroVelocityTerm z q +
    suzukiPtZeroVelocityTerm z (xiZeroCopyReflectEquiv q)

/-- Reflection restores the missing divisor denominator at zero time. -/
theorem suzukiPtZeroReflectionVelocity_eq (z : ℂ) (q : XiZeroCopy)
    (hz : XiC z ≠ 0) :
    suzukiPtZeroReflectionVelocity z q =
      2 * Complex.I * z * xiReciprocalSquareResolventTerm z q := by
  have hgamma : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hzp : z ≠ xiSpectralPoint q := by
    intro h
    exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, h.symm⟩)
  have hzn : z ≠ -xiSpectralPoint q := by
    intro h
    exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr
      ⟨xiZeroCopyReflectEquiv q, by rw [xiSpectralPoint_reflect, ← h]⟩)
  have hp : xiSpectralPoint q - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzp)
  have hn : -xiSpectralPoint q - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzn)
  have hpair :
      suzukiPtZeroVelocityTerm z q +
          suzukiPtZeroVelocityTerm z (xiZeroCopyReflectEquiv q) =
        -Complex.I * (xiRelativeResolventTerm z q +
          xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q)) := by
    unfold suzukiPtZeroVelocityTerm xiRelativeResolventTerm
    rw [xiSpectralPoint_reflect]
    field_simp [hgamma, hp, hn]
    ring
  unfold suzukiPtZeroReflectionVelocity
  rw [hpair, pair_xiRelativeResolventTerm z q hzp hzn]
  ring

/-- The reflection-paired velocity is absolutely summable at every off-divisor base point. -/
theorem summable_suzukiPtZeroReflectionVelocity {z : ℂ} (hz : XiC z ≠ 0) :
    Summable (suzukiPtZeroReflectionVelocity z) := by
  refine (summable_xiReciprocalSquareResolventTerm hz).mul_left (2 * Complex.I * z) |>.congr
    fun q => ?_
  exact (suzukiPtZeroReflectionVelocity_eq z q hz).symm

/-- At the regular base point `z = 0`, Suzuki's literal `P_t` is the complete Xi screw.
The identification uses only the divisor reflection, before summation. -/
theorem suzukiPtZeroSum_zeroBase_eq_xiScrewDivisor (t : ℝ) :
    suzukiPtZeroSum t 0 = xiScrewDivisor t := by
  rw [suzukiPtZeroSum, xiScrewDivisor_eq_tsum_exponential]
  calc
    (∑' q : XiZeroCopy, suzukiPtZeroTerm t 0 q) =
        ∑' q : XiZeroCopy, xiScrewExponentialTerm t (xiZeroCopyReflectEquiv q) := by
      apply tsum_congr
      intro q
      have hgamma : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
      rw [suzukiPtZeroTerm, xiScrewExponentialTerm, xiSpectralPoint_reflect]
      field_simp [hgamma]
      ring
    _ = ∑' q : XiZeroCopy, xiScrewExponentialTerm t q :=
      xiZeroCopyReflectEquiv.tsum_eq _

end

end RHTower
