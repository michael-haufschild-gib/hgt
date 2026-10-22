import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilPropOneTwo
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilPropThreeOneCapstone
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# `S_t` through the Xi-zero series, for every real `t`

Suzuki, arXiv:2301.00421v3, defines `P_t` by eq. (1.6) only for `t >= 0` and then extends both
`P_t` (eq. 3.2) and `S_t` (eq. 1.5) to negative `t` by *evenness*, `S_t := S_{-t}`.

**That extension is inconsistent with the rest of the paper.**  Equations (3.6)–(3.8), Theorem 4.2
and Theorem 1.4 all use, for `t` of either sign,

`S_t(z) = sum over gamma of sqrt(pi m_gamma) ((e^{-i gamma t} - 1)/gamma) F_gamma^#(z)`,

i.e. the eq. (3.2) series *without* the absolute value.  The two disagree: with the even extension
one computes, for `phi = D psi`,

`Phat_{D psi}(z) = -(i/2)(1+Theta(z)) sum_gamma m_gamma c_gamma / (gamma (z - gamma))`,
`c_gamma = gamma * integral over (0,infty) of e^{i gamma t}(psi(t) - psi(-t)) dt`,

which vanishes identically for every **even** `psi`; Lemma 3.2 (that `‖.‖_0` is a norm) and eq.
(1.9) would then both be false.  Dropping the absolute value gives instead `c_gamma = gamma
psihat(gamma)`, which is what (3.8) asserts (up to one overall sign, immaterial for norms).

This file therefore builds `suzukiFrakSFull t z := i(1 + Theta^#(z))/2 * P_t(z)` for *every* real
`t`, records that it agrees with the eq. (1.5)/(1.6) object `suzukiFrakS` for `t > 0` (Proposition
3.1), and transports Proposition 1.2 to it.  The transport uses the divisor reflection
`gamma |-> -gamma` (`xiZeroCopyReflectEquiv`): `P_{-t}(z) = P_t(-z)`, together with
`|A/E^#|(-x) = |A/E^#|(x)` on the real axis, which holds because `E^#(x) = conj(E(x))` there.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower


namespace RHTower
noncomputable section

/-! ## The zero-series form of `𝔖_t`, valid for every real `t` -/

/-- **Suzuki eq. (1.5) through the zero series.**  `𝔖_t = i(1+Θ^♯)/2 · P_t`, with `P_t` the
multiplicity-exact Xi-zero series of eq. (3.2).  For `t > 0` this agrees with the definition
through eq. (1.6) by Proposition 3.1; unlike eq. (1.6) it makes sense for every real `t`. -/
def suzukiFrakSFull (t : ℝ) (z : ℂ) : ℂ :=
  I * (1 + suzukiThetaSharp z) / 2 * suzukiPtZeroSum t z

theorem suzukiFrakSFull_ofReal_eq (t : ℝ) {x : ℝ} (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    suzukiFrakSFull t ((x : ℝ) : ℂ)
      = I * (XiC ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ))
        * suzukiPtZeroSum t ((x : ℝ) : ℂ) := by
  have hE := xiHedenmalmDeBrangesESharp_ofReal_ne_zero hx
  have hadd := xiHedenmalmDeBrangesE_add_sharp (((x : ℝ) : ℂ))
  rw [suzukiFrakSFull, suzukiThetaSharp]
  congr 1
  field_simp
  linear_combination hadd

theorem suzukiFrakSFull_eq_suzukiFrakS {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ≠ 0)
    (hXi : XiC ((x : ℝ) : ℂ) ≠ 0) :
    suzukiFrakSFull t ((x : ℝ) : ℂ) = suzukiFrakS t ((x : ℝ) : ℂ) := by
  have hz0 : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx
  have hw : 0 < ((1 : ℂ) / 4 - I * ((x : ℝ) : ℂ) / 2).re := by rw [quarterLine_re]; norm_num
  have hsre : ((1 : ℂ) / 2 - I * ((x : ℝ) : ℂ)).re = 1 / 2 := by
    simp [Complex.sub_re, Complex.mul_re]
  have hs1 : (1 : ℂ) / 2 - I * ((x : ℝ) : ℂ) ≠ 1 := by
    intro h; rw [h] at hsre; norm_num at hsre
  rw [suzukiFrakSFull, suzukiFrakS,
    ← suzukiFrakP_eq_suzukiPtZeroSum hz0 hw hs1 hXi ht]

/-! ## Reflection in `t` -/

theorem suzukiPtZeroSum_neg (t : ℝ) (z : ℂ) :
    suzukiPtZeroSum (-t) z = suzukiPtZeroSum t (-z) := by
  rw [suzukiPtZeroSum, suzukiPtZeroSum,
    ← xiZeroCopyReflectEquiv.tsum_eq (fun q => suzukiPtZeroTerm t (-z) q)]
  refine tsum_congr fun q => ?_
  rw [suzukiPtZeroTerm, suzukiPtZeroTerm, xiSpectralPoint_reflect]
  have hexp : Complex.exp (-(I * xiSpectralPoint q * ((-t : ℝ) : ℂ)))
      = Complex.exp (-(I * -xiSpectralPoint q * (t : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  congr 1
  ring

theorem norm_XiC_div_ESharp_neg (x : ℝ) :
    ‖XiC (((-x : ℝ)) : ℂ) / xiHedenmalmDeBrangesESharp (((-x : ℝ)) : ℂ)‖
      = ‖XiC ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ)‖ := by
  have hcast : (((-x : ℝ)) : ℂ) = -((x : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, XiC_neg, xiHedenmalmDeBrangesESharp_neg_eq_E, norm_div, norm_div]
  congr 1
  have hEsharp : xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ)
      = (starRingEnd ℂ) (xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) := by
    rw [xiHedenmalmDeBrangesESharp, xiHedenmalmDeBrangesE, map_add, map_mul, Complex.conj_I]
    rw [Complex.conj_eq_iff_im.mpr (XiC_ofReal_im x),
      Complex.conj_eq_iff_im.mpr (deriv_XiC_ofReal_im x)]
    ring
  rw [hEsharp, Complex.norm_conj]

theorem norm_suzukiFrakSFull_ofReal_neg (t : ℝ) {x : ℝ} (hXi : XiC ((x : ℝ) : ℂ) ≠ 0) :
    ‖suzukiFrakSFull (-t) ((x : ℝ) : ℂ)‖ = ‖suzukiFrakSFull t (((-x : ℝ)) : ℂ)‖ := by
  have hcast : (((-x : ℝ)) : ℂ) = -((x : ℝ) : ℂ) := by push_cast; ring
  have hXi' : XiC (((-x : ℝ)) : ℂ) ≠ 0 := by rw [hcast, XiC_neg]; exact hXi
  rw [suzukiFrakSFull_ofReal_eq _ hXi, suzukiFrakSFull_ofReal_eq _ hXi',
    norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I,
    norm_XiC_div_ESharp_neg x, suzukiPtZeroSum_neg, hcast]

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

theorem suzukiPtZeroSum_zero (z : ℂ) : suzukiPtZeroSum 0 z = 0 := by
  have hzero : ∀ q : XiZeroCopy, suzukiPtZeroTerm 0 z q = 0 := by
    intro q
    rw [suzukiPtZeroTerm]
    norm_num
  rw [suzukiPtZeroSum, funext hzero, tsum_zero]

theorem decayW_neg (x : ℝ) : decayW (-x) = decayW x := by
  rw [decayW, decayW, abs_neg]

/-- **The master bound for every real `t`.** -/
theorem norm_suzukiFrakSFull_le (t : ℝ) {x : ℝ} (hx : x ≠ 0) (hXi : XiC ((x : ℝ) : ℂ) ≠ 0) :
    ‖suzukiFrakSFull t ((x : ℝ) : ℂ)‖ ≤ suzukiFrakSConst |t| * decayW x := by
  have hnn : (0 : ℝ) ≤ suzukiFrakSConst |t| * decayW x :=
    mul_nonneg (suzukiFrakSConst_nonneg (abs_nonneg t)) (decayW_pos x).le
  rcases lt_trichotomy t 0 with h | h | h
  · have hxn : (-x) ≠ 0 := neg_ne_zero.mpr hx
    have hcast : (((-x : ℝ)) : ℂ) = -((x : ℝ) : ℂ) := by push_cast; ring
    have hXin : XiC (((-x : ℝ)) : ℂ) ≠ 0 := by rw [hcast, XiC_neg]; exact hXi
    have hrefl : ‖suzukiFrakSFull t ((x : ℝ) : ℂ)‖
        = ‖suzukiFrakSFull (-t) (((-x : ℝ)) : ℂ)‖ := by
      have hkey := norm_suzukiFrakSFull_ofReal_neg (-t) hXi
      rw [neg_neg] at hkey
      exact hkey
    have hpos : 0 < -t := by linarith
    rw [hrefl, suzukiFrakSFull_eq_suzukiFrakS hpos hxn hXin, abs_of_neg h]
    have hb := norm_suzukiFrakS_le hpos.le hxn hXin
    rwa [decayW_neg] at hb
  · subst h
    rw [suzukiFrakSFull, suzukiPtZeroSum_zero, mul_zero, norm_zero]
    exact hnn
  · rw [suzukiFrakSFull_eq_suzukiFrakS h hx hXi, abs_of_pos h]
    exact norm_suzukiFrakS_le h.le hx hXi

/-! ## Measurability -/

theorem measurable_suzukiPtZeroSum_ofReal (t : ℝ) :
    Measurable (fun x : ℝ => suzukiPtZeroSum t ((x : ℝ) : ℂ)) := by
  refine Measurable.tsum fun q => ?_
  unfold suzukiPtZeroTerm
  fun_prop

theorem measurable_uncurry_suzukiPtZeroSum :
    Measurable (fun p : ℝ × ℝ => suzukiPtZeroSum p.2 ((p.1 : ℝ) : ℂ)) := by
  refine Measurable.tsum fun q => ?_
  unfold suzukiPtZeroTerm
  fun_prop

theorem measurable_XiC_ofReal : Measurable (fun x : ℝ => XiC ((x : ℝ) : ℂ)) :=
  continuous_XiC.measurable.comp Complex.measurable_ofReal

theorem measurable_suzukiThetaSharp_ofReal :
    Measurable (fun x : ℝ => suzukiThetaSharp ((x : ℝ) : ℂ)) := by
  have hX := measurable_XiC_ofReal
  have hD : Measurable (fun x : ℝ => deriv XiC ((x : ℝ) : ℂ)) :=
    (measurable_deriv XiC).comp Complex.measurable_ofReal
  unfold suzukiThetaSharp xiHedenmalmDeBrangesE xiHedenmalmDeBrangesESharp
  fun_prop

theorem measurable_suzukiFrakSFull_ofReal (t : ℝ) :
    Measurable (fun x : ℝ => suzukiFrakSFull t ((x : ℝ) : ℂ)) := by
  have hT := measurable_suzukiThetaSharp_ofReal
  have hP := measurable_suzukiPtZeroSum_ofReal t
  unfold suzukiFrakSFull
  fun_prop

theorem measurable_uncurry_suzukiFrakSFull :
    Measurable (fun p : ℝ × ℝ => suzukiFrakSFull p.2 ((p.1 : ℝ) : ℂ)) := by
  have hT : Measurable (fun p : ℝ × ℝ => suzukiThetaSharp ((p.1 : ℝ) : ℂ)) :=
    measurable_suzukiThetaSharp_ofReal.comp measurable_fst
  have hP := measurable_uncurry_suzukiPtZeroSum
  unfold suzukiFrakSFull
  fun_prop

/-- **Proposition 1.2 for the corrected object**, valid for every real `t`. -/
theorem memLp_suzukiFrakSFull (t : ℝ) :
    MemLp (fun x : ℝ => suzukiFrakSFull t ((x : ℝ) : ℂ)) 2 volume := by
  refine (memLp_decayW (suzukiFrakSConst |t|)).of_le
    (measurable_suzukiFrakSFull_ofReal t).aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero_and_XiC_ne_zero] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (suzukiFrakSConst_nonneg (abs_nonneg t)) (decayW_pos x).le)]
  exact norm_suzukiFrakSFull_le t hx.1 hx.2

end
end RHTower

