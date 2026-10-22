import GaloisForLFunctions.RHTower.StrictHermiteBiehlerGivesRH
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAllAngleWitnesses
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedPublishedGrowthPriorArt
import GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH
import GaloisForLFunctions.RHTower.XiWeilCriterionConverse

/-!
# The exact Xi target for Suzuki's two-angle Donoghue limit

Suzuki's finite two-angle quotient is canonically normalized: its Herglotz transform sends `i`
to `i`, and its Livšic transform sends `i` to zero.  The unscaled logarithmic derivative
`-XiC'/XiC` does not carry that normalization.  Its unique positive real normalization under RH is

`m_Xi(z) = (-logDeriv XiC z) / Im(-logDeriv XiC i)`.

This file fixes that endpoint exactly.  Under RH, `m_Xi` maps the upper half-plane strictly into
itself, is anchored at `i`, and its Cayley transform is strictly Schur and vanishes at `i`.
Conversely, strict Hermite--Biehler separation for Hedenmalm's entire Xi pair implies RH, so the
strict Hermite--Biehler endpoint is equivalent to RH.

These are consumer and target-identification theorems.  They do not construct Suzuki's missing
source-selected finite-aperture limit.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Under RH the Xi logarithmic derivative is strictly anti-Herglotz in the upper half-plane. -/
theorem im_logDeriv_XiC_neg_of_rh
    (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 < z.im) :
    (logDeriv XiC z).im < 0 := by
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_upperHalf_of_rh hRH (by simpa [xiCenteredUpperHalfPlane] using hz)
  have hXiNeg : XiC (-z) ≠ 0 := by
    simpa only [XiC_even] using hXi
  have htrace :=
    xiRelativeResolventTrace_im_pos_of_halfPlaneBound
      (alpha := 0) (by norm_num) (xiZeroHalfPlaneBound_zero_of_rh hRH) (-z) (by
        simpa only [Complex.neg_im, neg_zero] using (neg_lt_zero.mpr hz))
  rw [← logDeriv_XiC_eq_relativeResolventTrace hXiNeg, logDeriv_XiC_neg] at htrace
  exact neg_pos.mp htrace

/-- RH supplies strict Hermite--Biehler separation for Hedenmalm's entire Xi pair. -/
theorem strict_hermiteBiehler_of_rh
    (hRH : RiemannHypothesis) :
    GaloisForLFunctions.RHTower.SuzukiHermiteBiehler xiHedenmalmDeBrangesE := by
  intro z hz
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_upperHalf_of_rh hRH (by simpa [xiCenteredUpperHalfPlane] using hz)
  have him := im_logDeriv_XiC_neg_of_rh hRH hz
  have hpos : 0 < (-logDeriv XiC z).im := by
    simpa only [Complex.neg_im] using neg_pos.mpr him
  have hnorm :=
    GaloisForLFunctions.RHTower.norm_sub_I_lt_norm_add_I hpos
  have hnorm' :
      ‖logDeriv XiC z + I‖ < ‖logDeriv XiC z - I‖ := by
    rw [show -logDeriv XiC z - I = -(logDeriv XiC z + I) by ring,
      show -logDeriv XiC z + I = -(logDeriv XiC z - I) by ring,
      norm_neg, norm_neg] at hnorm
    exact hnorm
  have hsharp :
      xiHedenmalmDeBrangesESharp z =
        XiC z * (-I * (logDeriv XiC z + I)) := by
    rw [xiHedenmalmDeBrangesESharp, logDeriv_apply]
    field_simp [hXi]
    linear_combination (XiC z) * Complex.I_mul_I
  have hE :
      xiHedenmalmDeBrangesE z =
        XiC z * (I * (logDeriv XiC z - I)) := by
    rw [xiHedenmalmDeBrangesE, logDeriv_apply]
    field_simp [hXi]
    linear_combination (XiC z) * Complex.I_mul_I
  rw [suzukiEntireSharp_xiHedenmalmDeBrangesE,
    hsharp, hE, norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, norm_I, one_mul]
  simpa only [one_mul] using
    (mul_lt_mul_of_pos_left hnorm' (norm_pos_iff.mpr hXi))

/-- Positive real scale that enforces Suzuki's Donoghue anchor `m(i)=i`. -/
def xiHedenmalmDonoghueScale : ℝ :=
  (-logDeriv XiC I).im

/-- Exact normalized Xi Donoghue target for any two-angle Suzuki limit. -/
def xiHedenmalmDonoghueTarget (z : ℂ) : ℂ :=
  (-logDeriv XiC z) / (xiHedenmalmDonoghueScale : ℂ)

/-- Exact normalized Xi Livšic target, obtained by the upper-half-plane Cayley transform. -/
def xiHedenmalmLivsicTarget (z : ℂ) : ℂ :=
  (xiHedenmalmDonoghueTarget z - I) /
    (xiHedenmalmDonoghueTarget z + I)

/-- The Donoghue normalization scale is strictly positive under RH. -/
theorem xiHedenmalmDonoghueScale_pos_of_rh
    (hRH : RiemannHypothesis) :
    0 < xiHedenmalmDonoghueScale := by
  exact neg_pos.mpr (im_logDeriv_XiC_neg_of_rh hRH (by norm_num))

/-- Schwarz reality and oddness make the logarithmic derivative purely imaginary at `i`. -/
theorem re_logDeriv_XiC_I_eq_zero (hXi : XiC I ≠ 0) :
    (logDeriv XiC I).re = 0 := by
  have hconj := logDeriv_XiC_conj (z := I) hXi
  have hodd := logDeriv_XiC_neg I
  rw [show (starRingEnd ℂ) I = -I by simp, hodd] at hconj
  have hre := congrArg Complex.re hconj
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

/-- The normalized Xi Donoghue target has Suzuki's exact anchor `m(i)=i`. -/
theorem xiHedenmalmDonoghueTarget_I_of_rh
    (hRH : RiemannHypothesis) :
    xiHedenmalmDonoghueTarget I = I := by
  have hXi : XiC I ≠ 0 :=
    XiC_ne_zero_upperHalf_of_rh hRH (by
      rw [xiCenteredUpperHalfPlane, Set.mem_setOf_eq]
      norm_num)
  have hre := re_logDeriv_XiC_I_eq_zero hXi
  have hc := xiHedenmalmDonoghueScale_pos_of_rh hRH
  have hraw :
      -logDeriv XiC I = (xiHedenmalmDonoghueScale : ℂ) * I := by
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero]
      linarith
    · simp [xiHedenmalmDonoghueScale]
  rw [xiHedenmalmDonoghueTarget, hraw]
  field_simp [hc.ne']

/-- Under RH the exact Donoghue target is strictly Herglotz. -/
theorem im_xiHedenmalmDonoghueTarget_pos_of_rh
    (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 < z.im) :
    0 < (xiHedenmalmDonoghueTarget z).im := by
  have hc := xiHedenmalmDonoghueScale_pos_of_rh hRH
  have him := im_logDeriv_XiC_neg_of_rh hRH hz
  rw [xiHedenmalmDonoghueTarget, Complex.div_ofReal_im]
  exact div_pos (neg_pos.mpr him) hc

/-- Under RH the exact Livšic target lies strictly inside the unit disk. -/
theorem norm_xiHedenmalmLivsicTarget_lt_one_of_rh
    (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 < z.im) :
    ‖xiHedenmalmLivsicTarget z‖ < 1 := by
  exact GaloisForLFunctions.cayley_upperHalfPlane_to_disk
    (xiHedenmalmDonoghueTarget z)
    (im_xiHedenmalmDonoghueTarget_pos_of_rh hRH hz)

/-- The exact Livšic target has Suzuki's finite-aperture anchor `Theta(i)=0`. -/
theorem xiHedenmalmLivsicTarget_I_of_rh
    (hRH : RiemannHypothesis) :
    xiHedenmalmLivsicTarget I = 0 := by
  rw [xiHedenmalmLivsicTarget, xiHedenmalmDonoghueTarget_I_of_rh hRH]
  norm_num

/-- Strict Hermite--Biehler separation for Hedenmalm's Xi pair is exactly RH. -/
theorem riemannHypothesis_iff_strict_hermiteBiehler :
    RiemannHypothesis ↔
      GaloisForLFunctions.RHTower.SuzukiHermiteBiehler xiHedenmalmDeBrangesE := by
  exact ⟨strict_hermiteBiehler_of_rh, riemannHypothesis_of_strict_hermiteBiehler⟩

end

end RHTower
