import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFullDensityWronskianNoGo
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityDeBranges

/-!
# Projective collision geometry of the completed theta density

The completed-density ratio `E# / E` detects a noncentral Xi zero by the single projective value
`-1`.  This file identifies the actual derivative numerator of that ratio and proves its exact
boundary entry law at every positive simple real Xi zero.

The resulting projective Wronskian is not the full-density reflected connection previously used
for the transfer quotient.  At a Xi zero their carriers are respectively `E` and `F`, and their
normalized difference is the nonzero completion seam `-z^2 XiC'` at every noncentral simple zero.
Thus any negative-ray argument must control the projective Wronskian defined here.

All results are unconditional.  No zero-location or simplicity assertion is assumed globally.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Complex derivative selected by the damped completed-density channel. -/
def thetaCuspTailSecondDensityDeBrangesEDerivative (z : ℂ) : ℂ :=
  2 * z * thetaCuspTailSecondDensityPhaseValue z +
    (z ^ 2 + 1 / 4) * thetaCuspTailSecondDensityPhaseDerivative z

/-- Complex derivative selected by the reflected growing channel. -/
def thetaCuspTailSecondDensityDeBrangesESharpDerivative (z : ℂ) : ℂ :=
  2 * z * thetaCuspTailSecondDensityPhaseValue (-z) -
    (z ^ 2 + 1 / 4) * thetaCuspTailSecondDensityPhaseDerivative (-z)

/-- Meromorphic projective ratio of the two completed-density channels. -/
def thetaCuspTailSecondDensityDeBrangesProjectiveRatio (z : ℂ) : ℂ :=
  thetaCuspTailSecondDensityDeBrangesESharp z /
    thetaCuspTailSecondDensityDeBrangesE z

/-- Division-free derivative numerator of the completed-density projective ratio. -/
def thetaCuspTailSecondDensityDeBrangesProjectiveWronskian (z : ℂ) : ℂ :=
  thetaCuspTailSecondDensityDeBrangesESharpDerivative z *
      thetaCuspTailSecondDensityDeBrangesE z -
    thetaCuspTailSecondDensityDeBrangesESharp z *
      thetaCuspTailSecondDensityDeBrangesEDerivative z

/-- Division-free tangent vector for projective level curves.  Multiplying by `E^2` removes the
quotient denominator, while conjugating the Wronskian orients increasing real ratio. -/
def thetaCuspTailSecondDensityDeBrangesProjectiveFlow (z : ℂ) : ℂ :=
  thetaCuspTailSecondDensityDeBrangesE z ^ 2 *
    starRingEnd ℂ
      (thetaCuspTailSecondDensityDeBrangesProjectiveWronskian z)

theorem hasDerivAt_thetaCuspTailSecondDensityDeBrangesE
    {z : ℂ} (hz : -1 < z.im) :
    HasDerivAt thetaCuspTailSecondDensityDeBrangesE
      (thetaCuspTailSecondDensityDeBrangesEDerivative z) z := by
  have hq : HasDerivAt (fun w : ℂ => w ^ 2 + 1 / 4) (2 * z) z := by
    simpa [mul_comm] using ((hasDerivAt_id z).pow 2).add_const (1 / 4)
  have hF := hasDerivAt_thetaCuspTailSecondDensityPhaseValue (z₀ := z) hz
  unfold thetaCuspTailSecondDensityDeBrangesE
    thetaCuspTailSecondDensityDeBrangesEDerivative
  exact (hq.mul hF).sub_const (1 / 4)

theorem hasDerivAt_thetaCuspTailSecondDensityDeBrangesESharp
    {z : ℂ} (hz : z.im < 1) :
    HasDerivAt thetaCuspTailSecondDensityDeBrangesESharp
      (thetaCuspTailSecondDensityDeBrangesESharpDerivative z) z := by
  have hq : HasDerivAt (fun w : ℂ => w ^ 2 + 1 / 4) (2 * z) z := by
    simpa [mul_comm] using ((hasDerivAt_id z).pow 2).add_const (1 / 4)
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
  have hF0 := hasDerivAt_thetaCuspTailSecondDensityPhaseValue
    (z₀ := -z) (by simpa using neg_lt_neg hz)
  have hF := hF0.comp z hneg
  unfold thetaCuspTailSecondDensityDeBrangesESharp
    thetaCuspTailSecondDensityDeBrangesESharpDerivative
  exact ((hq.mul hF).sub_const (1 / 4)).congr_deriv (by
    simp only [Function.comp_apply]
    ring)

/-- Differentiating the completed reflection identity preserves its exact completion seam. -/
theorem thetaCuspTailSecondDensityDeBrangesDerivative_add_sharp
    {z : ℂ} (hz : |z.im| < 1) :
    thetaCuspTailSecondDensityDeBrangesEDerivative z +
        thetaCuspTailSecondDensityDeBrangesESharpDerivative z =
      8 * z * XiC z + 4 * z ^ 2 * deriv XiC z := by
  convert thetaCuspTailSecondDensityPhaseValue_twoSided_derivative_crossed hz using 1
  simp only [thetaCuspTailSecondDensityDeBrangesEDerivative,
    thetaCuspTailSecondDensityDeBrangesESharpDerivative]
  ring

/-- Exact reflected connection for the derivative of `E# / E`.  Unlike the full-density
connection, this identity retains the completed channel `E` as its carrier. -/
theorem thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_eq_connection
    {z : ℂ} (hz : |z.im| < 1) :
    thetaCuspTailSecondDensityDeBrangesProjectiveWronskian z =
      8 * z * XiC z * thetaCuspTailSecondDensityDeBrangesE z +
        4 * z ^ 2 *
          (deriv XiC z * thetaCuspTailSecondDensityDeBrangesE z -
            XiC z * thetaCuspTailSecondDensityDeBrangesEDerivative z) := by
  have hv := thetaCuspTailSecondDensityDeBrangesE_add_sharp hz
  have hd := thetaCuspTailSecondDensityDeBrangesDerivative_add_sharp hz
  unfold thetaCuspTailSecondDensityDeBrangesProjectiveWronskian
  linear_combination
    thetaCuspTailSecondDensityDeBrangesE z * hd -
      thetaCuspTailSecondDensityDeBrangesEDerivative z * hv

/-- At an antipodal collision, projective transversality is carried by `XiC' * E`. -/
theorem thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_eq_at_XiC_zero
    {z : ℂ} (hzstrip : |z.im| < 1) (hz : XiC z = 0) :
    thetaCuspTailSecondDensityDeBrangesProjectiveWronskian z =
      4 * z ^ 2 * deriv XiC z *
        thetaCuspTailSecondDensityDeBrangesE z := by
  rw [thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_eq_connection hzstrip,
    hz]
  ring

/-- Quotient rule for the completed-density projective ratio on its regular chart. -/
theorem hasDerivAt_thetaCuspTailSecondDensityDeBrangesProjectiveRatio
    {z : ℂ} (hzstrip : |z.im| < 1)
    (hE : thetaCuspTailSecondDensityDeBrangesE z ≠ 0) :
    HasDerivAt thetaCuspTailSecondDensityDeBrangesProjectiveRatio
      (thetaCuspTailSecondDensityDeBrangesProjectiveWronskian z /
        thetaCuspTailSecondDensityDeBrangesE z ^ 2) z := by
  have hS := hasDerivAt_thetaCuspTailSecondDensityDeBrangesESharp
    (z := z) (abs_lt.mp hzstrip).2
  have hE' := hasDerivAt_thetaCuspTailSecondDensityDeBrangesE
    (z := z) (abs_lt.mp hzstrip).1
  exact hS.div hE' hE

/-- Exact flow law: the derivative of the ratio along its division-free projective flow is the
nonnegative Wronskian norm-square.  It is strictly positive exactly at regular points. -/
theorem thetaCuspTailSecondDensityDeBrangesProjectiveRatioDerivative_mul_flow
    {z : ℂ} (hE : thetaCuspTailSecondDensityDeBrangesE z ≠ 0) :
    (thetaCuspTailSecondDensityDeBrangesProjectiveWronskian z /
        thetaCuspTailSecondDensityDeBrangesE z ^ 2) *
        thetaCuspTailSecondDensityDeBrangesProjectiveFlow z =
      (Complex.normSq
        (thetaCuspTailSecondDensityDeBrangesProjectiveWronskian z) : ℂ) := by
  unfold thetaCuspTailSecondDensityDeBrangesProjectiveFlow
  field_simp [hE]
  simp only [Complex.normSq_apply, Complex.ofReal_add, Complex.ofReal_mul]
  apply Complex.ext <;> simp
  ring

/-- On the noncentral regular chart, the single antipodal projective value is exactly the Xi
divisor. -/
theorem thetaCuspTailSecondDensityDeBrangesProjectiveRatio_eq_neg_one_iff
    {z : ℂ} (hzstrip : |z.im| < 1) (hz0 : z ≠ 0)
    (hE : thetaCuspTailSecondDensityDeBrangesE z ≠ 0) :
    thetaCuspTailSecondDensityDeBrangesProjectiveRatio z = -1 ↔ XiC z = 0 := by
  have hsum := thetaCuspTailSecondDensityDeBrangesE_add_sharp hzstrip
  constructor
  · intro hratio
    have hsharp : thetaCuspTailSecondDensityDeBrangesESharp z =
        -thetaCuspTailSecondDensityDeBrangesE z := by
      rw [thetaCuspTailSecondDensityDeBrangesProjectiveRatio,
        div_eq_iff hE] at hratio
      simpa using hratio
    rw [hsharp] at hsum
    have hfac : (4 : ℂ) * z ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hz0)
    have hprod : ((4 : ℂ) * z ^ 2) * XiC z = 0 := by
      calc
        ((4 : ℂ) * z ^ 2) * XiC z =
            thetaCuspTailSecondDensityDeBrangesE z +
              -thetaCuspTailSecondDensityDeBrangesE z := by
                simpa only [mul_assoc] using hsum.symm
        _ = 0 := by ring
    exact (mul_eq_zero.mp hprod).resolve_left hfac
  · intro hz
    rw [thetaCuspTailSecondDensityDeBrangesProjectiveRatio, div_eq_iff hE]
    rw [hz, mul_zero] at hsum
    linear_combination hsum

/-- Public real-boundary value law for the source-selected completed channel. -/
theorem thetaCuspTailSecondDensityDeBrangesE_re_ofReal (t : ℝ) :
    (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).re =
      2 * t ^ 2 * (XiC (t : ℂ)).re := by
  have h := thetaCuspTailSecondDensityPhaseValue_re_ofReal_crossed t
  have hq : (t : ℂ) ^ 2 + 1 / 4 = ((t ^ 2 + 1 / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  unfold thetaCuspTailSecondDensityDeBrangesE
  rw [hq]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  norm_num
  linarith

theorem thetaCuspTailSecondDensityDeBrangesE_re_ofReal_eq_zero
    {t : ℝ} (hz : XiC (t : ℂ) = 0) :
    (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).re = 0 := by
  rw [thetaCuspTailSecondDensityDeBrangesE_re_ofReal, hz]
  simp

/-- Positivity of the odd boundary channel makes `E` a valid projective chart at every positive
real point. -/
theorem thetaCuspTailSecondDensityDeBrangesE_ofReal_ne_zero
    {t : ℝ} (ht : 0 < t) :
    thetaCuspTailSecondDensityDeBrangesE (t : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.zero_im] at him
  exact (thetaCuspTailSecondDensityDeBrangesE_im_ofReal_pos ht).ne' him

/-- Every positive real Xi zero is the boundary antipode of the projective ratio. -/
theorem thetaCuspTailSecondDensityDeBrangesProjectiveRatio_ofReal_eq_neg_one
    {t : ℝ} (ht : 0 < t) (hz : XiC (t : ℂ) = 0) :
    thetaCuspTailSecondDensityDeBrangesProjectiveRatio (t : ℂ) = -1 := by
  apply (thetaCuspTailSecondDensityDeBrangesProjectiveRatio_eq_neg_one_iff
    (z := (t : ℂ)) (by simp) (Complex.ofReal_ne_zero.mpr ht.ne')
    (thetaCuspTailSecondDensityDeBrangesE_ofReal_ne_zero ht)).2
  exact hz

/-- A positive simple real Xi zero is a regular point of the projective ratio. -/
theorem thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_ofReal_ne_zero
    {t : ℝ} (ht : 0 < t) (hz : XiC (t : ℂ) = 0)
    (hsimple : deriv XiC (t : ℂ) ≠ 0) :
    thetaCuspTailSecondDensityDeBrangesProjectiveWronskian (t : ℂ) ≠ 0 := by
  rw [thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_eq_at_XiC_zero
    (z := (t : ℂ)) (by simp) hz]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num)
        (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht.ne')))
      hsimple)
    (thetaCuspTailSecondDensityDeBrangesE_ofReal_ne_zero ht)

/-- Exact seam separating the genuine projective Wronskian from the previous full-density
connection.  The latter differentiates `XiC / F`; it does not differentiate `E# / E`. -/
theorem thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_sub_fullConnection
    {z : ℂ} (hzstrip : |z.im| < 1) (hz : XiC z = 0) :
    thetaCuspTailSecondDensityDeBrangesProjectiveWronskian z -
        (z ^ 2 + 1 / 4) * xiFullDensityReflectedConnection z =
      -(z ^ 2 * deriv XiC z) := by
  rw [thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_eq_at_XiC_zero
      hzstrip hz,
    xiFullDensityReflectedConnection_eq_at_XiC_zero hzstrip hz]
  unfold thetaCuspTailSecondDensityDeBrangesE
  ring

/-- At every noncentral simple collision the two proposed connections are provably different. -/
theorem thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_ne_fullConnection
    {z : ℂ} (hzstrip : |z.im| < 1)
    (hz : XiC z = 0) (hsimple : deriv XiC z ≠ 0) :
    thetaCuspTailSecondDensityDeBrangesProjectiveWronskian z ≠
      (z ^ 2 + 1 / 4) * xiFullDensityReflectedConnection z := by
  intro heq
  have hzero :
      thetaCuspTailSecondDensityDeBrangesProjectiveWronskian z -
        (z ^ 2 + 1 / 4) * xiFullDensityReflectedConnection z = 0 :=
    sub_eq_zero.mpr heq
  rw [thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_sub_fullConnection
    hzstrip hz] at hzero
  have hprod : z ^ 2 * deriv XiC z = 0 := neg_eq_zero.mp hzero
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact XiC_zero_ne hz
  exact (mul_ne_zero (pow_ne_zero 2 hz0) hsimple) hprod

/-- Complex tangent derivative of the projective ratio at a positive real collision. -/
theorem hasDerivAt_thetaCuspTailSecondDensityDeBrangesProjectiveRatio_ofReal
    {t : ℝ} (ht : 0 < t) (hz : XiC (t : ℂ) = 0) :
    HasDerivAt thetaCuspTailSecondDensityDeBrangesProjectiveRatio
      (4 * (t : ℂ) ^ 2 * deriv XiC (t : ℂ) /
        thetaCuspTailSecondDensityDeBrangesE (t : ℂ)) (t : ℂ) := by
  have h := hasDerivAt_thetaCuspTailSecondDensityDeBrangesProjectiveRatio
    (z := (t : ℂ)) (by simp)
      (thetaCuspTailSecondDensityDeBrangesE_ofReal_ne_zero ht)
  convert h using 1
  rw [thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_eq_at_XiC_zero
    (z := (t : ℂ)) (by simp) hz]
  field_simp [thetaCuspTailSecondDensityDeBrangesE_ofReal_ne_zero ht]

/-- Real normal velocity with which the projective ratio leaves `-1` above a real Xi zero. -/
def thetaCuspTailSecondDensityDeBrangesProjectiveVerticalVelocity (t : ℝ) : ℝ :=
  4 * t ^ 2 * (deriv XiC (t : ℂ)).re /
    (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im

/-- Exact boundary-entry law.  The horizontal derivative is imaginary, while the inward normal
derivative is the displayed real velocity.  Its sign is the sign of the real Xi derivative. -/
theorem hasDerivAt_thetaCuspTailSecondDensityDeBrangesProjectiveRatio_vertical
    {t : ℝ} (ht : 0 < t) (hz : XiC (t : ℂ) = 0) :
    HasDerivAt
      (fun y : ℝ => thetaCuspTailSecondDensityDeBrangesProjectiveRatio
        ((t : ℂ) + (y : ℂ) * I))
      (thetaCuspTailSecondDensityDeBrangesProjectiveVerticalVelocity t : ℂ) 0 := by
  have hpath : HasDerivAt
      (fun y : ℝ => (t : ℂ) + (y : ℂ) * I) I 0 := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I
    simpa using h.const_add (t : ℂ)
  have hratio0 :=
    hasDerivAt_thetaCuspTailSecondDensityDeBrangesProjectiveRatio
      (z := (t : ℂ) + ((0 : ℝ) : ℂ) * I) (by simp)
      (by simpa using thetaCuspTailSecondDensityDeBrangesE_ofReal_ne_zero ht)
  have hratio : HasDerivAt
      (fun y : ℝ => thetaCuspTailSecondDensityDeBrangesProjectiveRatio
        ((t : ℂ) + (y : ℂ) * I))
      ((thetaCuspTailSecondDensityDeBrangesProjectiveWronskian (t : ℂ) /
        thetaCuspTailSecondDensityDeBrangesE (t : ℂ) ^ 2) * I) 0 := by
    simpa [Function.comp_def] using hratio0.comp 0 hpath
  have hEre := thetaCuspTailSecondDensityDeBrangesE_re_ofReal_eq_zero hz
  have hEeq : thetaCuspTailSecondDensityDeBrangesE (t : ℂ) =
      I * ((thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im : ℂ) := by
    apply Complex.ext <;> simp [hEre]
  have hconj := deriv_XiC_conj (t : ℂ)
  simp only [conj_ofReal] at hconj
  have hXiim : (deriv XiC (t : ℂ)).im = 0 := by
    have him := congrArg Complex.im hconj
    simp only [conj_im] at him
    linarith
  have hXieq : deriv XiC (t : ℂ) = ((deriv XiC (t : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [hXiim]
  have himne : (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im ≠ 0 :=
    (thetaCuspTailSecondDensityDeBrangesE_im_ofReal_pos ht).ne'
  have hcoeff :
      (thetaCuspTailSecondDensityDeBrangesProjectiveVerticalVelocity t : ℂ) =
        (thetaCuspTailSecondDensityDeBrangesProjectiveWronskian (t : ℂ) /
          thetaCuspTailSecondDensityDeBrangesE (t : ℂ) ^ 2) * I := by
    unfold thetaCuspTailSecondDensityDeBrangesProjectiveVerticalVelocity
    rw [thetaCuspTailSecondDensityDeBrangesProjectiveWronskian_eq_at_XiC_zero
      (z := (t : ℂ)) (by simp) hz, hEeq, hXieq]
    push_cast
    field_simp [I_ne_zero, Complex.ofReal_ne_zero.mpr himne]
    simp
    ring
  rw [hcoeff]
  exact hratio

/-- Simple real Xi zeros enter the negative-ray geometry transversely: normal velocity cannot
vanish. -/
theorem thetaCuspTailSecondDensityDeBrangesProjectiveVerticalVelocity_ne_zero
    {t : ℝ} (ht : 0 < t) (hsimple : deriv XiC (t : ℂ) ≠ 0) :
    thetaCuspTailSecondDensityDeBrangesProjectiveVerticalVelocity t ≠ 0 := by
  have hconj := deriv_XiC_conj (t : ℂ)
  simp only [conj_ofReal] at hconj
  have hXiim : (deriv XiC (t : ℂ)).im = 0 := by
    have him := congrArg Complex.im hconj
    simp only [conj_im] at him
    linarith
  have hXieq : deriv XiC (t : ℂ) = ((deriv XiC (t : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [hXiim]
  have hXire : (deriv XiC (t : ℂ)).re ≠ 0 := by
    intro hre
    apply hsimple
    rw [hXieq, hre]
    simp
  unfold thetaCuspTailSecondDensityDeBrangesProjectiveVerticalVelocity
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht.ne')) hXire)
    (thetaCuspTailSecondDensityDeBrangesE_im_ofReal_pos ht).ne'

end

end RHTower
