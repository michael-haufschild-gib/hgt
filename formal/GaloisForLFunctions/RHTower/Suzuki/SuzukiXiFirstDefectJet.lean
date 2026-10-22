import GaloisForLFunctions.RHTower.SquaredXiCompleteMonotonicity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiXiDonoghueTarget
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The first normalized Xi–Suzuki defect jet

The normalized Xi Livšic target has a source-visible first jet at Suzuki's anchor.  This file
computes that jet from the multiplicity-exact squared-zero moment tower and proves, without RH,

`77 / 85 < Re (2 i Θ_Xi'(i)) < 1`.

In fact the jet is real.  The lower constant comes from two unconditional divisor facts:

* every nontrivial Xi zero has squared imaginary height greater than `41 / 2`;
* every zero lies in the open critical strip, so its centered squared real part is less than `1/4`.

Consequently every shifted squared-zero node has real part greater than `81 / 4`.  An atomwise
resolvent inequality sums strictly over the multiplicity copy and gives the logarithmic-derivative
bound.  The theorem also proves that compact-open convergence to the Xi Livšic target forces
convergence of the first anchored defect jets.  This is an unconditional target obstruction, not a
construction of Suzuki's missing source-selected limit and not a proof of RH.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every shifted squared-zero atom satisfies the strict `85`-to-`4` resolvent inequality forced
by the unconditional first-zero-height gap and the critical strip. -/
theorem eightyFive_mul_re_xiShiftedReciprocalSquare_sq_lt_four_mul_re
    (q : XiZeroCopy) :
    85 * (xiShiftedReciprocalSquare 1 q ^ (2 : ℕ)).re <
      4 * (xiShiftedReciprocalSquare 1 q).re := by
  let A : ℝ := 1 + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have ht : 81 / 4 < (xiSquaredNode q).re := by
    rw [xiSquaredNode_re]
    have hv := xiZeroCopy_fortyOne_div_two_lt_im_sq q
    have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
    linarith
  have hA : 85 / 4 < A := by
    dsimp only [A]
    linarith
  have hA0 : 0 < A := by linarith
  have hden : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA0, sq_nonneg B]
  have hcoord : (1 : ℂ) + xiSquaredNode q = (A : ℂ) + (B : ℂ) * I := by
    apply Complex.ext <;> simp [A, B]
  rw [xiShiftedReciprocalSquare_eq_inv (by norm_num)]
  change 85 * (((1 : ℂ) + xiSquaredNode q)⁻¹ ^ (2 : ℕ)).re <
    4 * (((1 : ℂ) + xiSquaredNode q)⁻¹).re
  rw [hcoord, pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, mul_one, add_zero, zero_add]
  have hgap : 85 * A < 4 * (A ^ (2 : ℕ) + B ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg B]
  field_simp
  nlinarith [hden, sq_nonneg (A ^ (2 : ℕ) + B ^ (2 : ℕ))]

/-- Summing the strict atomwise inequality gives a strict relation between the first two
multiplicity-exact shifted squared-zero moments at base `1`. -/
theorem eightyFive_mul_re_xiShiftedReciprocalMoment_one_lt_four_mul_zero :
    85 * (xiShiftedReciprocalMoment 1 1).re <
      4 * (xiShiftedReciprocalMoment 1 0).re := by
  have hsum1C :
      Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare 1 q ^ (0 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow (by norm_num) 0
  have hsum2C :
      Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare 1 q ^ (1 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow (by norm_num) 1
  have hsum1 : Summable (fun q : XiZeroCopy =>
      4 * (xiShiftedReciprocalSquare 1 q).re) := by
    simpa using (Complex.reCLM.summable hsum1C).mul_left 4
  have hsum2 : Summable (fun q : XiZeroCopy =>
      85 * (xiShiftedReciprocalSquare 1 q ^ (2 : ℕ)).re) := by
    simpa using (Complex.reCLM.summable hsum2C).mul_left 85
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  have hlt := hsum2.tsum_lt_tsum (i := q0)
    (fun q =>
      (eightyFive_mul_re_xiShiftedReciprocalSquare_sq_lt_four_mul_re q).le)
    (eightyFive_mul_re_xiShiftedReciprocalSquare_sq_lt_four_mul_re q0) hsum1
  change 85 * (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare 1 q ^ (1 + 1)).re <
    4 * (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare 1 q ^ (0 + 1)).re
  rw [Complex.re_tsum hsum2C, Complex.re_tsum hsum1C]
  simpa only [tsum_mul_left, zero_add, pow_one] using hlt

/-- On the positive real ray, the Xi logarithmic derivative is the radial coordinate times the
zeroth shifted squared-zero moment. -/
theorem xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment
    {w : ℝ} (hw : 0 < w) :
    xiRealLogDeriv w =
      w * (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) 0).re := by
  have h := squaredXiRadialField_sq_eq hw
  rw [squaredXiRadialField] at h
  field_simp [hw.ne'] at h
  linarith

/-- Exact first derivative of the positive-ray Xi logarithmic derivative at the Suzuki base. -/
theorem deriv_xiRealLogDeriv_one_eq :
    deriv xiRealLogDeriv 1 =
      (xiShiftedReciprocalMoment 1 0).re -
        2 * (xiShiftedReciprocalMoment 1 1).re := by
  have hmoment :=
    hasDerivAt_re_xiShiftedReciprocalMoment (y := (1 : ℝ) ^ (2 : ℕ)) (by norm_num) 0
  have hpow : HasDerivAt (fun w : ℝ => w ^ (2 : ℕ)) 2 1 := by
    simpa using hasDerivAt_pow 2 (1 : ℝ)
  have hraw := hmoment.comp (h := fun w : ℝ => w ^ (2 : ℕ)) (1 : ℝ) hpow
  have hrhs := (hasDerivAt_id (1 : ℝ)).mul hraw
  have heq : xiRealLogDeriv =ᶠ[nhds (1 : ℝ)]
      fun w : ℝ => w * (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) 0).re := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with w hw
    exact xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment hw
  have hlhs := hasDerivAt_xiRealLogDeriv (1 : ℝ)
  have hu := hlhs.unique (hrhs.congr_of_eventuallyEq heq)
  rw [hlhs.deriv]
  convert hu using 1
  all_goals norm_num
  all_goals ring

/-- Quantitative lower bound for the first positive-ray logarithmic jet. -/
theorem seventySeven_div_eightyFive_mul_xiRealLogDeriv_one_lt_deriv :
    (77 : ℝ) / 85 * xiRealLogDeriv 1 <
      deriv xiRealLogDeriv 1 := by
  have hm0 := re_xiShiftedReciprocalMoment_pos
    (y := (1 : ℝ)) (by norm_num) (n := 0) (by norm_num)
  have hbound :=
    eightyFive_mul_re_xiShiftedReciprocalMoment_one_lt_four_mul_zero
  rw [deriv_xiRealLogDeriv_one_eq,
    xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment (by norm_num)]
  norm_num
  nlinarith

/-- Suzuki's normalization scale is exactly the positive-ray Xi logarithmic derivative at `1`. -/
theorem xiHedenmalmDonoghueScale_eq_xiRealLogDeriv_one :
    xiHedenmalmDonoghueScale = xiRealLogDeriv 1 := by
  have hchain := logDeriv_XiC_eq_mul_I_logDeriv_xi I
  have harg : (1 / 2 : ℂ) + I * I = -(1 / 2 : ℂ) := by
    rw [I_mul_I]
    ring
  rw [harg] at hchain
  have hrec := logDeriv_xi_reciprocity (3 / 2 : ℂ)
  norm_num at hrec
  rw [xiHedenmalmDonoghueScale, hchain, hrec, xiRealLogDeriv]
  norm_num [Complex.mul_im]

/-- The derivative of the Xi logarithmic derivative is invariant under functional-equation
reflection. -/
theorem deriv_logDeriv_xi_one_sub (sigma : ℂ) :
    deriv (logDeriv xi) (1 - sigma) = deriv (logDeriv xi) sigma := by
  have hfun : (fun s : ℂ => logDeriv xi (1 - s)) = -(logDeriv xi) := by
    funext s
    exact logDeriv_xi_reciprocity s
  have hd := congrArg (fun f : ℂ → ℂ => iteratedDeriv 1 f sigma) hfun
  change iteratedDeriv 1 (fun s : ℂ => logDeriv xi (1 - s)) sigma =
    iteratedDeriv 1 (-(logDeriv xi)) sigma at hd
  rw [congrFun (iteratedDeriv_comp_const_sub 1 (logDeriv xi) 1) sigma,
    iteratedDeriv_neg] at hd
  norm_num [iteratedDeriv_one] at hd
  exact hd

private theorem logDeriv_xi_conj_for_firstDefectJet (s : ℂ) :
    logDeriv xi ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (logDeriv xi s) := by
  have h := congrArg Neg.neg (seamFluxCochain_conj s)
  simpa only [seamFluxCochain, neg_neg, map_neg] using h

private theorem deriv_logDeriv_xi_ofReal_im_eq_zero (sigma : ℝ) :
    (deriv (logDeriv xi) (sigma : ℂ)).im = 0 := by
  have hfun :
      (starRingEnd ℂ) ∘ (logDeriv xi) ∘ (starRingEnd ℂ) =
        logDeriv xi := by
    funext z
    simp only [Function.comp_apply]
    rw [logDeriv_xi_conj_for_firstDefectJet, Complex.conj_conj]
  have hder : deriv (logDeriv xi) =
      (starRingEnd ℂ) ∘ deriv (logDeriv xi) ∘ (starRingEnd ℂ) := by
    calc
      deriv (logDeriv xi) =
          deriv ((starRingEnd ℂ) ∘ (logDeriv xi) ∘ (starRingEnd ℂ)) :=
        congrArg deriv hfun.symm
      _ = (starRingEnd ℂ) ∘ deriv (logDeriv xi) ∘ (starRingEnd ℂ) :=
        deriv_conj_conj
  have hfix :
      deriv (logDeriv xi) (sigma : ℂ) =
        (starRingEnd ℂ) (deriv (logDeriv xi) (sigma : ℂ)) := by
    have hsigma : (starRingEnd ℂ) (sigma : ℂ) = (sigma : ℂ) := by simp
    simpa only [Function.comp_apply, hsigma] using congrFun hder (sigma : ℂ)
  have him := congrArg Complex.im hfix
  rw [Complex.conj_im] at him
  linarith

/-- The centered logarithmic-derivative second jet at `i` is the negative ordinary Xi
logarithmic-derivative second jet at `3/2`. -/
theorem deriv_logDeriv_XiC_I_eq_neg :
    deriv (logDeriv XiC) I =
      -deriv (logDeriv xi) (3 / 2 : ℂ) := by
  have hxi : xi (-(1 / 2 : ℂ)) ≠ 0 := by
    have h := xi_ofReal_shift_ne_zero (-1)
    have hcoord : (1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) = -(1 / 2 : ℂ) := by
      norm_num
    rwa [hcoord] at h
  have harg : (1 / 2 : ℂ) + I * I = -(1 / 2 : ℂ) := by
    rw [I_mul_I]
    ring
  have hxi' : xi ((1 / 2 : ℂ) + I * I) ≠ 0 := by
    rw [harg]
    exact hxi
  have hout : HasDerivAt (logDeriv xi)
      (deriv (logDeriv xi) ((1 / 2 : ℂ) + I * I))
      ((1 / 2 : ℂ) + I * I) :=
    (differentiableAt_logDeriv_xi hxi').hasDerivAt
  have hinner : HasDerivAt (fun z : ℂ => 1 / 2 + z * I) I I := by
    simpa using ((hasDerivAt_id I).mul_const I).const_add (1 / 2 : ℂ)
  have hcomp := hout.comp (h := fun z : ℂ => 1 / 2 + z * I) I hinner
  have hmul := hcomp.const_mul I
  have hfun : logDeriv XiC =
      fun z : ℂ => I * logDeriv xi (1 / 2 + z * I) := by
    funext z
    exact logDeriv_XiC_eq_mul_I_logDeriv_xi z
  have hderiv : deriv (fun z : ℂ =>
      I * logDeriv xi (1 / 2 + z * I)) I =
      I * (deriv (logDeriv xi) ((1 / 2 : ℂ) + I * I) * I) := by
    simpa [Function.comp_def] using hmul.deriv
  rw [hfun, hderiv, harg]
  have href := deriv_logDeriv_xi_one_sub (3 / 2 : ℂ)
  norm_num at href
  rw [href]
  calc
    I * (deriv (logDeriv xi) (3 / 2 : ℂ) * I) =
        (I * I) * deriv (logDeriv xi) (3 / 2 : ℂ) := by ring
    _ = -deriv (logDeriv xi) (3 / 2 : ℂ) := by
      rw [I_mul_I]
      ring

/-- Exact derivative of the normalized Xi Donoghue target at Suzuki's anchor. -/
theorem deriv_xiHedenmalmDonoghueTarget_I_eq :
    deriv xiHedenmalmDonoghueTarget I =
      deriv (logDeriv xi) (3 / 2 : ℂ) /
        (xiHedenmalmDonoghueScale : ℂ) := by
  have hXi : XiC I ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_nine_halves
    norm_num
  have hlog : DifferentiableAt ℂ (logDeriv XiC) I := by
    have h1 : DifferentiableAt ℂ (deriv XiC) I :=
      (XiC_analytic I (Set.mem_univ I)).deriv.differentiableAt
    have h2 : DifferentiableAt ℂ XiC I :=
      (XiC_analytic I (Set.mem_univ I)).differentiableAt
    simpa [logDeriv] using h1.div h2 hXi
  have htarget := hlog.hasDerivAt.neg.div_const
    (xiHedenmalmDonoghueScale : ℂ)
  have hderiv : deriv (fun z : ℂ =>
      (-logDeriv XiC z) / (xiHedenmalmDonoghueScale : ℂ)) I =
      -deriv (logDeriv XiC) I / (xiHedenmalmDonoghueScale : ℂ) := by
    simpa only [Pi.neg_apply] using htarget.deriv
  change deriv (fun z : ℂ =>
    (-logDeriv XiC z) / (xiHedenmalmDonoghueScale : ℂ)) I = _
  rw [hderiv, deriv_logDeriv_XiC_I_eq_neg]
  ring

/-- The normalized Xi Donoghue scale is unconditionally positive. -/
theorem xiHedenmalmDonoghueScale_pos :
    0 < xiHedenmalmDonoghueScale := by
  rw [xiHedenmalmDonoghueScale_eq_xiRealLogDeriv_one,
    xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment (by norm_num)]
  norm_num
  exact re_xiShiftedReciprocalMoment_pos
    (y := (1 : ℝ)) (by norm_num) (n := 0) (by norm_num)

/-- The normalized Xi Donoghue target has the exact Suzuki anchor unconditionally. -/
theorem xiHedenmalmDonoghueTarget_I :
    xiHedenmalmDonoghueTarget I = I := by
  have hXi : XiC I ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_nine_halves
    norm_num
  have hre := re_logDeriv_XiC_I_eq_zero hXi
  have hraw :
      -logDeriv XiC I = (xiHedenmalmDonoghueScale : ℂ) * I := by
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero]
      linarith
    · simp [xiHedenmalmDonoghueScale]
  rw [xiHedenmalmDonoghueTarget, hraw]
  field_simp [xiHedenmalmDonoghueScale_pos.ne']

/-- The real part of the normalized Donoghue first jet is the logarithmic-jet ratio. -/
theorem deriv_xiHedenmalmDonoghueTarget_I_re_eq :
    (deriv xiHedenmalmDonoghueTarget I).re =
      deriv xiRealLogDeriv 1 / xiHedenmalmDonoghueScale := by
  rw [deriv_xiHedenmalmDonoghueTarget_I_eq, Complex.div_ofReal_re]
  have h := (hasDerivAt_xiRealLogDeriv (1 : ℝ)).deriv
  norm_num at h
  rw [h]

/-- The normalized Donoghue first jet is a real complex number. -/
theorem deriv_xiHedenmalmDonoghueTarget_I_eq_ofReal :
    deriv xiHedenmalmDonoghueTarget I =
      ((deriv xiRealLogDeriv 1 / xiHedenmalmDonoghueScale : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [deriv_xiHedenmalmDonoghueTarget_I_re_eq]
    simp
  · have him : (deriv (logDeriv xi) (3 / 2 : ℂ)).im = 0 := by
      convert deriv_logDeriv_xi_ofReal_im_eq_zero (3 / 2 : ℝ) using 1
      norm_num
    rw [deriv_xiHedenmalmDonoghueTarget_I_eq, Complex.div_ofReal_im, him]
    simp

/-- Strict upper bound for the first positive-ray logarithmic jet. -/
theorem deriv_xiRealLogDeriv_one_lt :
    deriv xiRealLogDeriv 1 < xiRealLogDeriv 1 := by
  have hm1 := re_xiShiftedReciprocalMoment_pos
    (y := (1 : ℝ)) (by norm_num) (n := 1) (by norm_num)
  rw [deriv_xiRealLogDeriv_one_eq,
    xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment (by norm_num)]
  norm_num
  linarith

private theorem deriv_xiHedenmalmDonoghueTarget_I_re_mem_Ioo :
    (deriv xiHedenmalmDonoghueTarget I).re ∈
      Set.Ioo ((77 : ℝ) / 85) 1 := by
  rw [deriv_xiHedenmalmDonoghueTarget_I_re_eq,
    xiHedenmalmDonoghueScale_eq_xiRealLogDeriv_one]
  have hc : 0 < xiRealLogDeriv 1 := by
    simpa only [xiHedenmalmDonoghueScale_eq_xiRealLogDeriv_one] using
      xiHedenmalmDonoghueScale_pos
  constructor
  · rw [lt_div_iff₀ hc]
    exact seventySeven_div_eightyFive_mul_xiRealLogDeriv_one_lt_deriv
  · rw [div_lt_one hc]
    exact deriv_xiRealLogDeriv_one_lt

/-- Cayley differentiation at the normalized anchor identifies the first Livšic defect jet with
the first Donoghue jet. -/
theorem two_mul_I_mul_deriv_xiHedenmalmLivsicTarget_I :
    2 * I * deriv xiHedenmalmLivsicTarget I =
      deriv xiHedenmalmDonoghueTarget I := by
  have hXi : XiC I ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_nine_halves
    norm_num
  have hlog : DifferentiableAt ℂ (logDeriv XiC) I := by
    have h1 : DifferentiableAt ℂ (deriv XiC) I :=
      (XiC_analytic I (Set.mem_univ I)).deriv.differentiableAt
    have h2 : DifferentiableAt ℂ XiC I :=
      (XiC_analytic I (Set.mem_univ I)).differentiableAt
    simpa [logDeriv] using h1.div h2 hXi
  have hm : DifferentiableAt ℂ xiHedenmalmDonoghueTarget I := by
    change DifferentiableAt ℂ
      (fun z : ℂ => (-logDeriv XiC z) /
        (xiHedenmalmDonoghueScale : ℂ)) I
    exact hlog.neg.div_const _
  have hnum : HasDerivAt
      (fun z => xiHedenmalmDonoghueTarget z - I)
      (deriv xiHedenmalmDonoghueTarget I) I :=
    hm.hasDerivAt.sub_const I
  have hden : HasDerivAt
      (fun z => xiHedenmalmDonoghueTarget z + I)
      (deriv xiHedenmalmDonoghueTarget I) I :=
    hm.hasDerivAt.add_const I
  have hne : xiHedenmalmDonoghueTarget I + I ≠ 0 := by
    rw [xiHedenmalmDonoghueTarget_I]
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hquot : HasDerivAt
      (fun z => (xiHedenmalmDonoghueTarget z - I) /
        (xiHedenmalmDonoghueTarget z + I))
      ((deriv xiHedenmalmDonoghueTarget I *
          (xiHedenmalmDonoghueTarget I + I) -
        (xiHedenmalmDonoghueTarget I - I) *
          deriv xiHedenmalmDonoghueTarget I) /
        (xiHedenmalmDonoghueTarget I + I) ^ (2 : ℕ)) I :=
    hnum.div hden hne
  have hderiv : deriv (fun z : ℂ =>
      (xiHedenmalmDonoghueTarget z - I) /
        (xiHedenmalmDonoghueTarget z + I)) I =
      (deriv xiHedenmalmDonoghueTarget I *
          (xiHedenmalmDonoghueTarget I + I) -
        (xiHedenmalmDonoghueTarget I - I) *
          deriv xiHedenmalmDonoghueTarget I) /
        (xiHedenmalmDonoghueTarget I + I) ^ (2 : ℕ) :=
    hquot.deriv
  change 2 * I * deriv (fun z : ℂ =>
      (xiHedenmalmDonoghueTarget z - I) /
        (xiHedenmalmDonoghueTarget z + I)) I =
      deriv xiHedenmalmDonoghueTarget I
  rw [hderiv, xiHedenmalmDonoghueTarget_I]
  field_simp [I_ne_zero]
  ring

/-- Real first anchored Livšic defect jet of the normalized Xi target. -/
def xiHedenmalmLivsicFirstDefectJet : ℝ :=
  (2 * I * deriv xiHedenmalmLivsicTarget I).re

/-- Source-only prime--Gamma calibration scalar for Suzuki's first defect.  Both entries are
absolutely convergent negative-binomial transforms of the normalized prime--archimedean moment
tower at the safe shift `1`; no Xi zero occurs in this definition. -/
def primeArchSuzukiFirstDefectCalibration : ℝ :=
  ((primeArchShiftedReciprocalMoment 1 0).re -
      2 * (primeArchShiftedReciprocalMoment 1 1).re) /
    (primeArchShiftedReciprocalMoment 1 0).re

/-- The zeroth safe-shift prime--Gamma moment has strictly positive real part. -/
theorem re_primeArchShiftedReciprocalMoment_one_zero_pos :
    0 < (primeArchShiftedReciprocalMoment 1 0).re := by
  rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
    (y := 1) (by norm_num) (by norm_num) 0]
  exact re_xiShiftedReciprocalMoment_pos
    (y := (1 : ℝ)) (by norm_num) (n := 0) (by norm_num)

/-- The first safe-shift prime--Gamma moment has strictly positive real part. -/
theorem re_primeArchShiftedReciprocalMoment_one_one_pos :
    0 < (primeArchShiftedReciprocalMoment 1 1).re := by
  rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
    (y := 1) (by norm_num) (by norm_num) 1]
  exact re_xiShiftedReciprocalMoment_pos
    (y := (1 : ℝ)) (by norm_num) (n := 1) (by norm_num)

/-- **Safe-Euler prime--Gamma first-jet inequality.**  The divisor gap transports exactly to a
strict source-only inequality between the first two shifted prime--archimedean moments. -/
theorem eightyFive_mul_re_primeArchShiftedReciprocalMoment_one_lt_four_mul_zero :
    85 * (primeArchShiftedReciprocalMoment 1 1).re <
      4 * (primeArchShiftedReciprocalMoment 1 0).re := by
  rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 1,
    ← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 0]
  exact eightyFive_mul_re_xiShiftedReciprocalMoment_one_lt_four_mul_zero

/-- Exact divisor/logarithmic-jet representation of the first Xi Livšic defect jet. -/
theorem xiHedenmalmLivsicFirstDefectJet_eq_log_ratio :
    xiHedenmalmLivsicFirstDefectJet =
      deriv xiRealLogDeriv 1 / xiHedenmalmDonoghueScale := by
  rw [xiHedenmalmLivsicFirstDefectJet,
    two_mul_I_mul_deriv_xiHedenmalmLivsicTarget_I,
    deriv_xiHedenmalmDonoghueTarget_I_re_eq]

/-- **Prime--Gamma source identity for the Xi defect calibration.**  The target-defined anchored
jet is exactly the source-only safe-Euler moment ratio.  Thus matching this one scalar need not
select an Xi zero or assume RH. -/
theorem xiHedenmalmLivsicFirstDefectJet_eq_primeArchSuzukiFirstDefectCalibration :
    xiHedenmalmLivsicFirstDefectJet =
      primeArchSuzukiFirstDefectCalibration := by
  rw [xiHedenmalmLivsicFirstDefectJet_eq_log_ratio,
    deriv_xiRealLogDeriv_one_eq,
    xiHedenmalmDonoghueScale_eq_xiRealLogDeriv_one,
    xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment (by norm_num)]
  norm_num
  rw [xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 0,
    xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 1]
  rfl

/-- The source-only prime--Gamma calibration lies in the same strict defect cone, proved directly
from its two positive moments and their `85`-to-`4` inequality. -/
theorem primeArchSuzukiFirstDefectCalibration_mem_Ioo :
    primeArchSuzukiFirstDefectCalibration ∈ Set.Ioo ((77 : ℝ) / 85) 1 := by
  have h0 := re_primeArchShiftedReciprocalMoment_one_zero_pos
  have h1 := re_primeArchShiftedReciprocalMoment_one_one_pos
  have h85 :=
    eightyFive_mul_re_primeArchShiftedReciprocalMoment_one_lt_four_mul_zero
  rw [primeArchSuzukiFirstDefectCalibration]
  constructor
  · rw [lt_div_iff₀ h0]
    nlinarith
  · rw [div_lt_one h0]
    linarith

/-- The complex anchored Livšic derivative is exactly the real first-defect scalar. -/
theorem xiHedenmalmLivsicFirstDefectJet_complex :
    (xiHedenmalmLivsicFirstDefectJet : ℂ) =
      2 * I * deriv xiHedenmalmLivsicTarget I := by
  rw [xiHedenmalmLivsicFirstDefectJet,
    two_mul_I_mul_deriv_xiHedenmalmLivsicTarget_I,
    deriv_xiHedenmalmDonoghueTarget_I_eq_ofReal]
  simp only [Complex.div_ofReal_re, Complex.ofReal_re, Complex.ofReal_div]

/-- **Unconditional Xi first-defect jet gap.**  The exact normalized target lies in the strict
real interval `(77/85, 1)`. -/
theorem xiHedenmalmLivsicFirstDefectJet_mem_Ioo :
    xiHedenmalmLivsicFirstDefectJet ∈ Set.Ioo ((77 : ℝ) / 85) 1 := by
  simpa only [xiHedenmalmLivsicFirstDefectJet,
    two_mul_I_mul_deriv_xiHedenmalmLivsicTarget_I] using
    deriv_xiHedenmalmDonoghueTarget_I_re_mem_Ioo

/-- Compact-open convergence to the exact Xi Livšic target forces convergence of the first
anchored defect jets.  Thus no higher-order-only source escape can identify the target. -/
theorem xiHedenmalmLivsic_firstDefectJet_tendsto_of_locallyUniform
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (theta : ι → ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn theta xiHedenmalmLivsicTarget l
      {z : ℂ | 0 < z.im})
    (hdiff : ∀ᶠ j in l, DifferentiableOn ℂ (theta j) {z : ℂ | 0 < z.im}) :
    Tendsto (fun j => 2 * I * deriv (theta j) I) l
      (nhds (xiHedenmalmLivsicFirstDefectJet : ℂ)) := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hderiv := hconv.deriv hdiff hopen
  have hpoint : Tendsto (fun j => deriv (theta j) I) l
      (nhds (deriv xiHedenmalmLivsicTarget I)) := by
    simpa only [Function.comp_apply] using hderiv.tendsto_at (by norm_num)
  have hscaled := hpoint.const_mul (2 * I)
  rw [← xiHedenmalmLivsicFirstDefectJet_complex] at hscaled
  exact hscaled

end

end RHTower
