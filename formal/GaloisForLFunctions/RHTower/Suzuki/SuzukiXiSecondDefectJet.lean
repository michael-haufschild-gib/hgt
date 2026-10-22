import GaloisForLFunctions.RHTower.Suzuki.SuzukiXiFirstDefectJet
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteApertureHermiteBiehler
import GaloisForLFunctions.RHTower.Suzuki.SuzukiDonoghueHerglotzTransform
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Strict negative second Xi–Suzuki defect jet

The first normalized Livšic jet leaves a nontrivial Suzuki shift window.  This module extracts the
next unconditional source-visible invariant.  The first-zero height gap and critical-strip bound
force the strict atomwise and summed inequalities

`85 * Re r_q^3 < 4 * Re r_q^2`,  `85 * Re M₂(1) < 4 * Re M₁(1)`.

After exact second-order Cayley transport, the disk-conjugated Xi Livšic target has the safe-Euler
prime–Gamma curvature

`8 * (2 C / A - B / A - (B / A)^2)`,

where `A,B,C` are the first three shifted prime–archimedean moments at base `1`.  This quantity
is strictly negative, unconditionally.  Thus every Suzuki source family identifying Xi must match
both the positive first defect and a negative second defect; matching the first scalar alone is not
a target-identification theorem.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

theorem eightyFive_mul_re_xiShiftedReciprocalSquare_cube_lt_four_mul_square
    (q : XiZeroCopy) :
    85 * (xiShiftedReciprocalSquare 1 q ^ 3).re <
      4 * (xiShiftedReciprocalSquare 1 q ^ 2).re := by
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
  have hden : 0 < A ^ 2 + B ^ 2 := by
    nlinarith [sq_pos_of_pos hA0, sq_nonneg B]
  have hcoord : (1 : ℂ) + xiSquaredNode q = (A : ℂ) + (B : ℂ) * I := by
    apply Complex.ext <;> simp [A, B]
  have hcoord' : ((1 : ℝ) : ℂ) + xiSquaredNode q =
      (A : ℂ) + (B : ℂ) * I := by
    norm_num
    exact hcoord
  have hre2pos :
      0 < (xiShiftedReciprocalSquare 1 q ^ 2).re := by
    exact re_xiShiftedReciprocalSquare_pow_pos_of_le_nineteen
      (by norm_num) q (by norm_num)
  rw [xiShiftedReciprocalSquare_eq_inv (by norm_num), hcoord'] at hre2pos ⊢
  have hnormSq :
      Complex.normSq ((A : ℂ) + (B : ℂ) * I) = A ^ 2 + B ^ 2 := by
    norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have hsqRe (z : ℂ) :
      (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  have hcubeRe (z : ℂ) :
      (z ^ 3).re = z.re ^ 3 - 3 * z.re * z.im ^ 2 := by
    rw [show z ^ 3 = z * z * z by ring, Complex.mul_re,
      Complex.mul_re, Complex.mul_im]
    ring
  have hre2 :
      (((A : ℂ) + (B : ℂ) * I)⁻¹ ^ 2).re =
        (A ^ 2 - B ^ 2) / (A ^ 2 + B ^ 2) ^ 2 := by
    rw [hsqRe, Complex.inv_re, Complex.inv_im, hnormSq]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, mul_one, add_zero, zero_add]
    field_simp [hden.ne']
  have hre3 :
      (((A : ℂ) + (B : ℂ) * I)⁻¹ ^ 3).re =
        A * (A ^ 2 - 3 * B ^ 2) / (A ^ 2 + B ^ 2) ^ 3 := by
    rw [hcubeRe, Complex.inv_re, Complex.inv_im, hnormSq]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, mul_one, add_zero, zero_add]
    field_simp [hden.ne']
  rw [hre2] at hre2pos
  rw [hre3, hre2]
  have hnum2 : 0 < A ^ 2 - B ^ 2 := by
    rcases div_pos_iff.mp hre2pos with hpos | hneg
    · exact hpos.1
    · nlinarith [sq_nonneg (A ^ 2 + B ^ 2)]
  have hratio :
      A ^ 2 * (A ^ 2 - 3 * B ^ 2) ≤
        (A ^ 2 - B ^ 2) * (A ^ 2 + B ^ 2) := by
    have hfactor : 0 ≤ 3 * A ^ 2 - B ^ 2 := by nlinarith
    have hprod : 0 ≤ B ^ 2 * (3 * A ^ 2 - B ^ 2) :=
      mul_nonneg (sq_nonneg B) hfactor
    nlinarith
  have hscale : 85 < 4 * A := by linarith
  have hstep :
      85 * A * (A ^ 2 - 3 * B ^ 2) <
        4 * (A ^ 2 - B ^ 2) * (A ^ 2 + B ^ 2) := by
    by_cases hnum3 : 0 ≤ A ^ 2 - 3 * B ^ 2
    · rcases hnum3.eq_or_lt with hzero | hpos
      · rw [← hzero]
        have hright : 0 <
            4 * (A ^ 2 - B ^ 2) * (A ^ 2 + B ^ 2) := by positivity
        linarith
      · have hleft :=
          mul_lt_mul_of_pos_right hscale (mul_pos hA0 hpos)
        have hright := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4)
        nlinarith
    · have hneg : A ^ 2 - 3 * B ^ 2 < 0 := lt_of_not_ge hnum3
      have hright : 0 <
          4 * (A ^ 2 - B ^ 2) * (A ^ 2 + B ^ 2) := by positivity
      nlinarith
  field_simp
  nlinarith [hstep, sq_pos_of_pos hden]

theorem eightyFive_mul_re_xiShiftedReciprocalMoment_two_lt_four_mul_one :
    85 * (xiShiftedReciprocalMoment 1 2).re <
      4 * (xiShiftedReciprocalMoment 1 1).re := by
  have hsum2C :
      Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare 1 q ^ (1 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow (by norm_num) 1
  have hsum3C :
      Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare 1 q ^ (2 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow (by norm_num) 2
  have hsum2 : Summable (fun q : XiZeroCopy =>
      4 * (xiShiftedReciprocalSquare 1 q ^ 2).re) := by
    simpa using (Complex.reCLM.summable hsum2C).mul_left 4
  have hsum3 : Summable (fun q : XiZeroCopy =>
      85 * (xiShiftedReciprocalSquare 1 q ^ 3).re) := by
    simpa using (Complex.reCLM.summable hsum3C).mul_left 85
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  have hlt := hsum3.tsum_lt_tsum (i := q0)
    (fun q =>
      (eightyFive_mul_re_xiShiftedReciprocalSquare_cube_lt_four_mul_square q).le)
    (eightyFive_mul_re_xiShiftedReciprocalSquare_cube_lt_four_mul_square q0) hsum2
  change 85 * (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare 1 q ^ (2 + 1)).re <
    4 * (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare 1 q ^ (1 + 1)).re
  rw [Complex.re_tsum hsum3C, Complex.re_tsum hsum2C]
  simpa only [tsum_mul_left] using hlt

theorem deriv_xiRealLogDeriv_eq
    {w : ℝ} (hw : 0 < w) :
    deriv xiRealLogDeriv w =
      (xiShiftedReciprocalMoment (w ^ 2) 0).re -
        2 * w ^ 2 * (xiShiftedReciprocalMoment (w ^ 2) 1).re := by
  have hy : 0 < w ^ 2 := sq_pos_of_pos hw
  have hmoment :=
    hasDerivAt_re_xiShiftedReciprocalMoment hy 0
  have hpow : HasDerivAt (fun v : ℝ => v ^ 2) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  have hraw := hmoment.comp (h := fun v : ℝ => v ^ 2) w hpow
  have hrhs := (hasDerivAt_id w).mul hraw
  have heq : xiRealLogDeriv =ᶠ[nhds w]
      fun v : ℝ => v * (xiShiftedReciprocalMoment (v ^ 2) 0).re := by
    filter_upwards [Ioi_mem_nhds hw] with v hv
    exact xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment hv
  have hlhs := hasDerivAt_xiRealLogDeriv w
  have hu := hlhs.unique (hrhs.congr_of_eventuallyEq heq)
  rw [hlhs.deriv]
  convert hu using 1 <;> norm_num <;> ring

theorem deriv2_xiRealLogDeriv_one_eq :
    deriv (deriv xiRealLogDeriv) 1 =
      -6 * (xiShiftedReciprocalMoment 1 1).re +
        8 * (xiShiftedReciprocalMoment 1 2).re := by
  have hpow : HasDerivAt (fun w : ℝ => w ^ 2) 2 1 := by
    simpa using hasDerivAt_pow 2 (1 : ℝ)
  have hM0 :=
    (hasDerivAt_re_xiShiftedReciprocalMoment
      (y := (1 : ℝ) ^ 2) (by norm_num) 0).comp (1 : ℝ) hpow
  have hM1 :=
    (hasDerivAt_re_xiShiftedReciprocalMoment
      (y := (1 : ℝ) ^ 2) (by norm_num) 1).comp (1 : ℝ) hpow
  have hterm :=
    (((hasDerivAt_pow 2 (1 : ℝ)).mul hM1).const_mul (2 : ℝ))
  have hformula := hM0.sub hterm
  have hformulaEq :
      (fun w : ℝ =>
        (xiShiftedReciprocalMoment (w ^ 2) 0).re -
          2 * w ^ 2 * (xiShiftedReciprocalMoment (w ^ 2) 1).re) =ᶠ[nhds (1 : ℝ)]
      (((fun v : ℝ => (xiShiftedReciprocalMoment v 0).re) ∘ fun w : ℝ => w ^ 2) -
        fun y : ℝ =>
          2 * ((fun x : ℝ => x ^ 2) *
            (fun v : ℝ => (xiShiftedReciprocalMoment v 1).re) ∘
              fun w : ℝ => w ^ 2) y) := by
    filter_upwards [] with w
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    ring
  have hformula' := hformula.congr_of_eventuallyEq hformulaEq
  have heq : deriv xiRealLogDeriv =ᶠ[nhds (1 : ℝ)]
      fun w : ℝ =>
        (xiShiftedReciprocalMoment (w ^ 2) 0).re -
          2 * w ^ 2 * (xiShiftedReciprocalMoment (w ^ 2) 1).re := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with w hw
    exact deriv_xiRealLogDeriv_eq hw
  have hderiv := (hformula'.congr_of_eventuallyEq heq).deriv
  rw [hderiv]
  norm_num
  ring

theorem deriv_suzukiUpperCayleyInv {w : ℂ} (hw : w ≠ 1) :
    deriv GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w =
      2 * I / (1 - w) ^ 2 := by
  have hfun :
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv =
        GaloisForLFunctions.RHTower.herglotzOfCayley := by
    funext z
    rw [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv,
      GaloisForLFunctions.RHTower.herglotzOfCayley]
    ring
  rw [hfun,
    (GaloisForLFunctions.RHTower.hasDerivAt_herglotzOfCayley hw).deriv]

theorem iteratedDeriv_two_suzukiUpperCayleyInv :
    iteratedDeriv 2
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0 = 4 * I := by
  have hbase : HasDerivAt (fun w : ℂ => 1 - w) (-1) 0 := by
    simpa using! (hasDerivAt_const 0 (1 : ℂ)).sub (hasDerivAt_id 0)
  have hden := hbase.pow 2
  have hne : ((1 : ℂ) - 0) ^ 2 ≠ 0 := by norm_num
  have hrhs := ((hasDerivAt_const 0 (2 * I)).div hden hne)
  have heq : deriv GaloisForLFunctions.RHTower.suzukiUpperCayleyInv =ᶠ[nhds 0]
      fun w : ℂ => 2 * I / (1 - w) ^ 2 := by
    filter_upwards [eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)] with w hw
    exact deriv_suzukiUpperCayleyInv hw
  rw [show
    iteratedDeriv 2 GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0 =
      deriv (iteratedDeriv 1
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv) 0 by
      simpa using congrFun
        (iteratedDeriv_succ
          (n := 1)
          (f := GaloisForLFunctions.RHTower.suzukiUpperCayleyInv)) 0]
  simp only [iteratedDeriv_one]
  have hderiv := (hrhs.congr_of_eventuallyEq heq).deriv
  rw [hderiv]
  norm_num
  ring

theorem deriv_cayleyAtI {z : ℂ} (hz : z ≠ -I) :
    deriv (fun u : ℂ => (u - I) / (u + I)) z =
      2 * I / (z + I) ^ 2 := by
  have hne : z + I ≠ 0 := by
    intro h
    apply hz
    linear_combination h
  have hfun :
      (fun u : ℂ => (u - I) / (u + I)) =
        GaloisForLFunctions.RHTower.cayleyOfHerglotz := rfl
  rw [hfun,
    (GaloisForLFunctions.RHTower.hasDerivAt_cayleyOfHerglotz hne).deriv]

theorem cayleyAtI_deriv :
    deriv (fun z : ℂ => (z - I) / (z + I)) I = -I / 2 := by
  have hne : I ≠ -I := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  rw [deriv_cayleyAtI hne]
  field_simp [I_ne_zero]
  rw [Complex.I_sq]
  norm_num

theorem cayleyAtI_iteratedDeriv_two :
    iteratedDeriv 2 (fun z : ℂ => (z - I) / (z + I)) I = 1 / 2 := by
  have hbase : HasDerivAt (fun z : ℂ => z + I) 1 I :=
    (hasDerivAt_id I).add_const I
  have hden := hbase.pow 2
  have hne : (I + I) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hrhs := (hasDerivAt_const I (2 * I)).div hden hne
  have heq : deriv (fun z : ℂ => (z - I) / (z + I)) =ᶠ[nhds I]
      fun z : ℂ => 2 * I / (z + I) ^ 2 := by
    have hIne : I ≠ -I := by
      intro h
      have him := congrArg Complex.im h
      norm_num at him
    filter_upwards [eventually_ne_nhds hIne] with z hz
    exact deriv_cayleyAtI hz
  rw [show
    iteratedDeriv 2 (fun z : ℂ => (z - I) / (z + I)) I =
      deriv (iteratedDeriv 1
        (fun z : ℂ => (z - I) / (z + I))) I by
      simpa using congrFun
        (iteratedDeriv_succ
          (n := 1) (f := fun z : ℂ => (z - I) / (z + I))) I]
  simp only [iteratedDeriv_one]
  have hderiv := (hrhs.congr_of_eventuallyEq heq).deriv
  rw [hderiv]
  have hII : I + I = (2 : ℂ) * I := by ring
  rw [hII]
  field_simp [I_ne_zero]
  simp only [Pi.pow_apply]
  ring_nf
  rw [Complex.I_sq]
  norm_num

theorem iteratedDeriv_two_disk_cayley_comp
    {m : ℂ → ℂ}
    (hm : ContDiffAt ℂ 2 m I)
    (hmI : m I = I) :
    iteratedDeriv 2
      (fun w => (m (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w) - I) /
        (m (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w) + I)) 0 =
      2 * (deriv m I + I * iteratedDeriv 2 m I - deriv m I ^ 2) := by
  let cayleyAtI : ℂ → ℂ := fun z => (z - I) / (z + I)
  let upperInv := GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
  have hInvZero : upperInv 0 = I := by
    simp [upperInv, GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]
  have hInvCont : ContDiffAt ℂ 2 upperInv 0 := by
    change ContDiffAt ℂ 2 (fun w : ℂ => I * ((1 + w) / (1 - w))) 0
    fun_prop (disch := norm_num)
  have hmComp : ContDiffAt ℂ 2 (m ∘ upperInv) 0 := by
    have hm' : ContDiffAt ℂ 2 m (upperInv 0) := by
      rw [hInvZero]
      exact hm
    exact hm'.comp 0 hInvCont
  have hCayleyCont : ContDiffAt ℂ 2 cayleyAtI I := by
    dsimp only [cayleyAtI]
    fun_prop (disch := norm_num)
  have hmCompZero : (m ∘ upperInv) 0 = I := by
    simp only [Function.comp_apply, hInvZero, hmI]
  have hCayleyCont' : ContDiffAt ℂ 2 cayleyAtI ((m ∘ upperInv) 0) := by
    rw [hmCompZero]
    exact hCayleyCont
  have houter := iteratedDeriv_comp_two hCayleyCont' hmComp
  have hm' : ContDiffAt ℂ 2 m (upperInv 0) := by
    rw [hInvZero]
    exact hm
  have hinner := iteratedDeriv_comp_two hm' hInvCont
  have hinnerOne :
      deriv (m ∘ upperInv) 0 =
        deriv m (upperInv 0) * deriv upperInv 0 :=
    ((hm'.differentiableAt (by norm_num)).hasDerivAt.comp 0
      (hInvCont.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hInvDeriv : deriv upperInv 0 = 2 * I := by
    dsimp only [upperInv]
    convert deriv_suzukiUpperCayleyInv (w := 0) (by norm_num) using 1 <;>
      norm_num
  have hInvDeriv2 : iteratedDeriv 2 upperInv 0 = 4 * I := by
    dsimp only [upperInv]
    exact iteratedDeriv_two_suzukiUpperCayleyInv
  have hCayleyDeriv : deriv cayleyAtI I = -I / 2 := by
    exact cayleyAtI_deriv
  have hCayleyDeriv2 : iteratedDeriv 2 cayleyAtI I = 1 / 2 := by
    exact cayleyAtI_iteratedDeriv_two
  change iteratedDeriv 2 (cayleyAtI ∘ (m ∘ upperInv)) 0 = _
  rw [houter, Function.comp_apply, hInvZero, hmI, hCayleyDeriv2, hCayleyDeriv,
    hinnerOne, hinner, hInvZero, hInvDeriv, hInvDeriv2]
  ring_nf
  rw [Complex.I_sq]
  rw [show I ^ 3 = -I by rw [pow_succ, Complex.I_sq]; ring]
  ring

private theorem analyticAt_logDeriv_xi
    {sigma : ℂ} (hxi : xi sigma ≠ 0) :
    AnalyticAt ℂ (logDeriv xi) sigma := by
  change AnalyticAt ℂ (fun z => deriv xi z / xi z) sigma
  exact (xi_analyticOnNhd_univ sigma (Set.mem_univ sigma)).deriv.div
    (xi_analyticOnNhd_univ sigma (Set.mem_univ sigma)) hxi

theorem iteratedDeriv_two_logDeriv_xi_one_sub (sigma : ℂ) :
    iteratedDeriv 2 (logDeriv xi) (1 - sigma) =
      -iteratedDeriv 2 (logDeriv xi) sigma := by
  have hfun : (fun s : ℂ => logDeriv xi (1 - s)) = -(logDeriv xi) := by
    funext s
    exact logDeriv_xi_reciprocity s
  have hd := congrArg (fun f : ℂ → ℂ => iteratedDeriv 2 f sigma) hfun
  change iteratedDeriv 2 (fun s : ℂ => logDeriv xi (1 - s)) sigma =
    iteratedDeriv 2 (-(logDeriv xi)) sigma at hd
  rw [congrFun (iteratedDeriv_comp_const_sub 2 (logDeriv xi) 1) sigma,
    iteratedDeriv_neg] at hd
  norm_num at hd
  exact hd

theorem iteratedDeriv_two_logDeriv_XiC_I_eq :
    iteratedDeriv 2 (logDeriv XiC) I =
      I * iteratedDeriv 2 (logDeriv xi) (3 / 2 : ℂ) := by
  let affine : ℂ → ℂ := fun z => 1 / 2 + z * I
  have harg : affine I = -(1 / 2 : ℂ) := by
    dsimp only [affine]
    rw [I_mul_I]
    ring
  have hxi : xi (affine I) ≠ 0 := by
    rw [harg]
    have h := xi_ofReal_shift_ne_zero (-1)
    have hcoord : (1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) = -(1 / 2 : ℂ) := by
      norm_num
    rwa [hcoord] at h
  have hlog : ContDiffAt ℂ 2 (logDeriv xi) (affine I) :=
    (analyticAt_logDeriv_xi hxi).contDiffAt
  have haffine : ContDiffAt ℂ 2 affine I := by
    dsimp only [affine]
    fun_prop
  have hcomp := iteratedDeriv_comp_two hlog haffine
  have haffineDeriv : deriv affine I = I := by
    have h :=
      (((hasDerivAt_id I).mul_const I).const_add (1 / 2 : ℂ)).deriv
    simpa only [affine, id_eq, one_mul] using h
  have haffineDeriv2 : iteratedDeriv 2 affine I = 0 := by
    rw [show iteratedDeriv 2 affine I =
      deriv (iteratedDeriv 1 affine) I by
        simpa using congrFun
          (iteratedDeriv_succ (n := 1) (f := affine)) I]
    have hfirst : iteratedDeriv 1 affine = fun _ : ℂ => I := by
      funext z
      rw [iteratedDeriv_one]
      have h :=
        (((hasDerivAt_id z).mul_const I).const_add (1 / 2 : ℂ)).deriv
      simpa only [affine, id_eq, one_mul] using h
    rw [hfirst, deriv_const]
  have hfun : logDeriv XiC =
      fun z : ℂ => I * logDeriv xi (affine z) := by
    funext z
    exact logDeriv_XiC_eq_mul_I_logDeriv_xi z
  rw [hfun, iteratedDeriv_const_mul_field]
  change I * iteratedDeriv 2 ((logDeriv xi) ∘ affine) I = _
  rw [hcomp, haffineDeriv, haffineDeriv2, mul_zero, add_zero, harg]
  have href :=
    iteratedDeriv_two_logDeriv_xi_one_sub (3 / 2 : ℂ)
  norm_num at href
  rw [href]
  rw [Complex.I_sq]
  ring

theorem deriv2_xiRealLogDeriv_one_eq_re :
    deriv (deriv xiRealLogDeriv) 1 =
      (iteratedDeriv 2 (logDeriv xi) (3 / 2 : ℂ)).re := by
  have hxi : xi (3 / 2 : ℂ) ≠ 0 := by
    have h := xi_ofReal_shift_ne_zero 1
    norm_num at h ⊢
    exact h
  have houter : HasDerivAt (deriv (logDeriv xi))
      (deriv (deriv (logDeriv xi)) (3 / 2 : ℂ)) (3 / 2 : ℂ) :=
    (analyticAt_logDeriv_xi hxi).deriv.differentiableAt.hasDerivAt
  have haffine :
      HasDerivAt (fun z : ℂ => 1 / 2 + z) 1 (1 : ℂ) := by
    simpa using (hasDerivAt_id (1 : ℂ)).const_add (1 / 2 : ℂ)
  have houter' : HasDerivAt (deriv (logDeriv xi))
      (deriv (deriv (logDeriv xi)) (3 / 2 : ℂ))
      (1 / 2 + (1 : ℂ)) := by
    convert houter using 1 <;> norm_num
  have hcomp := houter'.comp (1 : ℂ) haffine
  rw [mul_one] at hcomp
  have hreal : HasDerivAt
      (fun w : ℝ => (deriv (logDeriv xi) (1 / 2 + (w : ℂ))).re)
      (deriv (deriv (logDeriv xi)) (3 / 2 : ℂ)).re 1 := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt
      (1 : ℝ) hcomp.comp_ofReal
  have heq : deriv xiRealLogDeriv =ᶠ[nhds (1 : ℝ)]
      fun w : ℝ => (deriv (logDeriv xi) (1 / 2 + (w : ℂ))).re := by
    filter_upwards [] with w
    exact (hasDerivAt_xiRealLogDeriv w).deriv
  have hderiv := (hreal.congr_of_eventuallyEq heq).deriv
  rw [hderiv]
  congr 1
  rw [show iteratedDeriv 2 (logDeriv xi) (3 / 2 : ℂ) =
      deriv (iteratedDeriv 1 (logDeriv xi)) (3 / 2 : ℂ) by
        simpa using congrFun
          (iteratedDeriv_succ (n := 1) (f := logDeriv xi)) (3 / 2 : ℂ),
    iteratedDeriv_one]

private theorem logDeriv_xi_conj (s : ℂ) :
    logDeriv xi ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (logDeriv xi s) := by
  have h := congrArg Neg.neg (seamFluxCochain_conj s)
  simpa only [seamFluxCochain, neg_neg, map_neg] using h

private theorem iteratedDeriv_two_logDeriv_xi_ofReal_im_eq_zero
    (sigma : ℝ) :
    (iteratedDeriv 2 (logDeriv xi) (sigma : ℂ)).im = 0 := by
  have hfun :
      (starRingEnd ℂ) ∘ (logDeriv xi) ∘ (starRingEnd ℂ) =
        logDeriv xi := by
    funext z
    simp only [Function.comp_apply]
    rw [logDeriv_xi_conj, Complex.conj_conj]
  have hd := iteratedDeriv_conj_conj (logDeriv xi) 2
  rw [hfun] at hd
  have hfix :
      iteratedDeriv 2 (logDeriv xi) (sigma : ℂ) =
        (starRingEnd ℂ)
          (iteratedDeriv 2 (logDeriv xi) (sigma : ℂ)) := by
    have hsigma : (starRingEnd ℂ) (sigma : ℂ) = (sigma : ℂ) := by simp
    simpa only [Function.comp_apply, hsigma] using
      congrFun hd (sigma : ℂ)
  have him := congrArg Complex.im hfix
  rw [Complex.conj_im] at him
  linarith

theorem iteratedDeriv_two_logDeriv_xi_threeHalves_eq_ofReal :
    iteratedDeriv 2 (logDeriv xi) (3 / 2 : ℂ) =
      ((deriv (deriv xiRealLogDeriv) 1 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [deriv2_xiRealLogDeriv_one_eq_re]
    simp
  · have him :=
      iteratedDeriv_two_logDeriv_xi_ofReal_im_eq_zero (3 / 2 : ℝ)
    norm_num at him ⊢
    exact him

theorem contDiffAt_xiHedenmalmDonoghueTarget_I :
    ContDiffAt ℂ 2 xiHedenmalmDonoghueTarget I := by
  have hXi : XiC I ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_nine_halves
    norm_num
  have hlog : AnalyticAt ℂ (logDeriv XiC) I := by
    change AnalyticAt ℂ (fun z => deriv XiC z / XiC z) I
    exact (XiC_analytic I (Set.mem_univ I)).deriv.div
      (XiC_analytic I (Set.mem_univ I)) hXi
  change ContDiffAt ℂ 2
    (fun z : ℂ => (-logDeriv XiC z) /
      (xiHedenmalmDonoghueScale : ℂ)) I
  have htarget : AnalyticAt ℂ
      (fun z : ℂ => (-logDeriv XiC z) /
        (xiHedenmalmDonoghueScale : ℂ)) I :=
    hlog.neg.div_const
  exact htarget.contDiffAt

theorem iteratedDeriv_two_xiHedenmalmDonoghueTarget_I_eq :
    iteratedDeriv 2 xiHedenmalmDonoghueTarget I =
      -I * (((deriv (deriv xiRealLogDeriv) 1) /
        xiHedenmalmDonoghueScale : ℝ) : ℂ) := by
  change iteratedDeriv 2
    (fun z : ℂ => (-logDeriv XiC z) /
      (xiHedenmalmDonoghueScale : ℂ)) I = _
  have hneg : (fun z : ℂ => -logDeriv XiC z) = -(logDeriv XiC) := rfl
  rw [iteratedDeriv_div_const, hneg, iteratedDeriv_neg,
    iteratedDeriv_two_logDeriv_XiC_I_eq,
    iteratedDeriv_two_logDeriv_xi_threeHalves_eq_ofReal]
  push_cast
  ring

theorem iteratedDeriv_two_xiHedenmalmLivsicTarget_disk_zero_eq :
    iteratedDeriv 2
      (xiHedenmalmLivsicTarget ∘
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv) 0 =
      ((2 * (deriv xiRealLogDeriv 1 / xiHedenmalmDonoghueScale +
          deriv (deriv xiRealLogDeriv) 1 / xiHedenmalmDonoghueScale -
          (deriv xiRealLogDeriv 1 / xiHedenmalmDonoghueScale) ^ 2) : ℝ) : ℂ) := by
  have h := iteratedDeriv_two_disk_cayley_comp
    contDiffAt_xiHedenmalmDonoghueTarget_I
    xiHedenmalmDonoghueTarget_I
  change iteratedDeriv 2
      (xiHedenmalmLivsicTarget ∘
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv) 0 = _ at h ⊢
  rw [h, deriv_xiHedenmalmDonoghueTarget_I_eq_ofReal,
    iteratedDeriv_two_xiHedenmalmDonoghueTarget_I_eq]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Source-only safe-Euler calibration of the second normalized Xi Livšic disk jet. -/
def primeArchSuzukiSecondDefectCalibration : ℝ :=
  8 * (2 * (primeArchShiftedReciprocalMoment 1 2).re /
      (primeArchShiftedReciprocalMoment 1 0).re -
    (primeArchShiftedReciprocalMoment 1 1).re /
      (primeArchShiftedReciprocalMoment 1 0).re -
    ((primeArchShiftedReciprocalMoment 1 1).re /
      (primeArchShiftedReciprocalMoment 1 0).re) ^ 2)

theorem eightyFive_mul_re_primeArchShiftedReciprocalMoment_two_lt_four_mul_one :
    85 * (primeArchShiftedReciprocalMoment 1 2).re <
      4 * (primeArchShiftedReciprocalMoment 1 1).re := by
  rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 2,
    ← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 1]
  exact
    eightyFive_mul_re_xiShiftedReciprocalMoment_two_lt_four_mul_one

theorem iteratedDeriv_two_xiHedenmalmLivsicTarget_disk_zero_eq_primeArch :
    iteratedDeriv 2
      (xiHedenmalmLivsicTarget ∘
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv) 0 =
      (primeArchSuzukiSecondDefectCalibration : ℂ) := by
  have hA : (primeArchShiftedReciprocalMoment 1 0).re ≠ 0 :=
    ne_of_gt re_primeArchShiftedReciprocalMoment_one_zero_pos
  rw [iteratedDeriv_two_xiHedenmalmLivsicTarget_disk_zero_eq,
    deriv_xiRealLogDeriv_one_eq,
    deriv2_xiRealLogDeriv_one_eq,
    xiHedenmalmDonoghueScale_eq_xiRealLogDeriv_one,
    xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment (by norm_num)]
  norm_num
  rw [xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 0,
    xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 1,
    xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 2]
  rw [primeArchSuzukiSecondDefectCalibration]
  push_cast
  field_simp [hA]
  ring

theorem primeArchSuzukiSecondDefectCalibration_neg :
    primeArchSuzukiSecondDefectCalibration < 0 := by
  let A := (primeArchShiftedReciprocalMoment 1 0).re
  let B := (primeArchShiftedReciprocalMoment 1 1).re
  let C := (primeArchShiftedReciprocalMoment 1 2).re
  have hA : 0 < A := by
    exact re_primeArchShiftedReciprocalMoment_one_zero_pos
  have hB : 0 < B := by
    exact re_primeArchShiftedReciprocalMoment_one_one_pos
  have h85 : 85 * C < 4 * B := by
    exact
      eightyFive_mul_re_primeArchShiftedReciprocalMoment_two_lt_four_mul_one
  have hCB : 2 * C < B := by
    nlinarith
  have hdiv : 2 * C / A < B / A :=
    div_lt_div_of_pos_right hCB hA
  have hsq : 0 ≤ (B / A) ^ 2 := sq_nonneg _
  rw [primeArchSuzukiSecondDefectCalibration]
  change 8 * (2 * C / A - B / A - (B / A) ^ 2) < 0
  nlinarith

/-- Real second normalized Xi Livšic disk jet. -/
def xiHedenmalmLivsicSecondDefectJet : ℝ :=
  (iteratedDeriv 2
    (xiHedenmalmLivsicTarget ∘
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv) 0).re

theorem xiHedenmalmLivsicSecondDefectJet_eq_primeArch :
    xiHedenmalmLivsicSecondDefectJet =
      primeArchSuzukiSecondDefectCalibration := by
  rw [xiHedenmalmLivsicSecondDefectJet,
    iteratedDeriv_two_xiHedenmalmLivsicTarget_disk_zero_eq_primeArch]
  simp

theorem xiHedenmalmLivsicSecondDefectJet_neg :
    xiHedenmalmLivsicSecondDefectJet < 0 := by
  rw [xiHedenmalmLivsicSecondDefectJet_eq_primeArch]
  exact primeArchSuzukiSecondDefectCalibration_neg

end

end RHTower

