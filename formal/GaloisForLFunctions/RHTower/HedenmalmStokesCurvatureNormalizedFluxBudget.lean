import GaloisForLFunctions.RHTower.HedenmalmStokesOrientedFirstTraceQuantizedJump
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.XiSquaredEulerRayFullResponse
import GaloisForLFunctions.RHTower.CCMCompletedPrimeGammaAccretivityCriterion

/-!
# Curvature-normalized first-trace flux and its sharp budget

P-G143 removes the universal first-trace residue.  The remaining completed flux still has a
zero-free functional-equation gauge:

`xi(s) -> exp(c (s - 1/2)^(2 : ℕ)) xi(s)`.

This multiplier preserves the Xi divisor and functional equation, but shifts the completed seam
flux by `-2 c (s - 1/2)`.  Therefore an uncalibrated sign of the raw completed flux cannot follow
from divisor and reflection data alone.

Subtracting the central slope removes this whole quadratic gauge exactly:

`N_F(s) = F(s) - (s - 1/2) F'(1/2)`.

The theta-cusp source fixes the discarded slope: it is the negative zeroth normalized
prime--Gamma moment and is strictly negative.  On the positive real Euler ray, `N_F` is not
dissipative: it is strictly positive.  Its exact positive value is the loss of the strictly
decreasing full squared-Euler response from radius zero.  It nevertheless stays strictly below
the central-curvature allowance `-(sigma - 1/2) F'(1/2)`.

The surviving Route P target is thus the complex-strip extension of this already true real-ray
budget.  Lean proves that this curvature-budget condition is exactly the P-G139 completed-source
dissipativity condition and hence exactly RH.  The reformulation is gauge invariant, source
calibrated, and isolates the missing transverse estimate; it does not prove that estimate.

No RH premise, numerical computation, or added axiom enters the unconditional results.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Quadratic functional-equation gauge -/

/-- Zero-free quadratic gauge centered at the functional-equation fixed point. -/
def hedenmalmQuadraticFEGauge (c : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((c : ℂ) * (s - 1 / 2) ^ (2 : ℕ))

/-- Xi multiplied by the centered quadratic zero-free gauge. -/
def hedenmalmQuadraticGaugedXi (c : ℝ) (s : ℂ) : ℂ :=
  hedenmalmQuadraticFEGauge c s * xi s

/-- Completed seam flux of the quadratically gauged Xi carrier. -/
def hedenmalmQuadraticGaugedSeamFlux (c : ℝ) (s : ℂ) : ℂ :=
  -logDeriv (hedenmalmQuadraticGaugedXi c) s

theorem hedenmalmQuadraticFEGauge_ne_zero (c : ℝ) (s : ℂ) :
    hedenmalmQuadraticFEGauge c s ≠ 0 :=
  Complex.exp_ne_zero _

/-- The quadratic gauge is fixed by functional-equation reflection. -/
@[simp] theorem hedenmalmQuadraticFEGauge_one_sub (c : ℝ) (s : ℂ) :
    hedenmalmQuadraticFEGauge c (1 - s) = hedenmalmQuadraticFEGauge c s := by
  rw [hedenmalmQuadraticFEGauge, hedenmalmQuadraticFEGauge]
  congr 1
  ring

/-- The gauged entire carrier retains the Xi functional equation. -/
theorem hedenmalmQuadraticGaugedXi_one_sub (c : ℝ) (s : ℂ) :
    hedenmalmQuadraticGaugedXi c (1 - s) = hedenmalmQuadraticGaugedXi c s := by
  rw [hedenmalmQuadraticGaugedXi, hedenmalmQuadraticGaugedXi,
    hedenmalmQuadraticFEGauge_one_sub, xi_one_sub]

/-- The zero-free gauge leaves the Xi zero set pointwise unchanged. -/
theorem hedenmalmQuadraticGaugedXi_eq_zero_iff (c : ℝ) (s : ℂ) :
    hedenmalmQuadraticGaugedXi c s = 0 ↔ xi s = 0 := by
  rw [hedenmalmQuadraticGaugedXi, mul_eq_zero]
  simp [hedenmalmQuadraticFEGauge_ne_zero]

theorem differentiableAt_hedenmalmQuadraticFEGauge (c : ℝ) (s : ℂ) :
    DifferentiableAt ℂ (hedenmalmQuadraticFEGauge c) s := by
  unfold hedenmalmQuadraticFEGauge
  fun_prop

/-- The logarithmic derivative of the quadratic gauge is its centered linear slope. -/
theorem logDeriv_hedenmalmQuadraticFEGauge (c : ℝ) (s : ℂ) :
    logDeriv (hedenmalmQuadraticFEGauge c) s =
      2 * (c : ℂ) * (s - 1 / 2) := by
  have hinner : HasDerivAt (fun z : ℂ => (c : ℂ) * (z - 1 / 2) ^ (2 : ℕ))
      (2 * (c : ℂ) * (s - 1 / 2)) s := by
    have hsub : HasDerivAt (fun z : ℂ => z - 1 / 2) 1 s := by
      convert! (hasDerivAt_id (𝕜 := ℂ) s).sub
        (hasDerivAt_const (x := s) (c := (1 / 2 : ℂ))) using 1 <;> ring
    have hsq : HasDerivAt ((fun z : ℂ => z - 1 / 2) ^ (2 : ℕ))
        (2 * (s - 1 / 2)) s := by
      exact (hsub.pow 2).congr_deriv (by norm_num)
    change HasDerivAt
      (fun z : ℂ => (c : ℂ) * (((fun w : ℂ => w - 1 / 2) ^ (2 : ℕ)) z))
      (2 * (c : ℂ) * (s - 1 / 2)) s
    exact (hsq.const_mul (c : ℂ)).congr_deriv (by ring)
  have hexp := hinner.cexp
  rw [logDeriv_apply]
  change deriv (fun z => Complex.exp ((c : ℂ) * (z - 1 / 2) ^ (2 : ℕ))) s /
      Complex.exp ((c : ℂ) * (s - 1 / 2) ^ (2 : ℕ)) = _
  rw [hexp.deriv]
  field_simp [Complex.exp_ne_zero]

/-- Away from the unchanged divisor, the raw completed flux shifts by an arbitrary centered
linear term. -/
theorem hedenmalmQuadraticGaugedSeamFlux_eq_shift
    (c : ℝ) {s : ℂ} (hxi : xi s ≠ 0) :
    hedenmalmQuadraticGaugedSeamFlux c s =
      seamFluxCochain s - 2 * (c : ℂ) * (s - 1 / 2) := by
  have hg := hedenmalmQuadraticFEGauge_ne_zero c s
  rw [hedenmalmQuadraticGaugedSeamFlux]
  change -logDeriv (fun z => hedenmalmQuadraticFEGauge c z * xi z) s = _
  rw [logDeriv_mul s hg hxi (differentiableAt_hedenmalmQuadraticFEGauge c s)
      xi_differentiable.differentiableAt,
    logDeriv_hedenmalmQuadraticFEGauge, seamFluxCochain]
  ring

theorem hedenmalmQuadraticGaugedSeamFlux_re_eq_shift
    (c : ℝ) {s : ℂ} (hxi : xi s ≠ 0) :
    (hedenmalmQuadraticGaugedSeamFlux c s).re =
      (seamFluxCochain s).re - 2 * c * (s.re - 1 / 2) := by
  rw [hedenmalmQuadraticGaugedSeamFlux_eq_shift c hxi]
  norm_num [Complex.sub_re, Complex.mul_re]

/-- At every noncentral zero-free point, a real quadratic gauge can prescribe an arbitrary real
part of the raw completed flux. -/
theorem exists_quadraticGauge_gaugedSeamFlux_re_eq
    {s : ℂ} (hxi : xi s ≠ 0) (hoff : s.re ≠ 1 / 2) (y : ℝ) :
    ∃ c : ℝ, (hedenmalmQuadraticGaugedSeamFlux c s).re = y := by
  refine ⟨((seamFluxCochain s).re - y) / (2 * (s.re - 1 / 2)), ?_⟩
  rw [hedenmalmQuadraticGaugedSeamFlux_re_eq_shift _ hxi]
  have hx : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hoff
  have hden : 2 * (s.re - 1 / 2) ≠ 0 := mul_ne_zero (by norm_num) hx
  rw [show 2 * (((seamFluxCochain s).re - y) /
      (2 * (s.re - 1 / 2))) * (s.re - 1 / 2) =
      (((seamFluxCochain s).re - y) / (2 * (s.re - 1 / 2))) *
        (2 * (s.re - 1 / 2)) by ring,
    div_mul_cancel₀ _ hden]
  ring

/-! ## Curvature normalization -/

/-- Remove the central linear jet of any completed flux. -/
def hedenmalmCurvatureNormalizedFlux (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  F s - (s - 1 / 2) * deriv F (1 / 2)

/-- Curvature-normalized canonical Xi seam flux. -/
def hedenmalmCurvatureNormalizedSeamFlux (s : ℂ) : ℂ :=
  hedenmalmCurvatureNormalizedFlux seamFluxCochain s

/-- Curvature-normalized flux of a quadratically gauged Xi carrier. -/
def hedenmalmCurvatureNormalizedGaugedSeamFlux (c : ℝ) (s : ℂ) : ℂ :=
  hedenmalmCurvatureNormalizedFlux (hedenmalmQuadraticGaugedSeamFlux c) s

lemma xi_one_half_ne_zero : xi (1 / 2 : ℂ) ≠ 0 := by
  simpa using xi_ofReal_shift_ne_zero 0

lemma analyticAt_seamFluxCochain_one_half :
    AnalyticAt ℂ seamFluxCochain (1 / 2 : ℂ) := by
  have hxi : AnalyticAt ℂ xi (1 / 2 : ℂ) :=
    xi_analyticOnNhd_univ _ (Set.mem_univ _)
  change AnalyticAt ℂ (fun z => -logDeriv xi z) (1 / 2 : ℂ)
  rw [show logDeriv xi = fun z => deriv xi z / xi z by rfl]
  exact (hxi.deriv.div hxi xi_one_half_ne_zero).neg

/-- Quadratic gauge shifts the central flux slope by exactly `-2c`. -/
theorem deriv_hedenmalmQuadraticGaugedSeamFlux_one_half (c : ℝ) :
    deriv (hedenmalmQuadraticGaugedSeamFlux c) (1 / 2) =
      deriv seamFluxCochain (1 / 2) - 2 * (c : ℂ) := by
  have hxi : ∀ᶠ s in nhds (1 / 2 : ℂ), xi s ≠ 0 :=
    (xi_analyticOnNhd_univ _ (Set.mem_univ _)).continuousAt.eventually_ne
      xi_one_half_ne_zero
  have heq : hedenmalmQuadraticGaugedSeamFlux c =ᶠ[nhds (1 / 2 : ℂ)]
      fun s => seamFluxCochain s - 2 * (c : ℂ) * (s - 1 / 2) := by
    filter_upwards [hxi] with s hs
    exact hedenmalmQuadraticGaugedSeamFlux_eq_shift c hs
  rw [heq.deriv_eq]
  have hlin : HasDerivAt (fun s : ℂ => 2 * (c : ℂ) * (s - 1 / 2))
      (2 * (c : ℂ)) (1 / 2 : ℂ) := by
    convert! ((hasDerivAt_id (1 / 2 : ℂ)).sub_const (1 / 2 : ℂ)).const_mul
      (2 * (c : ℂ)) using 1 <;> ring
  change deriv (seamFluxCochain -
      fun s : ℂ => 2 * (c : ℂ) * (s - 1 / 2)) (1 / 2) = _
  exact (analyticAt_seamFluxCochain_one_half.differentiableAt.hasDerivAt.sub hlin).deriv

/-- **Quadratic-gauge survivor.** Central-slope subtraction makes the completed flux pointwise
invariant under every HD3 quadratic gauge, away from the common divisor. -/
theorem hedenmalmCurvatureNormalizedGaugedSeamFlux_eq
    (c : ℝ) {s : ℂ} (hxi : xi s ≠ 0) :
    hedenmalmCurvatureNormalizedGaugedSeamFlux c s =
      hedenmalmCurvatureNormalizedSeamFlux s := by
  rw [hedenmalmCurvatureNormalizedGaugedSeamFlux,
    hedenmalmCurvatureNormalizedSeamFlux, hedenmalmCurvatureNormalizedFlux,
    hedenmalmCurvatureNormalizedFlux,
    hedenmalmQuadraticGaugedSeamFlux_eq_shift c hxi,
    deriv_hedenmalmQuadraticGaugedSeamFlux_one_half]
  ring

/-- Curvature normalization retains functional-equation orientation. -/
@[simp] theorem hedenmalmCurvatureNormalizedSeamFlux_one_sub (s : ℂ) :
    hedenmalmCurvatureNormalizedSeamFlux (1 - s) =
      -hedenmalmCurvatureNormalizedSeamFlux s := by
  rw [hedenmalmCurvatureNormalizedSeamFlux, hedenmalmCurvatureNormalizedSeamFlux,
    hedenmalmCurvatureNormalizedFlux, hedenmalmCurvatureNormalizedFlux,
    seamFluxCochain_reciprocity]
  ring

/-! ## Theta-source calibration of the removed central slope -/

/-- The canonical seam slope is the negative zeroth normalized prime--Gamma source moment. -/
theorem deriv_seamFluxCochain_one_half_eq_neg_normalizedPrimeArchMoment_zero :
    deriv seamFluxCochain (1 / 2) = -(normalizedPrimeArchMoment 0 : ℂ) := by
  have hsourceDeriv :
      deriv continuedPrimeArchSourceRelativeTrace 0 = deriv (logDeriv XiC) 0 :=
    continuedPrimeArchSourceRelativeTrace_eventuallyEq_logDeriv_XiC.deriv_eq
  have hgerm : normalizedPrimeArchMomentGerm 0 =
      -deriv continuedPrimeArchSourceRelativeTrace 0 := by
    rw [normalizedPrimeArchMomentGerm, normalizedTraceMomentGerm, dslope_same]
  have hcoordFun : logDeriv XiC = fun z : ℂ =>
      I * logDeriv xi (1 / 2 + z * I) := by
    funext z
    exact logDeriv_XiC_eq_mul_I_logDeriv_xi z
  have houter : HasDerivAt (logDeriv xi)
      (deriv (logDeriv xi) (1 / 2)) (1 / 2 : ℂ) := by
    have hxi : AnalyticAt ℂ xi (1 / 2 : ℂ) :=
      xi_analyticOnNhd_univ _ (Set.mem_univ _)
    have hlog : AnalyticAt ℂ (logDeriv xi) (1 / 2 : ℂ) := by
      rw [show logDeriv xi = fun z => deriv xi z / xi z by rfl]
      exact hxi.deriv.div hxi xi_one_half_ne_zero
    exact hlog.differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun z : ℂ => 1 / 2 + z * I) I 0 := by
    convert! (hasDerivAt_const (x := (0 : ℂ)) (c := (1 / 2 : ℂ))).add
      ((hasDerivAt_id (0 : ℂ)).mul_const I) using 1 <;> ring
  have hcoordDeriv : deriv (logDeriv XiC) 0 =
      -deriv (logDeriv xi) (1 / 2) := by
    rw [hcoordFun]
    have houter0 : HasDerivAt (logDeriv xi)
        (deriv (logDeriv xi) (1 / 2)) (1 / 2 + 0 * I) := by
      simpa using houter
    have hcomp := (houter0.comp 0 hinner).const_mul I
    have htarget : HasDerivAt
        (fun z : ℂ => I * logDeriv xi (1 / 2 + z * I))
        (-deriv (logDeriv xi) (1 / 2)) 0 := by
      simpa only [Function.comp_apply] using hcomp.congr_deriv (by
        rw [show I * (deriv (logDeriv xi) (1 / 2) * I) =
          (I * I) * deriv (logDeriv xi) (1 / 2) by ring, I_mul_I]
        ring)
    exact htarget.deriv
  have hseamDeriv : deriv seamFluxCochain (1 / 2) =
      -deriv (logDeriv xi) (1 / 2) := by
    change deriv (fun z => -logDeriv xi z) (1 / 2) = _
    simpa using houter.neg.deriv
  rw [normalizedPrimeArchMomentGerm_zero] at hgerm
  calc
    deriv seamFluxCochain (1 / 2) =
        -deriv (logDeriv xi) (1 / 2) := hseamDeriv
    _ = deriv (logDeriv XiC) 0 := hcoordDeriv.symm
    _ = deriv continuedPrimeArchSourceRelativeTrace 0 := hsourceDeriv.symm
    _ = -(normalizedPrimeArchMoment 0 : ℂ) := by
      have hneg := congrArg Neg.neg hgerm
      simpa only [neg_neg] using hneg.symm

theorem deriv_seamFluxCochain_one_half_re_neg :
    (deriv seamFluxCochain (1 / 2)).re < 0 := by
  rw [deriv_seamFluxCochain_one_half_eq_neg_normalizedPrimeArchMoment_zero]
  simpa using neg_neg_of_pos normalizedPrimeArchMoment_zero_pos

theorem deriv_seamFluxCochain_one_half_im_eq_zero :
    (deriv seamFluxCochain (1 / 2)).im = 0 := by
  rw [deriv_seamFluxCochain_one_half_eq_neg_normalizedPrimeArchMoment_zero]
  simp

/-- Radius-zero full squared-Euler response is exactly the theta-normalized central curvature. -/
theorem xiSquaredEulerFullResponse_zero_eq_normalizedPrimeArchMoment_zero :
    xiSquaredEulerFullResponse 0 = normalizedPrimeArchMoment 0 := by
  have hsum := summable_xiZeroCopyReciprocalSquare
  have hmoment := primeArchSourceMoment_eq_xiCentralReciprocalMoment 0
  have hmomentRe := congrArg Complex.re hmoment
  rw [xiSquaredEulerFullResponse]
  calc
    (∑' q : XiZeroCopy, xiSquaredEulerOrbitResponse q 0) =
        ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).re := by
      apply tsum_congr
      intro q
      have h := xiReciprocalSquareResolventTerm_neg_mul_I_re_eq q 0
      simpa [xiReciprocalSquareResolventTerm] using h.symm
    _ = (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q).re :=
      (Complex.re_tsum hsum).symm
    _ = (xiCentralReciprocalMoment 0).re := by
      have h := congrArg Complex.re (tsum_xiZeroCopyReciprocalSquare_pow 0)
      simpa using h
    _ = normalizedPrimeArchMoment 0 := by
      simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using hmomentRe.symm

/-! ## Unconditional real-ray budget -/

/-- Exact real-ray value of the curvature-normalized remainder. -/
theorem hedenmalmCurvatureNormalizedSeamFlux_ofReal_eq_response_loss
    {x : ℝ} (hx : 0 < x) :
    (hedenmalmCurvatureNormalizedSeamFlux
        ((1 / 2 : ℂ) + (x : ℂ))).re =
      x * (xiSquaredEulerFullResponse 0 -
        xiSquaredEulerFullResponse (x ^ (2 : ℕ))) := by
  have hlog := xiSquaredEulerFullQ_eq_logDeriv_re hx
  have hseam :
      (seamFluxCochain ((1 / 2 : ℂ) + (x : ℂ))).re =
        -x * xiSquaredEulerFullResponse (x ^ (2 : ℕ)) := by
    rw [seamFluxCochain, Complex.neg_re]
    rw [← hlog]
    simp [xiSquaredEulerFullQ]
  rw [hedenmalmCurvatureNormalizedSeamFlux, hedenmalmCurvatureNormalizedFlux,
    Complex.sub_re, hseam,
    deriv_seamFluxCochain_one_half_eq_neg_normalizedPrimeArchMoment_zero,
    ← xiSquaredEulerFullResponse_zero_eq_normalizedPrimeArchMoment_zero]
  simp only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, zero_mul, mul_zero, sub_zero]
  ring

/-- **Sharp real-ray survivor.** The gauge-invariant finite remainder is strictly positive, but
strictly below the theta central-curvature allowance.  This kills naive normalized dissipativity
and proves the exact one-dimensional budget which the complex-strip producer must extend. -/
theorem hedenmalmCurvatureNormalizedSeamFlux_ofReal_strict_budget
    {x : ℝ} (hx : 0 < x) :
    0 < (hedenmalmCurvatureNormalizedSeamFlux
          ((1 / 2 : ℂ) + (x : ℂ))).re ∧
      (hedenmalmCurvatureNormalizedSeamFlux
          ((1 / 2 : ℂ) + (x : ℂ))).re <
        -x * (deriv seamFluxCochain (1 / 2)).re := by
  have hx2 : 0 < x ^ (2 : ℕ) := sq_pos_of_pos hx
  have hdrop := strictAntiOn_xiSquaredEulerFullResponse
    (show (0 : ℝ) ∈ Ici 0 by simp)
    (show x ^ (2 : ℕ) ∈ Ici 0 by simp [sq_nonneg]) hx2
  have hpos := xiSquaredEulerFullResponse_pos (sq_nonneg x)
  have hzero := xiSquaredEulerFullResponse_zero_eq_normalizedPrimeArchMoment_zero
  have hslope := deriv_seamFluxCochain_one_half_eq_neg_normalizedPrimeArchMoment_zero
  rw [hedenmalmCurvatureNormalizedSeamFlux_ofReal_eq_response_loss hx]
  constructor
  · exact mul_pos hx (sub_pos.mpr hdrop)
  · have hslopeRe := congrArg Complex.re hslope
    simp only [Complex.neg_re, Complex.ofReal_re] at hslopeRe
    rw [hslopeRe, ← hzero]
    nlinarith [mul_pos hx hpos]

/-! ## Gauge-invariant complex-strip budget and RH -/

/-- The missing transverse producer: the gauge-invariant finite remainder may spend at most the
fixed theta central-curvature allowance throughout the right half of the critical strip. -/
def HedenmalmCurvatureNormalizedRightBudget : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 →
    (hedenmalmCurvatureNormalizedSeamFlux s).re ≤
      -(s.re - 1 / 2) * (deriv seamFluxCochain (1 / 2)).re

/-- The calibrated curvature budget is algebraically the canonical raw completed-flux sign. -/
theorem hedenmalmCurvatureNormalizedRightBudget_iff_squarefreeFirstTraceRightDissipative :
    HedenmalmCurvatureNormalizedRightBudget ↔
      SquarefreeFirstTraceRightDissipative := by
  constructor
  · intro hbudget s hhalf hone hzeta
    have hB := hbudget s hhalf hone hzeta
    have him := deriv_seamFluxCochain_one_half_im_eq_zero
    have hflux :
        (squarefreeFirstTraceContinuedCurrent s +
          xiPrimeLogHigherValuation s - logDeriv archFactor s).re =
          (seamFluxCochain s).re := by
      rw [← completedPrimeGammaFlux_eq_firstTrace_add_regular]
      have hspos : 0 < s.re := lt_trans (by norm_num) hhalf
      have hs1 : s ≠ 1 := by
        intro hs
        rw [hs] at hone
        norm_num at hone
      rw [completedPrimeGammaFlux,
        ← seamFluxCochain_eq_continuedPrime_add_archimedean hspos hs1 hzeta]
    rw [hedenmalmCurvatureNormalizedSeamFlux,
      hedenmalmCurvatureNormalizedFlux] at hB
    simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hB
    rw [him, mul_zero, sub_zero] at hB
    norm_num at hB
    rw [hflux]
    linarith
  · intro hsource s hhalf hone hzeta
    have hraw := hsource s hhalf hone hzeta
    have him := deriv_seamFluxCochain_one_half_im_eq_zero
    have hflux :
        (squarefreeFirstTraceContinuedCurrent s +
          xiPrimeLogHigherValuation s - logDeriv archFactor s).re =
          (seamFluxCochain s).re := by
      rw [← completedPrimeGammaFlux_eq_firstTrace_add_regular]
      have hspos : 0 < s.re := lt_trans (by norm_num) hhalf
      have hs1 : s ≠ 1 := by
        intro hs
        rw [hs] at hone
        norm_num at hone
      rw [completedPrimeGammaFlux,
        ← seamFluxCochain_eq_continuedPrime_add_archimedean hspos hs1 hzeta]
    rw [hflux] at hraw
    rw [hedenmalmCurvatureNormalizedSeamFlux,
      hedenmalmCurvatureNormalizedFlux]
    simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    rw [him, mul_zero, sub_zero]
    norm_num
    linarith

/-- Under RH the P-G139 right completed-source sign follows from the exact left-half criterion and
functional-equation reflection. -/
theorem squarefreeFirstTraceRightDissipative_of_riemannHypothesis
    (hRH : RiemannHypothesis) : SquarefreeFirstTraceRightDissipative := by
  intro s hhalf hone hzeta
  let r : ℂ := 1 - s
  have hrpos : 0 < r.re := by
    dsimp only [r]
    change 0 < 1 - s.re
    linarith
  have hrhalf : r.re < 1 / 2 := by
    dsimp only [r]
    change 1 - s.re < 1 / 2
    linarith
  have hspos : 0 < s.re := lt_trans (by norm_num) hhalf
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at hone
    norm_num at hone
  have hxi : xi s ≠ 0 := (xi_eq_zero_iff hspos hs1).not.mpr hzeta
  have hxiR : xi r ≠ 0 := by
    dsimp only [r]
    rw [xi_one_sub]
    exact hxi
  have hr1 : r ≠ 1 := by
    intro hr
    have hre := congrArg Complex.re hr
    dsimp only [r] at hre
    norm_num only [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hzetaR : riemannZeta r ≠ 0 :=
    (xi_eq_zero_iff hrpos hr1).not.mp hxiR
  have hleft :=
    (completedPrimeGammaLeftHalfAccretive_iff_riemannHypothesis.mpr hRH)
      r hrpos hrhalf hzetaR
  have hreflect := completedPrimeGammaFlux_one_sub_eq_neg
    (s := s) ⟨hspos, hone⟩ hzeta hzetaR
  change completedPrimeGammaFlux r = -completedPrimeGammaFlux s at hreflect
  change 0 ≤ (completedPrimeGammaFlux r).re at hleft
  rw [hreflect] at hleft
  rw [← completedPrimeGammaFlux_eq_firstTrace_add_regular]
  simpa using hleft

theorem squarefreeFirstTraceRightDissipative_iff_riemannHypothesis :
    SquarefreeFirstTraceRightDissipative ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_squarefreeFirstTraceRightDissipative,
    squarefreeFirstTraceRightDissipative_of_riemannHypothesis⟩

/-- **P-G144 capstone.** The source-calibrated, quadratic-gauge-invariant curvature budget on the
right strip is exactly RH.  Its real-axis restriction is already strict and unconditional; the
open content is precisely transverse propagation of that budget. -/
theorem hedenmalmCurvatureNormalizedRightBudget_iff_riemannHypothesis :
    HedenmalmCurvatureNormalizedRightBudget ↔ RiemannHypothesis := by
  rw [hedenmalmCurvatureNormalizedRightBudget_iff_squarefreeFirstTraceRightDissipative,
    squarefreeFirstTraceRightDissipative_iff_riemannHypothesis]

end

end RHTower
