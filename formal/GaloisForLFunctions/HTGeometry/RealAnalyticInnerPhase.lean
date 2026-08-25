import GaloisForLFunctions.HTGeometry.HalfPlanePolePhase
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Monotone phase of a real-analytic inner function

A holomorphic contraction of the upper half-plane that extends analytically across the real axis
and has unimodular real boundary values admits a global differentiable boundary phase.  Its phase
rate is nonnegative, so the phase is monotone.  This is the phase-theoretic content of the
meromorphic-inner/Blaschke factor in the Makarov--Poltoratski regularization argument, without any
finiteness assumption on its zero set.
-/

open Complex Filter Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem hasDerivAt_nonpos_of_isLocalMaxOn_Ici
    {f : ℝ → ℝ} {f' y : ℝ}
    (hd : HasDerivAt f f' y) (hmax : IsLocalMaxOn f (Ici y) y) :
    f' ≤ 0 := by
  have htan : (1 : ℝ) ∈ posTangentConeAt (Ici y) y := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    have hinter : Ioi y ∩ Ici y = Ioi y := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ici]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.le⟩
    rw [hinter, closure_Ioi]
    exact self_mem_Ici
  have h := hmax.hasFDerivWithinAt_nonpos
    hd.hasFDerivAt.hasFDerivWithinAt htan
  simpa [hasDerivAt_iff_hasFDerivAt] using h

/-- Boundary phase rate `Im (conj θ · θ')` of an analytic unimodular function. -/
def realBoundaryPhaseRate (theta : ℂ → ℂ) (x : ℝ) : ℝ :=
  ((starRingEnd ℂ) (theta (x : ℂ)) * deriv theta (x : ℂ)).im

theorem continuous_realBoundaryPhaseRate
    {theta : ℂ → ℂ} (han : ∀ x : ℝ, AnalyticAt ℂ theta (x : ℂ)) :
    Continuous (realBoundaryPhaseRate theta) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply Complex.continuous_im.continuousAt.comp
  apply ContinuousAt.mul
  · exact Complex.continuous_conj.continuousAt.comp
      ((han x).continuousAt.comp Complex.continuous_ofReal.continuousAt)
  · exact (han x).deriv.continuousAt.comp Complex.continuous_ofReal.continuousAt

theorem realBoundaryPhaseRate_nonneg
    {theta : ℂ → ℂ}
    (han : ∀ x : ℝ, AnalyticAt ℂ theta (x : ℂ))
    (hunit : ∀ x : ℝ, ‖theta (x : ℂ)‖ = 1)
    (hcontract : ∀ z : ℂ, 0 < z.im → ‖theta z‖ ≤ 1)
    (x : ℝ) : 0 ≤ realBoundaryPhaseRate theta x := by
  let curve : ℝ → ℂ := fun y => theta ((x : ℂ) + (y : ℂ) * I)
  have hpath : HasDerivAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) I 0 := by
    simpa using ((hasDerivAt_id (x := 0)).ofReal_comp.mul_const I).const_add (x : ℂ)
  have hcurve : HasDerivAt curve (deriv theta (x : ℂ) * I) 0 := by
    have han0 : AnalyticAt ℂ theta ((x : ℂ) + ((0 : ℝ) : ℂ) * I) := by
      simpa using han x
    simpa [curve, Function.comp_def] using
      han0.differentiableAt.hasDerivAt.comp 0 hpath
  have hnorm : HasDerivAt (fun y => ‖curve y‖ ^ 2)
      (2 * inner ℝ (curve 0) (deriv theta (x : ℂ) * I)) 0 :=
    hcurve.norm_sq
  have hmax : IsLocalMaxOn (fun y => ‖curve y‖ ^ 2) (Ici 0) 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [mem_Ici] at hy
    rw [show curve 0 = theta (x : ℂ) by simp [curve], hunit x]
    simp only [one_pow]
    by_cases hy0 : y = 0
    · subst y
      simp [curve, hunit x]
    · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
      have him : 0 < ((x : ℂ) + (y : ℂ) * I).im := by simp [hypos]
      have hc := hcontract _ him
      nlinarith [norm_nonneg (theta ((x : ℂ) + (y : ℂ) * I))]
  have hderivNonpos := hasDerivAt_nonpos_of_isLocalMaxOn_Ici hnorm hmax
  change 0 ≤ ((starRingEnd ℂ) (theta (x : ℂ)) * deriv theta (x : ℂ)).im
  simp only [curve, ofReal_zero, zero_mul, add_zero] at hderivNonpos
  rw [show inner ℝ (theta (x : ℂ)) (deriv theta (x : ℂ) * I) =
      (theta (x : ℂ)).re * (deriv theta (x : ℂ) * I).re +
        (theta (x : ℂ)).im * (deriv theta (x : ℂ) * I).im by
      simp [Complex.mul_re]
      ring] at hderivNonpos
  simp only [mul_re, mul_im, I_re, I_im, mul_zero, mul_one, add_zero] at hderivNonpos
  rw [Complex.mul_im]
  simp only [conj_re, conj_im]
  linarith

/-- Global real boundary phase, normalized by the principal argument at the origin. -/
def realAnalyticInnerPhase (theta : ℂ → ℂ) (x : ℝ) : ℝ :=
  Complex.arg (theta 0) + ∫ t in (0 : ℝ)..x, realBoundaryPhaseRate theta t

theorem hasDerivAt_realAnalyticInnerPhase
    {theta : ℂ → ℂ} (han : ∀ x : ℝ, AnalyticAt ℂ theta (x : ℂ)) (x : ℝ) :
    HasDerivAt (realAnalyticInnerPhase theta) (realBoundaryPhaseRate theta x) x := by
  have hc := continuous_realBoundaryPhaseRate han
  have hi : IntervalIntegrable (realBoundaryPhaseRate theta) volume 0 x :=
    hc.intervalIntegrable 0 x
  have hm : StronglyMeasurableAtFilter (realBoundaryPhaseRate theta) (nhds x) volume :=
    hc.stronglyMeasurable.stronglyMeasurableAtFilter
  change HasDerivAt
    (fun y => Complex.arg (theta 0) +
      ∫ t in (0 : ℝ)..y, realBoundaryPhaseRate theta t)
    (realBoundaryPhaseRate theta x) x
  exact (intervalIntegral.integral_hasDerivAt_right hi hm hc.continuousAt).const_add
    (Complex.arg (theta 0))

theorem monotone_realAnalyticInnerPhase
    {theta : ℂ → ℂ}
    (han : ∀ x : ℝ, AnalyticAt ℂ theta (x : ℂ))
    (hunit : ∀ x : ℝ, ‖theta (x : ℂ)‖ = 1)
    (hcontract : ∀ z : ℂ, 0 < z.im → ‖theta z‖ ≤ 1) :
    Monotone (realAnalyticInnerPhase theta) := by
  apply monotone_of_deriv_nonneg
  · exact fun x => (hasDerivAt_realAnalyticInnerPhase han x).differentiableAt
  · intro x
    rw [(hasDerivAt_realAnalyticInnerPhase han x).deriv]
    exact realBoundaryPhaseRate_nonneg han hunit hcontract x

private theorem exp_arg_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp ((Complex.arg z : ℂ) * I) = z := by
  have hne : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  rw [Complex.exp_mul_I]
  apply Complex.ext
  · simp only [add_re, Complex.cos_ofReal_re, mul_re, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
    rw [Complex.cos_arg hne, hz]
    simp
  · simp only [add_im, Complex.cos_ofReal_im, mul_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, I_re, I_im, mul_one, mul_zero, zero_add]
    rw [Complex.sin_arg, hz]
    simp

theorem exp_realAnalyticInnerPhase
    {theta : ℂ → ℂ}
    (han : ∀ x : ℝ, AnalyticAt ℂ theta (x : ℂ))
    (hunit : ∀ x : ℝ, ‖theta (x : ℂ)‖ = 1)
    (x : ℝ) :
    Complex.exp ((realAnalyticInnerPhase theta x : ℂ) * I) = theta (x : ℂ) := by
  let q : ℝ → ℂ := fun y => Complex.exp ((realAnalyticInnerPhase theta y : ℂ) * I)
  have htheta (y : ℝ) : HasDerivAt (fun t : ℝ => theta (t : ℂ))
      (deriv theta (y : ℂ)) y := (han y).differentiableAt.hasDerivAt.comp_ofReal
  have hre (y : ℝ) :
      ((starRingEnd ℂ) (theta (y : ℂ)) * deriv theta (y : ℂ)).re = 0 := by
    have hn := (htheta y).norm_sq
    have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
    have heq : (fun t : ℝ => ‖theta (t : ℂ)‖ ^ 2) = fun _ => (1 : ℝ) := by
      funext t
      rw [hunit t]
      norm_num
    rw [heq] at hn
    have hz := hn.unique hconst
    rw [show inner ℝ (theta (y : ℂ)) (deriv theta (y : ℂ)) =
      (theta (y : ℂ)).re * (deriv theta (y : ℂ)).re +
        (theta (y : ℂ)).im * (deriv theta (y : ℂ)).im by
      simp [Complex.mul_re]
      ring] at hz
    simp only [conj_re, conj_im, mul_re, neg_mul, sub_neg_eq_add]
    linarith
  have hthetaODE (y : ℝ) : HasDerivAt (fun t : ℝ => theta (t : ℂ))
      (theta (y : ℂ) * ((realBoundaryPhaseRate theta y : ℂ) * I)) y := by
    have ha : (starRingEnd ℂ) (theta (y : ℂ)) * deriv theta (y : ℂ) =
        (realBoundaryPhaseRate theta y : ℂ) * I := by
      apply Complex.ext <;> simp [realBoundaryPhaseRate, hre y]
    have hderivEq : deriv theta (y : ℂ) =
        theta (y : ℂ) * ((realBoundaryPhaseRate theta y : ℂ) * I) := by
      calc
        deriv theta (y : ℂ) =
            theta (y : ℂ) * ((starRingEnd ℂ) (theta (y : ℂ)) *
              deriv theta (y : ℂ)) := by
          symm
          calc
            theta (y : ℂ) * ((starRingEnd ℂ) (theta (y : ℂ)) *
                deriv theta (y : ℂ)) =
                (theta (y : ℂ) * (starRingEnd ℂ) (theta (y : ℂ))) *
                  deriv theta (y : ℂ) := by ring
            _ = deriv theta (y : ℂ) := by
              rw [RCLike.mul_conj, hunit y]
              norm_num
        _ = theta (y : ℂ) * ((realBoundaryPhaseRate theta y : ℂ) * I) := by rw [ha]
    rw [← hderivEq]
    exact htheta y
  have hq (y : ℝ) : HasDerivAt q
      (q y * ((realBoundaryPhaseRate theta y : ℂ) * I)) y := by
    have hphase := (hasDerivAt_realAnalyticInnerPhase han y).ofReal_comp.mul_const I
    simpa [q] using hphase.cexp
  have hqne (y : ℝ) : q y ≠ 0 := Complex.exp_ne_zero _
  let ratio : ℝ → ℂ := fun y => theta (y : ℂ) / q y
  have hratio (y : ℝ) : HasDerivAt ratio 0 y := by
    have h := (hthetaODE y).div (hq y) (hqne y)
    change HasDerivAt ((fun t : ℝ => theta (t : ℂ)) / q) 0 y
    have hnum :
        theta (y : ℂ) * ((realBoundaryPhaseRate theta y : ℂ) * I) * q y -
          theta (y : ℂ) *
            (q y * ((realBoundaryPhaseRate theta y : ℂ) * I)) = 0 := by ring
    exact h.congr_deriv (by rw [hnum, zero_div])
  have hratioDiff : Differentiable ℝ ratio := fun y => (hratio y).differentiableAt
  have hratioDeriv : ∀ y : ℝ, deriv ratio y = 0 := fun y => (hratio y).deriv
  have hconst := is_const_of_deriv_eq_zero hratioDiff hratioDeriv x 0
  have hq0 : q 0 = theta 0 := by
    rw [show q 0 = Complex.exp ((Complex.arg (theta 0) : ℂ) * I) by
      simp [q, realAnalyticInnerPhase]]
    exact exp_arg_of_norm_eq_one (hunit 0)
  have htheta0ne : theta 0 ≠ 0 :=
    norm_ne_zero_iff.mp (by
      have h0 : ‖theta 0‖ = 1 := by simpa using hunit (0 : ℝ)
      rw [h0]
      norm_num)
  have hratio0 : ratio 0 = 1 := by simp [ratio, hq0, htheta0ne]
  have hratiox : ratio x = 1 := by rw [hconst, hratio0]
  change q x = theta (x : ℂ)
  change theta (x : ℂ) / q x = 1 at hratiox
  exact (div_eq_one_iff_eq (hqne x)).mp hratiox |>.symm

theorem exists_monotone_phase_of_realAnalytic_inner
    {theta : ℂ → ℂ}
    (han : ∀ x : ℝ, AnalyticAt ℂ theta (x : ℂ))
    (hunit : ∀ x : ℝ, ‖theta (x : ℂ)‖ = 1)
    (hcontract : ∀ z : ℂ, 0 < z.im → ‖theta z‖ ≤ 1) :
    ∃ alpha : ℝ → ℝ, Monotone alpha ∧
      ∀ x : ℝ, theta (x : ℂ) = Complex.exp ((alpha x : ℂ) * I) := by
  refine ⟨realAnalyticInnerPhase theta,
    monotone_realAnalyticInnerPhase han hunit hcontract, ?_⟩
  intro x
  exact (exp_realAnalyticInnerPhase han hunit x).symm

end

end GaloisForLFunctions.HTGeometry
