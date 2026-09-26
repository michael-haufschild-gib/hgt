import GaloisForLFunctions.RHTower.EtaTransitionReflectionDrift
import GaloisForLFunctions.RHTower.DigammaQuarter

set_option autoImplicit false

/-!
# A stationary height for the actual eta reflection multiplier

The central horizontal drift is positive at height zero and negative at
height `2*pi`.  Analyticity and the intermediate value theorem therefore
produce a stationary height strictly between them.  There are also
positive heights with positive drift, so the large-height orientation
cannot extend unchanged to all positive heights.
-/

namespace RiemannGaussian

open Complex RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry Set
open scoped ComplexConjugate

noncomputable section

def etaPrefactorHalfRadius : ℝ := exteriorEulerRadius (etaPrefactorLeftCoordinate 0)

theorem etaPrefactor_coordinates_zero :
    etaPrefactorRightCoordinate 0 = etaPrefactorLeftCoordinate 0 := by
  norm_num [etaPrefactorRightCoordinate, etaPrefactorLeftCoordinate, sigmoid]

theorem etaPrefactorHalfRadius_sq : etaPrefactorHalfRadius ^ 2 = 2 := by
  have h := etaPrefactor_radii_mul 0
  rw [etaPrefactor_coordinates_zero] at h
  simpa [etaPrefactorHalfRadius, pow_two] using h

theorem etaPrefactorHalfRadius_gt_one : 1 < etaPrefactorHalfRadius :=
  exteriorEulerRadius_gt_one _

theorem etaPrefactorHalfSpeed :
    exteriorEulerSpeed (etaPrefactorLeftCoordinate 0) 0 = etaPrefactorHalfRadius + 2 := by
  have hd := exteriorEulerDenom_pos (etaPrefactorLeftCoordinate 0) 0
  have hs := etaPrefactorHalfRadius_sq
  unfold exteriorEulerSpeed exteriorEulerDenom
  simp only [Real.cos_zero, mul_one]
  change (etaPrefactorHalfRadius ^ 2 - etaPrefactorHalfRadius) /
    (etaPrefactorHalfRadius ^ 2 - 2 * etaPrefactorHalfRadius + 1) = _
  rw [div_eq_iff (by simpa [exteriorEulerDenom, etaPrefactorHalfRadius] using hd.ne')]
  rw [hs]
  nlinarith

/-- The actual central horizontal logarithmic drift, as a function of
height. -/
def etaReflectionCenterDrift (b : ℝ) : ℝ :=
  (logDeriv etaElementaryReflectionMultiplier (etaReflectionStripPoint 0 b)).re

/-- Gauss's quarter-digamma value gives an exact endpoint formula. -/
theorem etaReflectionCenterDrift_zero :
    etaReflectionCenterDrift 0 =
      Real.log Real.pi + Real.eulerMascheroniConstant + Real.pi / 2 -
        (1 + 2 * etaPrefactorHalfRadius) * Real.log 2 := by
  unfold etaReflectionCenterDrift
  rw [re_logDeriv_etaElementaryReflectionMultiplier,
    pairedEtaFactorLogDerivative_logistic_left,
    pairedEtaFactorLogDerivative_logistic_right, re_logDeriv_zetaChi_strip,
    etaPrefactor_coordinates_zero]
  have hs : sigmoid 0 = 1 / 2 := by norm_num [sigmoid]
  norm_num [hs]
  rw [etaPrefactorHalfSpeed, GaloisForLFunctions.RHTower.digamma_quarter]
  simp only [neg_re, ofReal_re]
  ring

/-- Positivity follows from analytic logarithm bounds, not a numerical
evaluation of the drift. -/
theorem etaReflectionCenterDrift_zero_pos : 0 < etaReflectionCenterDrift 0 := by
  have hlog2 : Real.log 2 ≤ (3 : ℝ) / 4 := by
    have h := Real.log_div_le_sum_range_add (x := (1 : ℝ) / 3)
      (by norm_num) (by norm_num) 0
    norm_num at h
    linarith
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.sum_range_le_log_div (x := (1 : ℝ) / 2)
      (by norm_num) (by norm_num) 1
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlogpi : (1 : ℝ) < Real.log Real.pi :=
    lt_of_le_of_lt hlog3 (Real.log_lt_log (by norm_num) Real.pi_gt_three)
  have hr := etaPrefactorHalfRadius_gt_one
  have hs := etaPrefactorHalfRadius_sq
  have hrbound : etaPrefactorHalfRadius < 3 / 2 := by nlinarith
  have hlpos : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hbudget : (1 + 2 * etaPrefactorHalfRadius) * Real.log 2 ≤ 3 := by
    nlinarith
  rw [etaReflectionCenterDrift_zero]
  linarith [Real.one_half_lt_eulerMascheroniConstant, Real.pi_gt_three]

/-- The multiplier is analytic at every point of the open strip,
including all real heights. -/
theorem analyticAt_etaElementaryReflectionMultiplier (x b : ℝ) :
    AnalyticAt ℂ etaElementaryReflectionMultiplier (etaReflectionStripPoint x b) := by
  let s := etaReflectionStripPoint x b
  have hs : 0 < s.re := etaReflectionStripPoint_re_pos x b
  have ht : s.re < 1 := etaReflectionStripPoint_re_lt_one x b
  have hp : 0 < (1 - s).re := by simpa using sub_pos.mpr ht
  have hpt : (1 - s).re < 1 := by simp; linarith
  have hf : Differentiable ℂ pairedEtaFactor :=
    fun z => (hasDerivAt_pairedEtaFactor z).differentiableAt
  have hsub : AnalyticAt ℂ (fun z : ℂ => 1 - z) s :=
    analyticAt_const.sub analyticAt_id
  have hden : AnalyticAt ℂ (fun z : ℂ => pairedEtaFactor (1 - z)) s := by
    simpa [Function.comp] using! (hf.analyticAt (1 - s)).comp hsub
  exact ((hf.analyticAt s).mul
    (zetaChi_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos hp))).div hden
    (pairedEtaFactor_ne_zero_of_re_lt_one hpt)

/-- Continuity of the actual drift in both unrestricted strip
coordinates. -/
theorem continuous_etaReflectionStripDrift :
    Continuous (fun p : ℝ × ℝ =>
      (logDeriv etaElementaryReflectionMultiplier (etaReflectionStripPoint p.1 p.2)).re) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have ha := analyticAt_etaElementaryReflectionMultiplier p.1 p.2
  have hc : ContinuousAt (logDeriv etaElementaryReflectionMultiplier)
      (etaReflectionStripPoint p.1 p.2) :=
    ha.deriv.continuousAt.div ha.continuousAt (etaElementaryReflectionMultiplier_ne_zero p.1 p.2)
  have hs : Continuous sigmoid :=
    continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_sigmoid x).continuousAt)
  have hreal : ContinuousAt (fun z : ℂ => (logDeriv etaElementaryReflectionMultiplier z).re)
      (etaReflectionStripPoint p.1 p.2) :=
    Complex.continuous_re.continuousAt.comp hc
  have hpath : Continuous (fun q : ℝ × ℝ => etaReflectionStripPoint q.1 q.2) :=
    (Complex.continuous_ofReal.comp (hs.comp continuous_fst)).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  exact ContinuousAt.comp (f := fun q : ℝ × ℝ => etaReflectionStripPoint q.1 q.2)
    (x := p) hreal hpath.continuousAt

theorem continuous_etaReflectionCenterDrift : Continuous etaReflectionCenterDrift := by
  simpa [etaReflectionCenterDrift, Function.comp] using!
    continuous_etaReflectionStripDrift.comp (continuous_const.prodMk continuous_id)

theorem etaReflectionCenterDrift_two_pi_neg :
    etaReflectionCenterDrift (2 * Real.pi) < 0 := by
  have h := re_logDeriv_etaElementaryReflectionMultiplier_transition 0 0
  have hn : etaReflectionCenterDrift (2 * Real.pi) < -(1 / 36) := by
    simpa [etaReflectionCenterDrift, etaTransitionHeight] using h
  linarith

/-- The central multiplier has a genuine stationary height before
`2*pi`.  Only continuity and exact endpoint signs enter the proof. -/
theorem exists_etaReflectionCenterDrift_zero :
    ∃ b ∈ Ioo (0 : ℝ) (2 * Real.pi), etaReflectionCenterDrift b = 0 := by
  have hp := etaReflectionCenterDrift_zero_pos
  have hn := etaReflectionCenterDrift_two_pi_neg
  obtain ⟨b, hb, hz⟩ := intermediate_value_Icc' (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    continuous_etaReflectionCenterDrift.continuousOn ⟨hn.le, hp.le⟩
  refine ⟨b, ⟨?_, ?_⟩, hz⟩
  · by_contra h
    have heq : b = 0 := le_antisymm (le_of_not_gt h) hb.1
    rw [heq] at hz
    linarith
  · by_contra h
    have heq : b = 2 * Real.pi := le_antisymm hb.2 (le_of_not_gt h)
    rw [heq] at hz
    linarith

/-- Positive-height positive drift exists as well: the high-height
orientation is not a global orientation across all positive heights. -/
theorem exists_etaReflectionCenterDrift_pos :
    ∃ b ∈ Ioo (0 : ℝ) (2 * Real.pi), 0 < etaReflectionCenterDrift b := by
  have hp := etaReflectionCenterDrift_zero_pos
  have hn := etaReflectionCenterDrift_two_pi_neg
  obtain ⟨b, hb, hz⟩ := intermediate_value_Icc' (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    continuous_etaReflectionCenterDrift.continuousOn
    (show etaReflectionCenterDrift 0 / 2 ∈
      Icc (etaReflectionCenterDrift (2 * Real.pi)) (etaReflectionCenterDrift 0) by
      constructor <;> linarith)
  refine ⟨b, ⟨?_, ?_⟩, by rw [hz]; linarith⟩
  · by_contra h
    have heq : b = 0 := le_antisymm (le_of_not_gt h) hb.1
    rw [heq] at hz
    linarith
  · by_contra h
    have heq : b = 2 * Real.pi := le_antisymm hb.2 (le_of_not_gt h)
    rw [heq] at hz
    linarith

/-- Positive drift also occurs strictly left of the midline at a
strictly positive height.  Thus the large-height orientation cannot be
extended to the full domain claimed for it in the paper. -/
theorem exists_etaReflectionLeftStrip_positive_drift :
    ∃ b ∈ Ioo (0 : ℝ) (2 * Real.pi), sigmoid (-b) < 1 / 2 ∧
      0 < (logDeriv etaElementaryReflectionMultiplier (etaReflectionStripPoint (-b) b)).re := by
  let f : ℝ → ℝ := fun b =>
    (logDeriv etaElementaryReflectionMultiplier (etaReflectionStripPoint (-b) b)).re
  have hf : Continuous f := by
    simpa [f, Function.comp] using!
      continuous_etaReflectionStripDrift.comp (continuous_neg.prodMk continuous_id)
  have hp : 0 < f 0 := by
    simpa [f, etaReflectionCenterDrift] using etaReflectionCenterDrift_zero_pos
  have hn : f (2 * Real.pi) < 0 := by
    have h := re_logDeriv_etaElementaryReflectionMultiplier_transition (-2 * Real.pi) 0
    have hbound : f (2 * Real.pi) < -(1 / 36) := by
      simpa [f, etaTransitionHeight] using h
    linarith
  obtain ⟨b, hb, hz⟩ := intermediate_value_Icc' (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    hf.continuousOn (show f 0 / 2 ∈ Icc (f (2 * Real.pi)) (f 0) by
      constructor <;> linarith)
  have hleft : 0 < b := by
    by_contra h
    have heq : b = 0 := le_antisymm (le_of_not_gt h) hb.1
    rw [heq] at hz
    linarith
  have hright : b < 2 * Real.pi := by
    by_contra h
    have heq : b = 2 * Real.pi := le_antisymm hb.2 (le_of_not_gt h)
    rw [heq] at hz
    linarith
  refine ⟨b, ⟨hleft, hright⟩, ?_, ?_⟩
  · have h := sigmoid_strictMono (show -b < 0 by linarith)
    simpa only [show sigmoid 0 = 1 / 2 by norm_num [sigmoid]] using h
  · change 0 < f b
    rw [hz]
    linarith

/-- The stationary height is stationary for the literal horizontal
log-modulus derivative, not only for an auxiliary expression. -/
theorem exists_stationary_horizontal_eta_multiplier_height :
    ∃ b ∈ Ioo (0 : ℝ) (2 * Real.pi),
      deriv (fun σ : ℝ => Real.log ‖etaElementaryReflectionMultiplier
        ((σ : ℂ) + (b : ℂ) * I)‖) (1 / 2) = 0 := by
  obtain ⟨b, hb, hz⟩ := exists_etaReflectionCenterDrift_zero
  refine ⟨b, hb, ?_⟩
  have hd := deriv_log_norm_etaElementaryReflectionMultiplier 0 b
  have hs : sigmoid 0 = 1 / 2 := by norm_num [sigmoid]
  rw [hs] at hd
  rw [hd]
  exact hz

/-- A direct counterexample to an everywhere-negative horizontal
derivative on the paper's left half-strip. -/
theorem exists_positive_horizontal_eta_multiplier_left_derivative :
    ∃ b ∈ Ioo (0 : ℝ) (2 * Real.pi), sigmoid (-b) < 1 / 2 ∧
      0 < deriv (fun σ : ℝ => Real.log ‖etaElementaryReflectionMultiplier
        ((σ : ℂ) + (b : ℂ) * I)‖) (sigmoid (-b)) := by
  obtain ⟨b, hb, hs, hp⟩ := exists_etaReflectionLeftStrip_positive_drift
  refine ⟨b, hb, hs, ?_⟩
  rw [deriv_log_norm_etaElementaryReflectionMultiplier]
  exact hp

/-- Unit modulus along the entire midline forces the logarithmic
derivative there to be real. -/
theorem im_logDeriv_etaElementaryReflectionMultiplier_center (b : ℝ) :
    (logDeriv etaElementaryReflectionMultiplier (etaReflectionStripPoint 0 b)).im = 0 := by
  have hd := (differentiableAt_etaElementaryReflectionMultiplier 0 b).hasDerivAt
  have hp : HasDerivAt (fun t : ℝ => etaReflectionStripPoint 0 t) I b := by
    simpa [etaReflectionStripPoint] using
      ((Complex.ofRealCLM.hasDerivAt (x := b)).mul_const I).const_add (sigmoid 0 : ℂ)
  have hcomp : HasDerivAt (fun t : ℝ =>
      etaElementaryReflectionMultiplier (etaReflectionStripPoint 0 t))
      (deriv etaElementaryReflectionMultiplier (etaReflectionStripPoint 0 b) * I) b := by
    simpa using! hd.comp b hp
  have heq := (hasDerivAt_log_norm_comp hcomp
    (etaElementaryReflectionMultiplier_ne_zero 0 b)).deriv
  have hfun : (fun t : ℝ => Real.log ‖etaElementaryReflectionMultiplier
      (etaReflectionStripPoint 0 t)‖) = fun _ : ℝ => 0 := by
    funext t
    have hm : ‖etaElementaryReflectionMultiplier (etaReflectionStripPoint 0 t)‖ = 1 := by
      have hs : sigmoid 0 = 1 / 2 := by norm_num [sigmoid]
      simpa [etaReflectionStripPoint, hs] using norm_etaElementaryReflectionMultiplier_half t
    rw [hm, Real.log_one]
  rw [hfun, deriv_const] at heq
  have hquot : (deriv etaElementaryReflectionMultiplier (etaReflectionStripPoint 0 b) * I) /
      etaElementaryReflectionMultiplier (etaReflectionStripPoint 0 b) =
      I * logDeriv etaElementaryReflectionMultiplier (etaReflectionStripPoint 0 b) := by
    rw [logDeriv_apply]
    ring
  rw [hquot, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub] at heq
  linarith

/-- There is an actual complex critical point of the nonzero eta
reflection multiplier on the midline below height `2*pi`. -/
theorem exists_etaElementaryReflectionMultiplier_critical_point :
    ∃ b ∈ Ioo (0 : ℝ) (2 * Real.pi),
      deriv etaElementaryReflectionMultiplier ((1 / 2 : ℂ) + (b : ℂ) * I) = 0 := by
  obtain ⟨b, hb, hz⟩ := exists_etaReflectionCenterDrift_zero
  have hl : logDeriv etaElementaryReflectionMultiplier (etaReflectionStripPoint 0 b) = 0 := by
    apply Complex.ext
    · exact hz
    · exact im_logDeriv_etaElementaryReflectionMultiplier_center b
  rw [logDeriv_apply] at hl
  have hd := (div_eq_zero_iff.mp hl).resolve_right
    (etaElementaryReflectionMultiplier_ne_zero 0 b)
  refine ⟨b, hb, ?_⟩
  have hs : sigmoid 0 = 1 / 2 := by norm_num [sigmoid]
  simpa [etaReflectionStripPoint, hs] using hd

end

end RiemannGaussian
