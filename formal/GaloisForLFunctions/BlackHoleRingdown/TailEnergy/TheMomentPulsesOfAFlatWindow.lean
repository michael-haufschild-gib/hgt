import GaloisForLFunctions.BlackHoleRingdown.ThePulseAmplitude
import GaloisForLFunctions.RHTower.ExpDecayFourierAnalytic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Moment pulses of a flat compact window

Multiplying a compact pulse by powers of time separates every complex
frequency. For the explicit window exp(-1/(1-t²)) on |t|<1, a
polynomial times the time derivative returns a polynomial multiple of
the same window. This closes the frequency-moment recurrence.
-/

noncomputable section
open Complex MeasureTheory Set
namespace GaloisForLFunctions.BlackHoleRingdown

/-- The j-th time moment of a compact pulse, with the same support bound. -/
def momentPulse (h : CompactPulse) (j : ℕ) : CompactPulse where
  toFun t := (t:ℂ)^j*h t
  smooth := (Complex.ofRealCLM.contDiff.pow _).mul h.smooth
  compact := h.compact.mul_left

/-- At every complex frequency some time moment of any nonzero compact
pulse has nonzero amplitude. -/
theorem moment_pulses_separate_frequencies (h : CompactPulse) (hn : ∃ t : ℝ, h t ≠ 0) (w : ℂ) :
    ∃ j : ℕ, pulseAmplitude (momentPulse h j) w ≠ 0 := by
  by_contra! hall
  let g := fun t : ℝ => h t*Complex.exp (-(I*w*(t:ℂ)))
  have hc : Continuous g := h.continuous_toFun.mul (by fun_prop)
  have hk : HasCompactSupport g := h.compact.mul_right
  have hweight : _root_.RHTower.ExpWeightIntegrable g 1 := by
    intro a _
    exact ((hc.norm.mul (by fun_prop)).integrable_of_hasCompactSupport (hk.norm.mul_right))
  have mom (j : ℕ) : (∫ t : ℝ,g t*(t:ℂ)^j)=0 := by
    have H := hall j
    rw [pulseAmplitude] at H
    have hpi : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2*Real.pi:ℝ) ≠ 0)
    have hv := (mul_eq_zero.mp H).resolve_left (inv_ne_zero hpi)
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)) hv
    change (h t*Complex.exp _)*(t:ℂ)^j=((t:ℂ)^j*h t)*Complex.exp _
    ring
  have ae := _root_.RHTower.ae_eq_zero_of_moments_eq_zero' hc.aestronglyMeasurable zero_lt_one hweight mom
  obtain ⟨t,ht⟩ := hn
  have he := congrFun (MeasureTheory.eq_of_ae_eq ae hc continuous_const) t
  exact (mul_ne_zero ht (Complex.exp_ne_zero _)) he

/-- The real flat window on the unit interval about zero. -/
def flatWindow (t : ℝ) := expNegInvGlue (1-t^2)

/-- Smoothness of the compact window across both endpoints. -/
theorem flat_window_smooth : ContDiff ℝ ∞ flatWindow :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

private theorem flat_compact : HasCompactSupport flatWindow := by
  apply HasCompactSupport.intro (K:=Icc (-1:ℝ) 1) isCompact_Icc
  intro t ht
  apply expNegInvGlue.zero_of_nonpos
  have hh : t < -1 ∨ 1<t := by simpa [not_and_or,not_le] using ht
  rcases hh with hh|hh
  · nlinarith only [sq_nonneg (t+1),hh]
  · nlinarith only [sq_nonneg (t-1),hh]

/-- Explicit real-valued compact smooth input. -/
def flatPulse : CompactPulse where
  toFun t := (flatWindow t:ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp flat_window_smooth
  compact := flat_compact.comp_left (g:=fun x : ℝ => (x:ℂ)) (by simp)

theorem flat_pulse_zero_time : flatPulse 0 ≠ 0 := by
  change (flatWindow 0:ℂ) ≠ 0
  apply Complex.ofReal_ne_zero.mpr
  exact (expNegInvGlue.pos_of_pos (by norm_num : (0:ℝ)<1-0^2)).ne'

private theorem glue_derivative (x : ℝ) :
    HasDerivAt expNegInvGlue ((x⁻¹)^2*expNegInvGlue x) x := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1:ℝ[X]) x

/-- Polynomial differential equation, valid also at the flat endpoints. -/
theorem flat_window_differential (t : ℝ) :
    (1-t^2)^2*deriv flatWindow t = -(2*t)*flatWindow t := by
  have h := (glue_derivative (1-t^2)).comp t ((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2))
  change (1-t^2)^2 * deriv (fun x : ℝ => expNegInvGlue (1-x^2)) t = _
  rw [h.deriv]
  dsimp only [flatWindow]
  by_cases h0 : 1-t^2=0
  · simp [h0,expNegInvGlue.zero]
  · field_simp [h0]
    <;> ring

#print axioms moment_pulses_separate_frequencies
#print axioms flat_window_differential
end GaloisForLFunctions.BlackHoleRingdown
