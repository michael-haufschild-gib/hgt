import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinitySlope
import Mathlib.Topology.Order.LeftRightNhds

/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology


def slopeValue (h r t : ℝ) : ℝ :=
  (eval (sourcePoint (h:ℂ) (r:ℂ) (t:ℂ)) ThetaRatioSquare.slope).re

def regularSlopeValue (h r t : ℝ) : ℝ :=
  (eval (basePoint (h:ℂ) (r:ℂ) (t:ℂ)) scaledSlope).re

theorem regularSlopeValue_continuous (r t : ℝ) :
    Continuous (fun h : ℝ => regularSlopeValue h r t) := by
  have hb : Continuous (fun h : ℝ => basePoint (h:ℂ) (r:ℂ) (t:ℂ)) := by
    apply continuous_pi
    intro i
    cases i <;> simp only [basePoint] <;> fun_prop
  exact Complex.continuous_re.comp
    ((GaloisForLFunctions.HTGeometry.contDiff_mvPolynomial_eval scaledSlope).continuous.comp hb)

theorem principalMass_real :
    principalMass=(((6:ℝ)^24*1990656*1679616:ℝ):ℂ) := by
  simp [principalMass]

theorem regularSlopeValue_zero (r t : ℝ) :
    regularSlopeValue 0 r t=-648*((6:ℝ)^24*1990656*1679616)*(r-12*t) := by
  simp only [regularSlopeValue,Complex.ofReal_zero,scaledSlope_zero,principalMass_real]
  norm_cast

theorem regularSlopeValue_eq (h r t : ℝ) (hh : h≠0) :
    h^19*slopeValue h r t=regularSlopeValue h r t := by
  have he := congrArg Complex.re (scaledSlope_eq (h:ℂ) (r:ℂ) (t:ℂ)
    (Complex.ofReal_ne_zero.mpr hh))
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,slopeValue,regularSlopeValue] using he

/-- The expanding boundary mode determines the strict negative tail. -/
theorem slopeValue_eventually_neg (r t : ℝ) (he : 0<r-12*t) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), slopeValue h r t<0 := by
  have hzero : regularSlopeValue 0 r t<0 := by
    rw [regularSlopeValue_zero]
    have hc : 0<(648:ℝ)*((6:ℝ)^24*1990656*1679616) := by positivity
    nlinarith [mul_pos hc he]
  have hn := (regularSlopeValue_continuous r t).continuousAt.eventually_lt_const hzero
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with h hs hh
  have hp : 0<h^19 := pow_pos hh 19
  rw [← regularSlopeValue_eq h r t (ne_of_gt hh)] at hs
  nlinarith

/-- The opposite strict halfspace gives a positive tail, without a sign premise on the slope. -/
theorem slopeValue_eventually_pos (r t : ℝ) (he : r-12*t<0) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), 0<slopeValue h r t := by
  have hzero : 0<regularSlopeValue 0 r t := by
    rw [regularSlopeValue_zero]
    have hc : 0<(648:ℝ)*((6:ℝ)^24*1990656*1679616) := by positivity
    nlinarith [mul_pos hc (neg_pos.mpr he)]
  have hn := (regularSlopeValue_continuous r t).continuousAt.eventually_const_lt hzero
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with h hs hh
  have hp : 0<h^19 := pow_pos hh 19
  rw [← regularSlopeValue_eq h r t (ne_of_gt hh)] at hs
  nlinarith

end
end HTGeometry.ThetaRatioInfinity
