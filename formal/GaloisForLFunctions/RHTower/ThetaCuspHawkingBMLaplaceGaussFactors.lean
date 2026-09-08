import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceParameters

/-! Actual analytic Gauss factors for independently varying BM Laplace frequency. -/

open Complex Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

def radialSeries (w chi : ℂ) (outer : Bool) : FormalMultilinearSeries ℂ ℂ ℂ :=
  if outer then outerSeries w chi else horizonSeries w chi

def gaussFactor (w chi : ℂ) (outer : Bool) (z : ℂ) : ℂ := (radialSeries w chi outer).sum z
def gaussFirst (w chi : ℂ) (outer : Bool) (z : ℂ) : ℂ :=
  ((radialSeries w chi outer).derivSeries.sum z) 1
def gaussSecond (w chi : ℂ) (outer : Bool) (z : ℂ) : ℂ :=
  (((radialSeries w chi outer).derivSeries.derivSeries.sum z) 1) 1

private theorem radialSeries_radius {w chi : ℂ} (h : Chamber w chi) (outer : Bool) :
    (radialSeries w chi outer).radius=1 := by
  cases outer
  · exact horizonSeries_radius h
  · exact outerSeries_radius h

/-- Both factors have their actual first and second derivatives in the entire
open radial disk, at every frequency of the independent chamber. -/
theorem gaussFactor_derivatives {w chi z : ℂ} (h : Chamber w chi) (outer : Bool) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (gaussFactor w chi outer) (gaussFirst w chi outer z) z ∧
    HasDerivAt (gaussFirst w chi outer) (gaussSecond w chi outer z) z := by
  let p := radialSeries w chi outer
  have hp : ‖z‖ₑ < p.radius := by rw [radialSeries_radius h]; exact hz
  constructor
  · exact (p.hasFDerivAt_sum hp).hasDerivAt
  · have hq := p.derivSeries.hasFDerivAt_sum (lt_of_lt_of_le hp p.radius_le_radius_derivSeries)
    simpa [gaussFirst,gaussSecond,p] using!
      (hq.clm_apply (hasFDerivAt_const (1:ℂ) z)).hasDerivAt

theorem gaussFactor_contDiffAt {w chi z : ℂ} (h : Chamber w chi) (outer : Bool)
    (hz : ‖z‖ₑ < 1) (m : WithTop ℕ∞) : ContDiffAt ℂ m (gaussFactor w chi outer) z := by
  let p := radialSeries w chi outer
  have hp : z ∈ Metric.eball 0 p.radius := by
    simp only [Metric.mem_eball,edist_zero_right]
    rw [radialSeries_radius h]
    exact hz
  exact (p.analyticOnNhd z hp).contDiffAt

@[simp] theorem gaussFactor_zero (w chi : ℂ) (outer : Bool) : gaussFactor w chi outer 0=1 := by
  cases outer <;> exact ordinaryHypergeometric_zero _ _ _

def gaussJet (w chi z v d dd : ℂ) : ℂ :=
  z*(1-z)*dd+(gaussC w-(gaussA w chi+gaussB w chi+1)*z)*d-gaussA w chi*gaussB w chi*v

/-- The horizon factor solves the original reduced Gauss equation at free frequency. -/
theorem horizonFactor_equation {w chi z : ℂ} (h : Chamber w chi) (hz : ‖z‖ₑ < 1) :
    gaussJet w chi z (gaussFactor w chi false z) (gaussFirst w chi false z)
      (gaussSecond w chi false z)=0 := by
  have hr : ‖z‖ₑ < (horizonSeries w chi).radius := by rw [horizonSeries_radius h]; exact hz
  exact ordinaryHypergeometric_standardGaussODE _ _ _ z
    (avoidsNegNat_of_re_pos (chamber_parameters h).2.2.1) hr

/-- The outer factor solves its transformed Gauss equation, with fixed
denominator 3/2 and the original independently varying numerator parameters. -/
theorem outerFactor_equation {w chi z : ℂ} (h : Chamber w chi) (hz : ‖z‖ₑ < 1) :
    z*(1-z)*gaussSecond w chi true z+
      (3/2-((gaussC w-gaussA w chi)+(gaussC w-gaussB w chi)+1)*z)*gaussFirst w chi true z-
      (gaussC w-gaussA w chi)*(gaussC w-gaussB w chi)*gaussFactor w chi true z=0 := by
  have hr : ‖z‖ₑ < (outerSeries w chi).radius := by rw [outerSeries_radius h]; exact hz
  exact ordinaryHypergeometric_standardGaussODE _ _ _ z
    (avoidsNegNat_of_re_pos (by norm_num : 0 < (3/2:ℂ).re)) hr

end
end RHTower.D4BMLaplaceRadial
