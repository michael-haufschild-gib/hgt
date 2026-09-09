import GaloisForLFunctions.HTGeometry.HardyArcGluing
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Hardy boundary uniqueness on every open circle arc

The actual L² Cauchy transform extends through a vanishing arc and is zero
outside the disk. Analytic uniqueness then propagates that zero into the disk
and recovers every Hardy coefficient. No boundary continuity is assumed.
-/

open MeasureTheory Complex Filter Topology Metric Set
open scoped ENNReal NNReal lp
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem circle_radial_norm (t : ℝ) (ζ : Circle) : ‖(t : ℂ) * (ζ : ℂ)‖ = |t| := by
  simp [Complex.norm_real,Real.norm_eq_abs]

private theorem circle_radial_dist (t : ℝ) (ζ : Circle) :
    dist ((t : ℂ) * (ζ : ℂ)) (ζ : ℂ) = |t-1| := by
  rw [dist_eq]
  have he : (t : ℂ) * (ζ : ℂ) - (ζ : ℂ) = ((t-1 : ℝ) : ℂ) * (ζ : ℂ) := by
    push_cast
    ring
  rw [he,circle_radial_norm]

private theorem analytic_cauchy_on_gap (f : Lp ℂ 2 circleLebesgue) (ζ₀ : Circle) (r : ℝ)
    (hgap : ∀ᵐ ζ : Circle ∂circleLebesgue, dist (ζ : ℂ) (ζ₀ : ℂ) < r → f ζ = 0) :
    AnalyticOnNhd ℂ (circleHardyCauchyTransform f) (ball (ζ₀ : ℂ) r) := by
  apply (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).2
  intro z hz
  have hr : 0 < r - dist z (ζ₀ : ℂ) := sub_pos.mpr hz
  apply (differentiableAt_circleHardyCauchyTransform_of_ae_zero_near f z hr ?_).differentiableWithinAt
  filter_upwards [hgap] with ζ hζ
  intro hnear
  apply hζ
  have ht := dist_triangle (ζ : ℂ) z (ζ₀ : ℂ)
  linarith

private theorem hardy_eq_zero_of_arc (f : HardyDisk) (ζ₀ : Circle) (r : ℝ) (hr : 0 < r)
    (hgap : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) (ζ₀ : ℂ) < r → (hardyDiskBoundary f : Circle → ℂ) ζ = 0) : f = 0 := by
  let s : ℝ := min (r/2) (1/2)
  have hs : 0 < s := lt_min (by linarith) (by norm_num)
  have hsr : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let zout : ℂ := ((1+s : ℝ) : ℂ) * (ζ₀ : ℂ)
  let zin : ℂ := ((1-s : ℝ) : ℂ) * (ζ₀ : ℂ)
  have houtnorm : 1 < ‖zout‖ := by
    rw [show zout = ((1+s : ℝ) : ℂ) * (ζ₀ : ℂ) from rfl,circle_radial_norm,abs_of_pos (by linarith : 0 < 1+s)]
    linarith
  have houtball : zout ∈ ball (ζ₀ : ℂ) r := by
    change dist (((1+s : ℝ) : ℂ) * (ζ₀ : ℂ)) (ζ₀ : ℂ) < r
    rw [circle_radial_dist,show 1+s-1=s by ring,abs_of_pos hs]
    exact hsr
  have hinnorm : ‖zin‖ < 1 := by
    rw [show zin = ((1-s : ℝ) : ℂ) * (ζ₀ : ℂ) from rfl,circle_radial_norm,abs_of_pos (by linarith : 0 < 1-s)]
    linarith
  have hinball : zin ∈ ball (ζ₀ : ℂ) r := by
    change dist (((1-s : ℝ) : ℂ) * (ζ₀ : ℂ)) (ζ₀ : ℂ) < r
    rw [circle_radial_dist,show 1-s-1 = -s by ring,abs_neg,abs_of_pos hs]
    exact hsr
  let F := circleHardyCauchyTransform (hardyDiskBoundary f)
  have hFzero : F =ᶠ[𝓝 zout] 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds houtnorm] with z hz
    exact circleHardyCauchyTransform_hardyDiskBoundary_exterior f hz
  have hFball : EqOn F 0 (ball (ζ₀ : ℂ) r) :=
    (analytic_cauchy_on_gap (hardyDiskBoundary f) ζ₀ r hgap).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (ζ₀ : ℂ) r).isPreconnected houtball hFzero
  have hindisk : zin ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball,dist_zero_right] using hinnorm
  have hlocal : hardyFun f =ᶠ[𝓝 zin] 0 := by
    filter_upwards [isOpen_ball.mem_nhds hinball,isOpen_ball.mem_nhds hindisk] with z hgapz hdiskz
    exact (circleHardyCauchyTransform_hardyDiskBoundary f (by simpa only [mem_ball,dist_zero_right] using hdiskz)).symm.trans (hFball hgapz)
  have han : AnalyticOnNhd ℂ (hardyFun f) (ball (0 : ℂ) 1) :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).2 (differentiableOn_hardyFun f)
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected hindisk hlocal
  have hzero : hardyFun f =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    exact hall hz
  apply lp.ext
  funext n
  have hn := Filter.EventuallyEq.iteratedDeriv_eq n hzero
  rw [← diskCoeff_hardyFun f n,diskCoeff,hn]
  simp

/-- Vanishing almost everywhere on any positive open arc forces the whole actual Hardy vector to vanish. -/
theorem hardyDiskBoundary_arc_zero_iff (f : HardyDisk) (ζ₀ : Circle) (a : ℝ) :
    (∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) (ζ₀ : ℂ) < Real.exp a → (hardyDiskBoundary f : Circle → ℂ) ζ = 0) ↔ f = 0 := by
  constructor
  · exact hardy_eq_zero_of_arc f ζ₀ (Real.exp a) (Real.exp_pos a)
  · rintro rfl
    filter_upwards [Lp.coeFn_zero ℂ 2 circleLebesgue] with ζ hζ
    intro _
    simpa only [map_zero,Pi.zero_apply] using hζ

/-- The literal Hardy boundary restriction to an arbitrary positive circle arc determines the vector. -/
theorem hardyDiskBoundary_arc_eq_iff (f g : HardyDisk) (ζ₀ : Circle) (a : ℝ) :
    (∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) (ζ₀ : ℂ) < Real.exp a →
        (hardyDiskBoundary f : Circle → ℂ) ζ = (hardyDiskBoundary g : Circle → ℂ) ζ) ↔ f = g := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply (hardyDiskBoundary_arc_zero_iff (f-g) ζ₀ a).1
    have hs := Lp.coeFn_sub (hardyDiskBoundary f) (hardyDiskBoundary g)
    rw [← map_sub] at hs
    filter_upwards [h,hs] with ζ hζ hsζ
    intro hz
    rw [hsζ,Pi.sub_apply,hζ hz,sub_self]
  · rintro rfl
    exact Eventually.of_forall (fun _ _ => rfl)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
