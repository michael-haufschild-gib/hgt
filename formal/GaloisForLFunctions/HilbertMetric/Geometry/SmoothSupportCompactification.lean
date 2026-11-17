import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzSurfaceCorrection
import GaloisForLFunctions.HilbertMetric.Geometry.SphericalChartRecovery

/-!
# Smooth compactification of the actual support parametrization

The south surface is the support parametrization. The north surface is
the inverse-coordinate round sphere plus the flat inversion pullback of
its Schwartz displacement. These actual maps agree on the overlap and
have identical jets to the round sphere at the missing pole.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.SmoothSupportCompactification
open Bottcher BonnetSupport BonnetSurface StereographicFrame
open SchwartzInversion SchwartzSurfaceCorrection SphericalChartRecovery
noncomputable section

/-- The actual support surface in the finite complex chart. -/
def south (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (z : ℂ) :
    EuclideanSpace ℝ (Fin 3) := surface (support f ε) (z.re, z.im)

/-- Its extension in the chart centered at the missing pole. -/
def north (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (z : ℂ) :
    EuclideanSpace ℝ (Fin 3) :=
  stereoInvExtended z + kelvin (ε • complexDisplacement f) z

theorem south_smooth (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) : ContDiff ℝ ∞ (south f ε) :=
  (surface_smooth (support_smooth (f.smooth ⊤) ε)).comp Complex.equivRealProdCLM.contDiff

theorem north_smooth (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) : ContDiff ℝ ∞ (north f ε) :=
  stereoInvExtended_smooth.add (kelvin_contDiff _)

/-- The two actual surface parametrizations agree under the inversion transition. -/
theorem chart_overlap (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) {z : ℂ} (hz : z ≠ 0) :
    south f ε z⁻¹ = north f ε z := by
  rw [south, surface_displacement]
  change stereo z⁻¹ + ε • displacement f ((z⁻¹).re, (z⁻¹).im) = _
  have hn : stereo z⁻¹ = stereoInvExtended z := by
    simpa only [inv_inv] using stereo_eq_stereoInvExtended_inv (inv_ne_zero hz)
  rw [hn, north, kelvin_of_ne_zero _ hz]
  rfl

theorem north_zero (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) : north f ε 0 = northPole := by
  rw [north, kelvin_zero, add_zero, stereoInvExtended_zero]

/-- Every finite jet of the compactified surface agrees with the round sphere at the pole. -/
theorem north_jet_round (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (north f ε) 0 = iteratedFDeriv ℝ n stereoInvExtended 0 := by
  change iteratedFDeriv ℝ n (stereoInvExtended + kelvin (ε • complexDisplacement f)) 0 = _
  rw [iteratedFDeriv_add_apply
    ((stereoInvExtended_smooth.of_le (by exact_mod_cast le_top)).contDiffAt)
    (((kelvin_contDiff (ε • complexDisplacement f)).of_le (by exact_mod_cast le_top)).contDiffAt),
    kelvin_iteratedFDeriv_zero, add_zero]

/-- The first derivative equality holds as an equality of actual Fréchet derivatives. -/
theorem north_fderiv_round (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) :
    fderiv ℝ (north f ε) 0 = fderiv ℝ stereoInvExtended 0 := by
  change fderiv ℝ (stereoInvExtended + kelvin (ε • complexDisplacement f)) 0 = _
  have h := ((stereoInvExtended_smooth.differentiable (by simp) 0).hasFDerivAt).add
    (kelvin_hasFDerivAt_zero (ε • complexDisplacement f))
  simpa only [add_zero] using h.fderiv

#print axioms chart_overlap
#print axioms north_smooth
#print axioms north_jet_round
#print axioms north_fderiv_round
end
end GaloisForLFunctions.HilbertMetric.Geometry.SmoothSupportCompactification
