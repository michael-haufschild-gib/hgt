import GaloisForLFunctions.HilbertMetric.Geometry.SmoothSupportCompactification

/-!
# The support parametrization on the actual unit sphere

The two verified surface charts glue to a single continuous map from the
unit sphere in Euclidean three-space. Both chart identities hold exactly,
so the map has a compact image and its local differential geometry is
computed by the previously established surface formulas.
-/

open Filter Topology Metric
namespace GaloisForLFunctions.HilbertMetric.Geometry.CompactifiedSupportSphere
open Bottcher SphericalChartRecovery
noncomputable section
abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := {v : Ambient // v ∈ Metric.sphere (0 : Ambient) 1}

instance : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient) 1)

theorem norm_eq_one (v : Sphere) : ‖(v : Ambient)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using v.property

def southChart (z : ℂ) : Sphere :=
  ⟨stereo z, by simpa only [mem_sphere, dist_zero_right] using norm_stereo_eq_one z⟩

def northChart (z : ℂ) : Sphere :=
  ⟨stereoInvExtended z, by simpa only [mem_sphere, dist_zero_right] using norm_stereoInvExtended z⟩

/-- The compactified support surface, parametrized by its actual unit normal. -/
def sphereMap (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (v : Sphere) : Ambient :=
  if (v : Ambient) = northPole then northPole
  else SmoothSupportCompactification.south f ε (stereoFiniteChart v)

private theorem stereo_ne_northPole (z : ℂ) : stereo z ≠ northPole := by
  intro h
  have hc := congrArg (fun v : Ambient => v 2) h
  change (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) = 1 at hc
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := by positivity
  have he := (div_eq_iff hd).mp hc
  linarith only [he]

/-- The finite chart of the global map is exactly the actual support parametrization. -/
theorem sphereMap_southChart (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (z : ℂ) :
    sphereMap f ε (southChart z) = SmoothSupportCompactification.south f ε z := by
  change (if stereo z = northPole then northPole else
    SmoothSupportCompactification.south f ε (stereoFiniteChart (stereo z))) = _
  rw [if_neg (stereo_ne_northPole z), stereoFiniteChart_stereo]

/-- The north chart of the global map is exactly the smooth flat extension. -/
theorem sphereMap_northChart (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (z : ℂ) :
    sphereMap f ε (northChart z) = SmoothSupportCompactification.north f ε z := by
  by_cases hz : z = 0
  · subst z
    simp [sphereMap, northChart, SmoothSupportCompactification.north_zero]
  · have he : northChart z = southChart z⁻¹ := by
      apply Subtype.ext
      simpa only [northChart, southChart, inv_inv] using
        (stereo_eq_stereoInvExtended_inv (inv_ne_zero hz)).symm
    rw [he, sphereMap_southChart]
    exact SmoothSupportCompactification.chart_overlap f ε hz

private theorem sphereMap_eq_south (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ)
    (v : Sphere) (hv : (v : Ambient) 2 ≠ 1) :
    sphereMap f ε v = SmoothSupportCompactification.south f ε (stereoFiniteChart v) := by
  have hn : (v : Ambient) ≠ northPole := by
    intro h
    apply hv
    rw [h]
    simp [northPole]
  rw [sphereMap, if_neg hn]

private theorem sphereMap_eq_north (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ)
    (v : Sphere) (hv : (v : Ambient) 2 ≠ -1) :
    sphereMap f ε v = SmoothSupportCompactification.north f ε (stereoInvChart v) := by
  have he : northChart (stereoInvChart v) = v := by
    apply Subtype.ext
    exact stereoInvExtended_inverseChart (norm_eq_one v) hv
  exact (congrArg (sphereMap f ε) he).symm.trans (sphereMap_northChart f ε _)

/-- Smooth chart compatibility gives continuity on the actual compact sphere. -/
theorem sphereMap_continuous (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) :
    Continuous (sphereMap f ε) := by
  have hcoord : Continuous (fun v : Sphere => (v : Ambient) 2) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).comp continuous_subtype_val
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : (q : Ambient) = northPole
  · have hqn : (q : Ambient) 2 ≠ -1 := by rw [hq]; change (1 : ℝ) ≠ -1; norm_num
    have hc : ContinuousAt (fun v : Sphere =>
        SmoothSupportCompactification.north f ε (stereoInvChart v)) q :=
      (SmoothSupportCompactification.north_smooth f ε).continuous.continuousAt.comp
        ((stereoInvChart_continuousAt hqn).comp continuous_subtype_val.continuousAt)
    have he : sphereMap f ε =ᶠ[𝓝 q] (fun v =>
        SmoothSupportCompactification.north f ε (stereoInvChart v)) := by
      filter_upwards [(hcoord.tendsto q).eventually (eventually_ne_nhds hqn)] with v hv
      exact sphereMap_eq_north f ε v hv
    exact hc.congr he.symm
  · have hqn : (q : Ambient) 2 ≠ 1 := fun h => hq ((third_eq_one_iff (norm_eq_one q)).mp h)
    have hc : ContinuousAt (fun v : Sphere =>
        SmoothSupportCompactification.south f ε (stereoFiniteChart v)) q :=
      (SmoothSupportCompactification.south_smooth f ε).continuous.continuousAt.comp
        ((stereoFiniteChart_continuousAt hqn).comp continuous_subtype_val.continuousAt)
    have he : sphereMap f ε =ᶠ[𝓝 q] (fun v =>
        SmoothSupportCompactification.south f ε (stereoFiniteChart v)) := by
      filter_upwards [(hcoord.tendsto q).eventually (eventually_ne_nhds hqn)] with v hv
      exact sphereMap_eq_south f ε v hv
    exact hc.congr he.symm

/-- The compactified image is a genuine compact subset of Euclidean three-space. -/
theorem sphereMap_range_compact (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) :
    IsCompact (Set.range (sphereMap f ε)) := isCompact_range (sphereMap_continuous f ε)

#print axioms sphereMap_southChart
#print axioms sphereMap_northChart
#print axioms sphereMap_continuous
#print axioms sphereMap_range_compact
end
end GaloisForLFunctions.HilbertMetric.Geometry.CompactifiedSupportSphere
