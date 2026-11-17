import GaloisForLFunctions.HilbertMetric.Geometry.CompactifiedSupportSphere
import GaloisForLFunctions.HilbertMetric.Geometry.BonnetHeightCritical
import GaloisForLFunctions.HilbertMetric.Geometry.NorthSupportFrame

/-!
# Global support uniqueness and embedding

Compactness supplies a maximum of each linear height. The actual first
and second derivatives identify its parameter with its height direction.
This gives strict support inequalities and injectivity of the compactified
surface without an assumed global convexity theorem.
-/

open Filter Topology
namespace GaloisForLFunctions.HilbertMetric.Geometry.CompactSupportEmbedding
open Bottcher CompactifiedSupportSphere SphericalChartRecovery SchwartzRadius
open BonnetSupport BonnetSurface StereographicFrame
noncomputable section

/-- The maximum of a unit linear height has that same actual unit normal. -/
theorem normal_of_global_height_max (f : SchwartzMap (ℝ × ℝ) ℝ)
    (v : Sphere) (n : Ambient) (hn : ‖n‖ = 1)
    (hmax : ∀ w : Sphere, inner ℝ (sphereMap f (positiveScale f) w) n ≤
      inner ℝ (sphereMap f (positiveScale f) v) n) : (v : Ambient) = n := by
  by_cases hv : (v : Ambient) = northPole
  · have he : v = northChart 0 := by apply Subtype.ext; simpa [northChart] using hv
    have h (z : ℂ) : inner ℝ (SmoothSupportCompactification.north f (positiveScale f) z) n ≤
        inner ℝ (SmoothSupportCompactification.north f (positiveScale f) 0) n := by
      simpa only [he, sphereMap_northChart] using hmax (northChart z)
    have hx : IsLocalMax (fun t : ℝ => inner ℝ
        (SmoothSupportCompactification.north f (positiveScale f) (t : ℂ)) n) 0 :=
      Eventually.of_forall (fun t => h (t : ℂ))
    have hy : IsLocalMax (fun t : ℝ => inner ℝ
        (SmoothSupportCompactification.north f (positiveScale f) (t * Complex.I)) n) 0 := by
      apply Eventually.of_forall
      intro t
      simpa only [Complex.ofReal_zero, zero_mul] using h (t * Complex.I)
    exact hv.trans (NorthSupportFrame.normal_of_north_height_max f _ n hn hx hy).symm
  · let z := stereoFiniteChart v
    have hv2 : (v : Ambient) 2 ≠ 1 := fun h => hv ((third_eq_one_iff (norm_eq_one v)).mp h)
    have he : v = southChart z := by
      apply Subtype.ext
      exact (stereo_finiteChart (norm_eq_one v) hv2).symm
    have h (w : ℂ) : inner ℝ (SmoothSupportCompactification.south f (positiveScale f) w) n ≤
        inner ℝ (SmoothSupportCompactification.south f (positiveScale f) z) n := by
      simpa only [he, sphereMap_southChart] using hmax (southChart w)
    have hx : IsLocalMax (fun t : ℝ => inner ℝ
        (surface (support f (positiveScale f)) (t, z.im)) n) z.re := by
      apply Eventually.of_forall
      intro t
      simpa only [SmoothSupportCompactification.south] using
        h (Complex.mk t z.im)
    have hy : IsLocalMax (fun t : ℝ => inner ℝ
        (surface (support f (positiveScale f)) (z.re, t)) n) z.im := by
      apply Eventually.of_forall
      intro t
      simpa only [SmoothSupportCompactification.south] using
        h (Complex.mk z.re t)
    have hn' := BonnetHeightCritical.normal_of_height_max f (z.re, z.im) n hn hx hy
    have hv' : (v : Ambient) = normal (z.re, z.im) := by
      rw [he]
      rfl
    exact hv'.trans hn'.symm

/-- Every parameter is the global support point in its own normal direction. -/
theorem support_inequality (f : SchwartzMap (ℝ × ℝ) ℝ) (n v : Sphere) :
    inner ℝ (sphereMap f (positiveScale f) v) (n : Ambient) ≤
      inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient) := by
  have hc : Continuous (fun w : Sphere =>
      inner ℝ (sphereMap f (positiveScale f) w) (n : Ambient)) :=
    (sphereMap_continuous f _).inner continuous_const
  obtain ⟨w, _, hw⟩ := isCompact_univ.exists_isMaxOn
    (show (Set.univ : Set Sphere).Nonempty from ⟨n, Set.mem_univ n⟩) hc.continuousOn
  have he : w = n := Subtype.ext (normal_of_global_height_max f w n (norm_eq_one n)
    (fun q => hw (Set.mem_univ q)))
  simpa only [he, Set.mem_setOf_eq] using hw (Set.mem_univ v)

/-- Equality in a support inequality forces equality of the actual normal parameters. -/
theorem support_equality_iff (f : SchwartzMap (ℝ × ℝ) ℝ) (n v : Sphere) :
    inner ℝ (sphereMap f (positiveScale f) v) (n : Ambient) =
      inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient) ↔ v = n := by
  constructor
  · intro h
    apply Subtype.ext
    apply normal_of_global_height_max f v n (norm_eq_one n)
    intro w
    rw [h]
    exact support_inequality f n w
  · rintro rfl
    rfl

/-- Each tangent plane has exactly one point of contact with the compact surface. -/
theorem strict_support_inequality (f : SchwartzMap (ℝ × ℝ) ℝ) (n v : Sphere) (hv : v ≠ n) :
    inner ℝ (sphereMap f (positiveScale f) v) (n : Ambient) <
      inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient) :=
  lt_of_le_of_ne (support_inequality f n v) (fun h => hv ((support_equality_iff f n v).mp h))

/-- Positive radius gives global injectivity of the actual compactified parametrization. -/
theorem sphereMap_injective (f : SchwartzMap (ℝ × ℝ) ℝ) :
    Function.Injective (sphereMap f (positiveScale f)) := by
  intro v w h
  apply (support_equality_iff f w v).mp
  rw [h]

/-- The parametrization is a closed topological embedding of the actual unit sphere. -/
theorem sphereMap_isClosedEmbedding (f : SchwartzMap (ℝ × ℝ) ℝ) :
    IsClosedEmbedding (sphereMap f (positiveScale f)) :=
  (sphereMap_continuous f _).isClosedEmbedding (sphereMap_injective f)

#print axioms sphereMap_isClosedEmbedding
#print axioms normal_of_global_height_max
#print axioms support_inequality
#print axioms support_equality_iff
#print axioms strict_support_inequality
#print axioms sphereMap_injective
end
end GaloisForLFunctions.HilbertMetric.Geometry.CompactSupportEmbedding
