import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzSupportBody
import GaloisForLFunctions.HilbertMetric.Geometry.BonnetEnvelope

/-!
# Support contacts determine the convex boundary

An active support plane fixes its contact point by differentiating its
nonnegative support gap in both chart directions. Consequently every
boundary point of the support body lies on the actual parametrized surface.
-/

open Set Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.SupportBodyContact
open Bottcher CompactifiedSupportSphere SchwartzSupportBody SchwartzRadius
open BonnetSupport BonnetSurface BonnetEnvelope StereographicFrame SphericalChartRecovery
open SmoothSupportCompactification NorthSupportFrame
noncomputable section

private theorem northPole_inner : inner ℝ northPole northPole = 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  change (0 : ℝ) * 0 + 0 * 0 + 1 * 1 = 1
  norm_num

private theorem north_contact_unique (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (x : Ambient)
    (hbelow : ∀ z : ℂ, inner ℝ x (stereoInvExtended z) ≤
      inner ℝ (north f ε z) (stereoInvExtended z))
    (htouch : inner ℝ x northPole = 1) : x = northPole := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => north f ε (t : ℂ)) :=
    (north_smooth f ε).comp Complex.ofRealCLM.contDiff
  have ht : ContDiff ℝ ∞ (fun t : ℝ => north f ε ((t : ℂ) * Complex.I)) :=
    (north_smooth f ε).comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hns : ContDiff ℝ ∞ (fun t : ℝ => stereoInvExtended (t : ℂ)) :=
    stereoInvExtended_smooth.comp Complex.ofRealCLM.contDiff
  have hnt : ContDiff ℝ ∞ (fun t : ℝ => stereoInvExtended ((t : ℂ) * Complex.I)) :=
    stereoInvExtended_smooth.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hdx : HasDerivAt (fun t : ℝ => north f ε (t : ℂ)) !₂[2, 0, 0] 0 := by
    rw [← (north_partials f ε).1]
    exact (hs.differentiable (by simp) 0).hasDerivAt
  have hdy : HasDerivAt (fun t : ℝ => north f ε ((t : ℂ) * Complex.I)) !₂[0, -2, 0] 0 := by
    rw [← (north_partials f ε).2]
    exact (ht.differentiable (by simp) 0).hasDerivAt
  have hnx : HasDerivAt (fun t : ℝ => stereoInvExtended (t : ℂ)) !₂[2, 0, 0] 0 := by
    rw [← round_partials.1]
    exact (hns.differentiable (by simp) 0).hasDerivAt
  have hny : HasDerivAt (fun t : ℝ => stereoInvExtended ((t : ℂ) * Complex.I)) !₂[0, -2, 0] 0 := by
    rw [← round_partials.2]
    exact (hnt.differentiable (by simp) 0).hasDerivAt
  have hn1 : inner ℝ northPole northPole = 1 := northPole_inner
  have hx : IsLocalMin (fun t : ℝ =>
      inner ℝ (north f ε (t : ℂ)) (stereoInvExtended (t : ℂ)) -
      inner ℝ x (stereoInvExtended (t : ℂ))) 0 := by
    apply Eventually.of_forall
    intro t
    simp only [Complex.ofReal_zero, north_zero, stereoInvExtended_zero, hn1, htouch, sub_self]
    exact sub_nonneg.mpr (hbelow (t : ℂ))
  have hy : IsLocalMin (fun t : ℝ =>
      inner ℝ (north f ε ((t : ℂ) * Complex.I)) (stereoInvExtended ((t : ℂ) * Complex.I)) -
      inner ℝ x (stereoInvExtended ((t : ℂ) * Complex.I))) 0 := by
    apply Eventually.of_forall
    intro t
    simp only [Complex.ofReal_zero, zero_mul, north_zero, stereoInvExtended_zero,
      hn1, htouch, sub_self]
    exact sub_nonneg.mpr (hbelow ((t : ℂ) * Complex.I))
  have hex := hx.hasDerivAt_eq_zero ((hdx.inner ℝ hnx).sub ((hasDerivAt_const 0 x).inner ℝ hnx))
  have hey := hy.hasDerivAt_eq_zero ((hdy.inner ℝ hny).sub ((hasDerivAt_const 0 x).inner ℝ hny))
  simp [north_zero, northPole, PiLp.inner_apply, Fin.sum_univ_three] at hex hey
  have hx0 : x 0 = 0 := by linarith only [hex]
  have hx1 : x 1 = 0 := by linarith only [hey]
  have hx2 : x 2 = 1 := by
    simpa [northPole, PiLp.inner_apply, Fin.sum_univ_three] using htouch
  ext i
  fin_cases i <;> simp [northPole, hx0, hx1, hx2]

/-- Every active support plane meets the body at its unique actual surface point. -/
theorem active_constraint_unique (f : SchwartzMap (ℝ × ℝ) ℝ) (x : Ambient) (hx : x ∈ body f)
    (n : Sphere) (he : inner ℝ x (n : Ambient) =
      inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient)) :
    x = sphereMap f (positiveScale f) n := by
  by_cases hn : (n : Ambient) = northPole
  · have hn' : n = northChart 0 := by apply Subtype.ext; simpa [northChart] using hn
    have ht : inner ℝ x northPole = 1 := by
      rw [hn', sphereMap_northChart, north_zero] at he
      change inner ℝ x (stereoInvExtended 0) = inner ℝ northPole (stereoInvExtended 0) at he
      rw [stereoInvExtended_zero] at he
      rwa [northPole_inner] at he
    have hb (z : ℂ) : inner ℝ x (stereoInvExtended z) ≤
        inner ℝ (north f (positiveScale f) z) (stereoInvExtended z) := by
      have h := hx (northChart z)
      rw [sphereMap_northChart] at h
      exact h
    rw [hn', sphereMap_northChart, north_zero]
    exact north_contact_unique f _ x hb ht
  · let z := stereoFiniteChart n
    have hn2 : (n : Ambient) 2 ≠ 1 := fun h => hn ((third_eq_one_iff (norm_eq_one n)).mp h)
    have hn' : n = southChart z := by
      apply Subtype.ext
      exact (stereo_finiteChart (norm_eq_one n) hn2).symm
    let ρ := support f (positiveScale f)
    have hb (q : ℝ × ℝ) : inner ℝ x (normal q) ≤ ρ q := by
      have h := hx (southChart (Complex.mk q.1 q.2))
      rw [sphereMap_southChart] at h
      change inner ℝ x (normal q) ≤ inner ℝ (surface ρ q) (normal q) at h
      rwa [surface_support_height] at h
    have ht : inner ℝ x (normal (z.re, z.im)) = ρ (z.re, z.im) := by
      rw [hn', sphereMap_southChart] at he
      change inner ℝ x (normal (z.re, z.im)) =
        inner ℝ (surface ρ (z.re, z.im)) (normal (z.re, z.im)) at he
      rwa [surface_support_height] at he
    rw [hn', sphereMap_southChart]
    exact contact_point_unique (support_smooth (f.smooth ⊤) _) (z.re, z.im) x hb ht

/-- The convex body's boundary is exactly the actual compactified support surface. -/
theorem frontier_body_eq_range (f : SchwartzMap (ℝ × ℝ) ℝ) :
    frontier (body f) = Set.range (sphereMap f (positiveScale f)) := by
  ext x
  rw [(body_closed f).frontier_eq]
  constructor
  · rintro ⟨hx, hi⟩
    have hn : ∃ n : Sphere, inner ℝ x (n : Ambient) =
        inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient) := by
      by_contra h
      push Not at h
      apply hi
      apply (mem_interior_body_iff f x).mpr
      intro n
      exact lt_of_le_of_ne (hx n) (h n)
    obtain ⟨n, hn⟩ := hn
    exact ⟨n, (active_constraint_unique f x hx n hn).symm⟩
  · rintro ⟨n, rfl⟩
    refine ⟨image_mem_body f n, ?_⟩
    intro hi
    exact (lt_irrefl _ ((mem_interior_body_iff f _).mp hi n))

/-- No nontrivial segment lies in the boundary of the actual support body. -/
theorem body_strictConvex (f : SchwartzMap (ℝ × ℝ) ℝ) : StrictConvex ℝ (body f) := by
  intro x hx y hy hxy a b ha hb hab
  apply (mem_interior_body_iff f _).mpr
  intro n
  have hx' := hx n
  have hy' := hy n
  have hneq : inner ℝ x (n : Ambient) ≠ inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient) ∨
      inner ℝ y (n : Ambient) ≠ inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient) := by
    by_contra h
    push Not at h
    exact hxy ((active_constraint_unique f x hx n h.1).trans
      (active_constraint_unique f y hy n h.2).symm)
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  rcases hneq with h | h
  · have h₁ := mul_lt_mul_of_pos_left (lt_of_le_of_ne hx' h) ha
    have h₂ := mul_le_mul_of_nonneg_left hy' hb.le
    nlinarith only [h₁, h₂, congrArg
      (fun t => t * inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient)) hab]
  · have h₁ := mul_le_mul_of_nonneg_left hx' ha.le
    have h₂ := mul_lt_mul_of_pos_left (lt_of_le_of_ne hy' h) hb
    nlinarith only [h₁, h₂, congrArg
      (fun t => t * inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient)) hab]

#print axioms active_constraint_unique
#print axioms frontier_body_eq_range
#print axioms body_strictConvex
end
end GaloisForLFunctions.HilbertMetric.Geometry.SupportBodyContact
