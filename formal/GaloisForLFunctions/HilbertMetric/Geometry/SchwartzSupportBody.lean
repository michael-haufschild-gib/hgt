import GaloisForLFunctions.HilbertMetric.Geometry.CompactSupportEmbedding
import Mathlib.Analysis.Convex.Strict

/-!
# The convex body defined by the actual support planes

The body is the intersection of all support half-spaces. Its
interior is exactly the set satisfying every inequality strictly: the
compact normal sphere turns pointwise slack into a uniform interior ball.
-/

open Set Filter Topology Metric
namespace GaloisForLFunctions.HilbertMetric.Geometry.SchwartzSupportBody
open CompactifiedSupportSphere CompactSupportEmbedding SchwartzRadius
noncomputable section

/-- The half-space body determined by the actual compactified support surface. -/
def body (f : SchwartzMap (ℝ × ℝ) ℝ) : Set Ambient :=
  {x | ∀ n : Sphere, inner ℝ x (n : Ambient) ≤
    inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient)}

theorem image_mem_body (f : SchwartzMap (ℝ × ℝ) ℝ) (v : Sphere) :
    sphereMap f (positiveScale f) v ∈ body f := fun n => support_inequality f n v

/-- The body is an actual closed convex intersection of Euclidean half-spaces. -/
theorem body_closed (f : SchwartzMap (ℝ × ℝ) ℝ) : IsClosed (body f) := by
  have he : body f = ⋂ n : Sphere, {x : Ambient | inner ℝ x (n : Ambient) ≤
      inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient)} := by ext x; simp [body]
  rw [he]
  exact isClosed_iInter (fun n => isClosed_le (continuous_id.inner continuous_const) continuous_const)

theorem body_convex (f : SchwartzMap (ℝ × ℝ) ℝ) : Convex ℝ (body f) := by
  intro x hx y hy a b ha hb hab n
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  have h₁ := mul_le_mul_of_nonneg_left (hx n) ha
  have h₂ := mul_le_mul_of_nonneg_left (hy n) hb
  nlinarith only [h₁, h₂, congrArg
    (fun t => t * inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient)) hab]

/-- Strict support slack on the compact normal sphere is equivalent to an interior point. -/
theorem mem_interior_body_iff (f : SchwartzMap (ℝ × ℝ) ℝ) (x : Ambient) :
    x ∈ interior (body f) ↔ ∀ n : Sphere, inner ℝ x (n : Ambient) <
      inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient) := by
  constructor
  · intro hx n
    obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    have hn := norm_eq_one n
    have hy : x + (δ / 2) • (n : Ambient) ∈ ball x δ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hn, mul_one,
        Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
      linarith only [hδ]
    have h := hb hy n
    have hnn : inner ℝ (n : Ambient) (n : Ambient) = 1 := by
      rw [real_inner_self_eq_norm_sq, hn]; norm_num
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial, hnn, mul_one] at h
    linarith only [h, hδ]
  · intro hx
    let gap : Sphere → ℝ := fun n => inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient) -
      inner ℝ x (n : Ambient)
    have hc : Continuous gap :=
      ((sphereMap_continuous f _).inner continuous_subtype_val).sub
        (continuous_const.inner continuous_subtype_val)
    obtain ⟨n, _, hn⟩ := isCompact_univ.exists_isMinOn
      (show (Set.univ : Set Sphere).Nonempty from ⟨northChart 0, mem_univ _⟩) hc.continuousOn
    have hg : 0 < gap n := sub_pos.mpr (hx n)
    apply mem_interior_iff_mem_nhds.mpr
    apply Metric.mem_nhds_iff.mpr
    refine ⟨gap n, hg, ?_⟩
    intro y hy m
    have hd : ‖y - x‖ < gap n := by simpa only [mem_ball, dist_eq_norm] using hy
    have hm : gap n ≤ gap m := hn (mem_univ m)
    have hi : inner ℝ (y - x) (m : Ambient) ≤ ‖y - x‖ := by
      simpa only [norm_eq_one, mul_one] using real_inner_le_norm (y - x) (m : Ambient)
    rw [inner_sub_left] at hi
    change gap n ≤ inner ℝ (sphereMap f (positiveScale f) m) (m : Ambient) -
      inner ℝ x (m : Ambient) at hm
    linarith only [hd, hm, hi]

/-- The support half-spaces cut out a compact body, not an unbounded convex region. -/
theorem body_compact (f : SchwartzMap (ℝ × ℝ) ℝ) : IsCompact (body f) := by
  obtain ⟨R, hR⟩ := (sphereMap_range_compact f (positiveScale f)).isBounded.subset_closedBall
    (0 : Ambient)
  apply (isCompact_closedBall (0 : Ambient) (|R| + 1)).of_isClosed_subset (body_closed f)
  intro x hx
  have hb : ‖x‖ ≤ |R| + 1 := by
    by_cases hx0 : x = 0
    · simp only [hx0, norm_zero]
      positivity
    · have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      let n : Sphere := ⟨‖x‖⁻¹ • x, by
        simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']⟩
      have he : inner ℝ x (n : Ambient) = ‖x‖ := by
        change inner ℝ x (‖x‖⁻¹ • x) = _
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp [hp.ne']
      have hh := hx n
      rw [he] at hh
      have hi : inner ℝ (sphereMap f (positiveScale f) n) (n : Ambient) ≤
          ‖sphereMap f (positiveScale f) n‖ := by
        simpa only [norm_eq_one, mul_one] using
          real_inner_le_norm (sphereMap f (positiveScale f) n) (n : Ambient)
      have hr : ‖sphereMap f (positiveScale f) n‖ ≤ R := by
        simpa only [mem_closedBall, dist_zero_right] using hR (mem_range_self n)
      exact (hh.trans (hi.trans hr)).trans (by linarith only [le_abs_self R])
  simpa only [mem_closedBall, dist_zero_right] using hb

/-- The midpoint of distinct support points lies in the actual Euclidean interior. -/
theorem midpoint_mem_interior (f : SchwartzMap (ℝ × ℝ) ℝ) (u v : Sphere) (huv : u ≠ v) :
    (1 / 2 : ℝ) • sphereMap f (positiveScale f) u +
      (1 / 2 : ℝ) • sphereMap f (positiveScale f) v ∈ interior (body f) := by
  apply (mem_interior_body_iff f _).mpr
  intro n
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  by_cases hu : u = n
  · have hv : v ≠ n := fun h => huv (hu.trans h.symm)
    have h₁ := support_inequality f n u
    have h₂ := strict_support_inequality f n v hv
    linarith only [h₁, h₂]
  · have h₁ := strict_support_inequality f n u hu
    have h₂ := support_inequality f n v
    linarith only [h₁, h₂]

/-- The support body has nonempty three-dimensional interior. -/
theorem body_interior_nonempty (f : SchwartzMap (ℝ × ℝ) ℝ) :
    (interior (body f)).Nonempty := by
  have hne : northChart 0 ≠ southChart 0 := by
    intro h
    have he := congrArg (fun v : Sphere => (v : Ambient) 2) h
    change (Bottcher.stereoInvExtended 0) 2 = (Bottcher.stereo 0) 2 at he
    rw [Bottcher.stereoInvExtended_zero] at he
    change (1 : ℝ) = (‖(0 : ℂ)‖ ^ 2 - 1) / (1 + ‖(0 : ℂ)‖ ^ 2) at he
    norm_num at he
  exact ⟨_, midpoint_mem_interior f (northChart 0) (southChart 0) hne⟩

#print axioms body_compact
#print axioms midpoint_mem_interior
#print axioms body_interior_nonempty
#print axioms body_closed
#print axioms body_convex
#print axioms mem_interior_body_iff
end
end GaloisForLFunctions.HilbertMetric.Geometry.SchwartzSupportBody
