/-
# Busemann functions of geodesic rays (Lemma 3.1)

For a unit-speed geodesic ray `γ` in a metric space, the *Busemann function*
`b(x) = lim_{s→∞} (d(γ(s), x) - s)` exists: the family is nonincreasing in `s` and bounded
below.  `GeodesicRay.tendsto_busemann` records the limit, `GeodesicRay.busemann_lipschitz`
that `b` is 1-Lipschitz, and `GeodesicRay.busemann_convex` that `b` is geodesically convex on
an NPC space.  These are the assertions of Lemma 3.1 with metric content; the `C²`-regularity
assertion is Riemannian and is not used anywhere in the 1-Lipschitz theory, whose analytic
input is packaged instead by the `BusemannFlow` axioms.

`GeodesicRay.busemann_linear` identifies `b` in the Euclidean model of Section 5.1.1:
for `γ(t) = x₀ - t u` with `‖u‖ = 1` one gets `b(x) = ⟪u, x⟫ - ⟪u, x₀⟫`.
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.LinearBusemannFlow

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Filter Topology
open scoped RealInnerProductSpace

variable {X : Type*} [MetricSpace X]

/-- A unit-speed geodesic ray `[0, ∞) → X`. -/
structure GeodesicRay (X : Type*) [MetricSpace X] where
  /-- The underlying map. -/
  toFun : ℝ → X
  /-- Unit speed: distances along the ray are parameter differences. -/
  dist_eq (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : dist (toFun s) (toFun t) = |s - t|

namespace GeodesicRay

/-- The Busemann approximant, extended to all of `ℝ` by freezing at `s = 0`. -/
noncomputable def approx (γ : GeodesicRay X) (x : X) (s : ℝ) : ℝ :=
  dist (γ.toFun (max s 0)) x - max s 0

theorem approx_antitone (γ : GeodesicRay X) (x : X) : Antitone (γ.approx x) := by
  intro s t hst
  have hs : (0:ℝ) ≤ max s 0 := le_max_right _ _
  have ht : (0:ℝ) ≤ max t 0 := le_max_right _ _
  have hle : max s 0 ≤ max t 0 := max_le_max hst le_rfl
  have htri : dist (γ.toFun (max t 0)) x
      ≤ dist (γ.toFun (max t 0)) (γ.toFun (max s 0)) + dist (γ.toFun (max s 0)) x :=
    dist_triangle _ _ _
  rw [γ.dist_eq _ _ ht hs, abs_of_nonneg (by linarith)] at htri
  simp only [approx]
  linarith

theorem approx_bddBelow (γ : GeodesicRay X) (x : X) : BddBelow (Set.range (γ.approx x)) := by
  refine ⟨-dist (γ.toFun 0) x, ?_⟩
  rintro _ ⟨s, rfl⟩
  have hs : (0:ℝ) ≤ max s 0 := le_max_right _ _
  have htri : dist (γ.toFun (max s 0)) (γ.toFun 0)
      ≤ dist (γ.toFun (max s 0)) x + dist x (γ.toFun 0) := dist_triangle _ _ _
  rw [γ.dist_eq _ _ hs le_rfl, sub_zero, abs_of_nonneg hs, dist_comm x] at htri
  simp only [approx]
  linarith

/-- The Busemann function of a geodesic ray. -/
noncomputable def busemann (γ : GeodesicRay X) (x : X) : ℝ := ⨅ s : ℝ, γ.approx x s

theorem tendsto_approx (γ : GeodesicRay X) (x : X) :
    Tendsto (γ.approx x) atTop (𝓝 (γ.busemann x)) :=
  tendsto_atTop_ciInf (γ.approx_antitone x) (γ.approx_bddBelow x)

/-- **Existence of the Busemann limit.** -/
theorem tendsto_busemann (γ : GeodesicRay X) (x : X) :
    Tendsto (fun s : ℝ => dist (γ.toFun s) x - s) atTop (𝓝 (γ.busemann x)) := by
  refine (γ.tendsto_approx x).congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
  simp only [approx, max_eq_left hs]

/-- **Lemma 3.1, 1-Lipschitz part.** -/
theorem busemann_lipschitz (γ : GeodesicRay X) (x y : X) :
    |γ.busemann x - γ.busemann y| ≤ dist x y := by
  have key : ∀ z w : X, γ.busemann z ≤ γ.busemann w + dist z w := by
    intro z w
    refine le_of_tendsto_of_tendsto' (γ.tendsto_approx z)
      ((γ.tendsto_approx w).add_const (dist z w)) fun s => ?_
    have h := dist_triangle (γ.toFun (max s 0)) w z
    rw [dist_comm w z] at h
    simp only [approx]
    linarith
  have h1 := key x y
  have h2 := key y x
  rw [dist_comm y x] at h2
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

variable [NPCSpace X]

/-- **Lemma 3.1, convexity part.**  On an NPC space every Busemann function is geodesically
convex. -/
theorem busemann_convex (γ : GeodesicRay X) (x y : X) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    γ.busemann (NPCSpace.gd x y t) ≤ (1 - t) * γ.busemann x + t * γ.busemann y := by
  have hlim : Tendsto (fun s : ℝ => (1 - t) * γ.approx x s + t * γ.approx y s) atTop
      (𝓝 ((1 - t) * γ.busemann x + t * γ.busemann y)) :=
    ((γ.tendsto_approx x).const_mul (1 - t)).add ((γ.tendsto_approx y).const_mul t)
  refine le_of_tendsto_of_tendsto' (γ.tendsto_approx (NPCSpace.gd x y t)) hlim fun s => ?_
  have h := NPCSpace.dist_gd_le x y (γ.toFun (max s 0)) t ht₀ ht₁
  rw [dist_comm (NPCSpace.gd x y t), dist_comm x, dist_comm y] at h
  simp only [approx]
  linarith

end GeodesicRay

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean geodesic ray `γ(t) = x₀ - t u` for a unit vector `u`. -/
noncomputable def linearRay (u : E) (hu : ‖u‖ = 1) (x₀ : E) : GeodesicRay E where
  toFun t := x₀ - t • u
  dist_eq s t _ _ := by
    rw [dist_eq_norm]
    have h : x₀ - s • u - (x₀ - t • u) = (t - s) • u := by module
    rw [h, norm_smul, Real.norm_eq_abs, hu, mul_one, abs_sub_comm]

/-- **Section 5.1.1.**  In Euclidean space the Busemann function of `γ(t) = x₀ - t u` is the
linear functional `x ↦ ⟪u, x⟫`, normalised by `⟪u, x₀⟫`. -/
theorem busemann_linear (u : E) (hu : ‖u‖ = 1) (x₀ x : E) :
    (linearRay u hu x₀).busemann x = ⟪u, x⟫ - ⟪u, x₀⟫ := by
  have h1 := (linearRay u hu x₀).tendsto_busemann x
  have h2 := (linearBusemannFlow u hu).tendsto_fn x₀ x
  exact tendsto_nhds_unique h1 h2

end Euclidean

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
