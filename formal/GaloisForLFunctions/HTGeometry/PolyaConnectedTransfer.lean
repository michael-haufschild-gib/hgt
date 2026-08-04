import Mathlib

/-!
# Composition growth from connectivity alone

A ball is connected, so the modulus of a continuous function on it attains every value between the
modulus at the centre and the modulus at any other point.  Consequently, if the outer function has a
floor on some circle of intermediate radius, the composition attains that floor somewhere on the
ball.

Unlike the segment argument this needs no normalisation of the inner function at the origin, and
unlike the open-mapping argument it needs no lower bound on the displacement `g - g 0` — the two
mechanisms that were shown to cap out.  Only the intermediate value theorem on a connected set is
used.
-/

open Complex Metric Set

namespace GaloisForLFunctions.HTGeometry

/-- **Every intermediate modulus is attained.**  For a continuous `g` on a closed ball, every value
between `‖g 0‖` and `‖g z₁‖` is the modulus of `g` at some point of the ball. -/
theorem exists_norm_eq_of_closedBall {g : ℂ → ℂ} {s t : ℝ} {z₁ : ℂ}
    (hs : 0 ≤ s) (hg : ContinuousOn g (closedBall (0 : ℂ) s))
    (hz₁ : z₁ ∈ closedBall (0 : ℂ) s) (ht : t ∈ Set.Icc ‖g 0‖ ‖g z₁‖) :
    ∃ z ∈ closedBall (0 : ℂ) s, ‖g z‖ = t := by
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) s := by
    simpa [mem_closedBall] using hs
  have hconn : IsPreconnected (closedBall (0 : ℂ) s) :=
    (convex_closedBall (0 : ℂ) s).isPreconnected
  have hmem := hconn.intermediate_value h0 hz₁ hg.norm ht
  obtain ⟨z, hz, hzt⟩ := hmem
  exact ⟨z, hz, hzt⟩

/-- **A circle floor for the outer function transfers to the composition.**  If the outer function
is bounded below on the circle of an intermediate radius, the composition attains that bound
somewhere on the ball. -/
theorem exists_le_norm_comp_of_floor {f g : ℂ → ℂ} {s t c : ℝ} {z₁ : ℂ}
    (hs : 0 ≤ s) (hg : ContinuousOn g (closedBall (0 : ℂ) s))
    (hz₁ : z₁ ∈ closedBall (0 : ℂ) s) (ht : t ∈ Set.Icc ‖g 0‖ ‖g z₁‖)
    (hfloor : ∀ w : ℂ, ‖w‖ = t → c ≤ ‖f w‖) :
    ∃ z ∈ closedBall (0 : ℂ) s, c ≤ ‖f (g z)‖ := by
  obtain ⟨z, hz, hzt⟩ := exists_norm_eq_of_closedBall hs hg hz₁ ht
  exact ⟨z, hz, hfloor (g z) hzt⟩

/-- **Pointwise growth separation for a composition.**  If the outer function has a circle floor `L`
at an intermediate radius, the inner function is bounded by `Mg` on the ball, and `L` beats any
prescribed multiple of `Mg` logarithmically, then at some point of the ball the composition
outgrows that multiple of the inner state. -/
theorem exists_posLog_separation_of_closedBall {f g : ℂ → ℂ} {s t L Mg C : ℝ} {z₁ : ℂ}
    (hs : 0 ≤ s) (hg : ContinuousOn g (closedBall (0 : ℂ) s))
    (hz₁ : z₁ ∈ closedBall (0 : ℂ) s) (ht : t ∈ Set.Icc ‖g 0‖ ‖g z₁‖)
    (hL : ∀ w : ℂ, ‖w‖ = t → L ≤ ‖f w‖) (hL0 : 0 ≤ L)
    (hMg : ∀ z ∈ closedBall (0 : ℂ) s, ‖g z‖ ≤ Mg)
    (hC : 0 ≤ C) (hsep : C * Real.posLog Mg < Real.posLog L) :
    ∃ z ∈ closedBall (0 : ℂ) s, C * Real.posLog ‖g z‖ < Real.posLog ‖f (g z)‖ := by
  obtain ⟨z, hz, hzt⟩ := exists_norm_eq_of_closedBall hs hg hz₁ ht
  refine ⟨z, hz, ?_⟩
  have hleft : C * Real.posLog ‖g z‖ ≤ C * Real.posLog Mg :=
    mul_le_mul_of_nonneg_left
      (Real.posLog_le_posLog (norm_nonneg _) (hMg z hz)) hC
  have hright : Real.posLog L ≤ Real.posLog ‖f (g z)‖ :=
    Real.posLog_le_posLog hL0 (hL (g z) hzt)
  linarith

/-! ## The circle version

A circle in the plane is connected too, so the same intermediate-value transfer runs on a single
circle.  This is what allows a floor for a *third* function, valid on the whole circle, to be held
simultaneously with the composition bound. -/

/-- **Every intermediate modulus is attained on a circle.** -/
theorem exists_norm_eq_of_sphere {g : ℂ → ℂ} {σ t : ℝ}
    (hg : ContinuousOn g (sphere (0 : ℂ) σ))
    (hlow : ∃ z₀ ∈ sphere (0 : ℂ) σ, ‖g z₀‖ ≤ t)
    (hhigh : ∃ z₁ ∈ sphere (0 : ℂ) σ, t ≤ ‖g z₁‖) :
    ∃ z ∈ sphere (0 : ℂ) σ, ‖g z‖ = t := by
  obtain ⟨z₀, hz₀, hz₀t⟩ := hlow
  obtain ⟨z₁, hz₁, hz₁t⟩ := hhigh
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hconn : IsPreconnected (sphere (0 : ℂ) σ) :=
    isPreconnected_sphere hrank 0 σ
  obtain ⟨z, hz, hzt⟩ :=
    hconn.intermediate_value hz₀ hz₁ hg.norm (Set.mem_Icc.mpr ⟨hz₀t, hz₁t⟩)
  exact ⟨z, hz, hzt⟩

/-- **Simultaneous control on a circle.**  A floor for `G` on the whole circle survives the choice
of the point at which the composition attains the outer function's floor. -/
theorem exists_point_sphere_floor_and_comp {f g G : ℂ → ℂ} {σ t cG L : ℝ}
    (hg : ContinuousOn g (sphere (0 : ℂ) σ))
    (hlow : ∃ z₀ ∈ sphere (0 : ℂ) σ, ‖g z₀‖ ≤ t)
    (hhigh : ∃ z₁ ∈ sphere (0 : ℂ) σ, t ≤ ‖g z₁‖)
    (hL : ∀ w : ℂ, ‖w‖ = t → L ≤ ‖f w‖)
    (hG : ∀ z ∈ sphere (0 : ℂ) σ, cG ≤ ‖G z‖) :
    ∃ z ∈ sphere (0 : ℂ) σ, cG ≤ ‖G z‖ ∧ L ≤ ‖f (g z)‖ := by
  obtain ⟨z, hz, hzt⟩ := exists_norm_eq_of_sphere hg hlow hhigh
  exact ⟨z, hz, hG z hz, hL (g z) hzt⟩

/-- **Pointwise separation on a circle, with a simultaneous floor.**  At the produced point the
composition outgrows any prescribed multiple of the inner state, and `G` still satisfies its floor.
The three quantities the Clunie estimate weighs — the dependent state, the previous states, and the
top grouped coefficient — are therefore controlled at one and the same point. -/
theorem exists_posLog_separation_of_sphere {f g G : ℂ → ℂ} {σ t cG L Mg C : ℝ}
    (hg : ContinuousOn g (sphere (0 : ℂ) σ))
    (hlow : ∃ z₀ ∈ sphere (0 : ℂ) σ, ‖g z₀‖ ≤ t)
    (hhigh : ∃ z₁ ∈ sphere (0 : ℂ) σ, t ≤ ‖g z₁‖)
    (hL : ∀ w : ℂ, ‖w‖ = t → L ≤ ‖f w‖) (hL0 : 0 ≤ L)
    (hG : ∀ z ∈ sphere (0 : ℂ) σ, cG ≤ ‖G z‖)
    (hMg : ∀ z ∈ sphere (0 : ℂ) σ, ‖g z‖ ≤ Mg)
    (hC : 0 ≤ C) (hsep : C * Real.posLog Mg < Real.posLog L) :
    ∃ z ∈ sphere (0 : ℂ) σ, cG ≤ ‖G z‖ ∧
      C * Real.posLog ‖g z‖ < Real.posLog ‖f (g z)‖ := by
  obtain ⟨z, hz, hzt⟩ := exists_norm_eq_of_sphere hg hlow hhigh
  refine ⟨z, hz, hG z hz, ?_⟩
  have hleft : C * Real.posLog ‖g z‖ ≤ C * Real.posLog Mg :=
    mul_le_mul_of_nonneg_left (Real.posLog_le_posLog (norm_nonneg _) (hMg z hz)) hC
  have hright : Real.posLog L ≤ Real.posLog ‖f (g z)‖ :=
    Real.posLog_le_posLog hL0 (hL (g z) hzt)
  linarith

end GaloisForLFunctions.HTGeometry
