import GaloisForLFunctions.HTGeometry.PolyaMaximumTransfer

/-!
# The composition disc at a free base point

The quantitative open mapping theorem places a disc of radius `ε/2` in the image, centred at the
value of the inner function at the *centre* of the ball on whose boundary circle the displacement
floor `ε` holds.  Nothing forces that centre to be the origin: applying the theorem on a subdisc
centred anywhere in the ball produces the same disc in the image of the large ball, now centred at
the value there.

This matters because the displacement floor at the origin is genuinely bounded for functions such as
`exp - 1`, while at a suitable interior base point it is of the order of the maximum modulus.  The
base point is a free parameter of the construction, and freeing it is what turns the transfer into a
usable composition-growth estimate.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

/-- A nonconstant entire function is nowhere locally constant. -/
theorem not_eventually_const_of_ne {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Set.univ) {w₀ w₁ : ℂ} (hne : g w₀ ≠ g w₁) (c : ℂ) :
    ¬ ∀ᶠ z in nhds c, g z = g c := by
  intro hcon
  have hshift : AnalyticOnNhd ℂ (fun z => g z - g c) Set.univ :=
    hg.sub analyticOnNhd_const
  have hev : (fun z => g z - g c) =ᶠ[nhds c] 0 := by
    filter_upwards [hcon] with z hz
    simp [hz]
  have heq := hshift.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ c) hev
  have h₀ : g w₀ = g c := by
    have := heq (Set.mem_univ w₀)
    simpa using sub_eq_zero.mp this
  have h₁ : g w₁ = g c := by
    have := heq (Set.mem_univ w₁)
    simpa using sub_eq_zero.mp this
  exact hne (h₀.trans h₁.symm)

/-- **A circle floor at an interior base point puts a disc in the image of the large ball.**  The
displacement floor is taken on a circle around the base point `c`, and the resulting disc in the
image is centred at `g c`. -/
theorem ball_subset_image_of_circle_floor_at {g : ℂ → ℂ} {s r ε : ℝ} {c : ℂ}
    (hr : 0 < r) (hcs : ‖c‖ + r ≤ s)
    (hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) s))
    (hfloor : ∀ z ∈ sphere c r, ε ≤ ‖g z - g c‖)
    (hnc : ¬ ∀ᶠ z in nhds c, g z = g c) :
    ball (g c) (ε / 2) ⊆ g '' closedBall (0 : ℂ) s := by
  have hsub : closedBall c r ⊆ closedBall (0 : ℂ) s := by
    intro z hz
    have hzc : ‖z - c‖ ≤ r := mem_closedBall_iff_norm.mp hz
    have : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
      calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
    rw [mem_closedBall_iff_norm, sub_zero]
    linarith
  have hgball : AnalyticOnNhd ℂ g (closedBall c r) := hg.mono hsub
  have hdiff : DifferentiableOn ℂ g (ball c r) :=
    (hgball.differentiableOn).mono ball_subset_closedBall
  have hclos : closure (ball c r) = closedBall c r := closure_ball c (ne_of_gt hr)
  have hcont : ContinuousOn g (closure (ball c r)) := by
    rw [hclos]
    exact hgball.continuousOn
  have hdc : DiffContOnCl ℂ g (ball c r) := ⟨hdiff, hcont⟩
  have hfreq : ∃ᶠ z in nhds c, g z ≠ g c := Filter.not_eventually.mp hnc
  have himg := hdc.ball_subset_image_closedBall hr hfloor hfreq
  exact subset_trans himg (Set.image_mono hsub)

/-- **The composition bound at a free base point.**  A bound for `f ∘ g` on the disc of radius `s`
bounds `f` on the closed disc of radius `ρ` about `g c`, for every `ρ < ε/2`, where `ε` is the
displacement floor of `g` around the interior base point `c`. -/
theorem norm_le_of_circle_floor_at {f g : ℂ → ℂ} {s r ε ρ K : ℝ} {c : ℂ}
    (hr : 0 < r) (hcs : ‖c‖ + r ≤ s) (hρ : 0 < ρ) (hρε : ρ < ε / 2)
    (hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) s))
    (hfloor : ∀ z ∈ sphere c r, ε ≤ ‖g z - g c‖)
    (hnc : ¬ ∀ᶠ z in nhds c, g z = g c)
    (hf : AnalyticOnNhd ℂ f (closedBall (g c) ρ))
    (hK : ∀ z ∈ closedBall (0 : ℂ) s, ‖f (g z)‖ ≤ K) :
    ∀ w ∈ closedBall (g c) ρ, ‖f w‖ ≤ K := by
  have himg := ball_subset_image_of_circle_floor_at hr hcs hg hfloor hnc
  have hsub : sphere (g c) ρ ⊆ g '' closedBall (0 : ℂ) s := by
    refine subset_trans ?_ himg
    intro w hw
    have hdist : dist w (g c) = ρ := by
      simpa [mem_sphere_iff_norm, dist_eq_norm] using hw
    simp only [mem_ball, hdist]
    linarith
  exact norm_le_of_sphere_subset_image hρ hf hsub hK

/-- **Composition growth at a free base point.**  If the outer function exceeds `K` somewhere on the
disc of radius `ρ` about `g c`, then the composition exceeds `K` somewhere on the disc of radius `s`.
This is the composition-growth statement: the disc on which the outer function is tested has radius
half the *interior* displacement floor of the inner function, which for a transcendental inner
function is of the order of its maximum modulus. -/
theorem exists_norm_comp_gt_at {f g : ℂ → ℂ} {s r ε ρ K : ℝ} {c : ℂ}
    (hr : 0 < r) (hcs : ‖c‖ + r ≤ s) (hρ : 0 < ρ) (hρε : ρ < ε / 2)
    (hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) s))
    (hfloor : ∀ z ∈ sphere c r, ε ≤ ‖g z - g c‖)
    (hnc : ¬ ∀ᶠ z in nhds c, g z = g c)
    (hf : AnalyticOnNhd ℂ f (closedBall (g c) ρ))
    {w₀ : ℂ} (hw₀ : w₀ ∈ closedBall (g c) ρ) (hlarge : K < ‖f w₀‖) :
    ∃ z ∈ closedBall (0 : ℂ) s, K < ‖f (g z)‖ := by
  by_contra hcon
  have hall : ∀ z ∈ closedBall (0 : ℂ) s, ‖f (g z)‖ ≤ K := by
    intro z hz
    by_contra hc
    exact hcon ⟨z, hz, not_le.mp hc⟩
  exact absurd (norm_le_of_circle_floor_at hr hcs hρ hρε hg hfloor hnc hf hall w₀ hw₀)
    (not_le.mpr hlarge)

end GaloisForLFunctions.HTGeometry
