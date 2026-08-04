import GaloisForLFunctions.HTGeometry.PoissonJensenUpperBound

/-!
# Proximity against the maximum modulus

The proximity function is a circle average of `log⁺ ‖f‖`, so a bound for `‖f‖` on the circle bounds
it directly.  Together with the Poisson--Jensen upper bound of `PoissonJensenUpperBound` this gives
the two-sided comparison between the maximum modulus and the proximity average, which is what lets
maximum-modulus estimates be read as value-distribution estimates and back.

The composition estimates also need the shift `f ↦ f - a`: a function without zeros, such as the
exponential, has none of its own, but every value it omits at most once is taken often, and the
shifted function carries the zeros the minimum-modulus argument counts.
-/

open Metric ValueDistribution

namespace GaloisForLFunctions.HTGeometry

/-- **Proximity is bounded by the maximum modulus.**  A bound on the circle bounds the circle
average of `log⁺ ‖f‖`. -/
theorem proximity_top_le_posLog {f : ℂ → ℂ} {r M : ℝ}
    (hf : MeromorphicOn f (sphere (0 : ℂ) |r|))
    (hM : ∀ z ∈ sphere (0 : ℂ) |r|, ‖f z‖ ≤ M) :
    proximity f ⊤ r ≤ Real.posLog M := by
  rw [proximity_top]
  refine Real.circleAverage_mono_on_of_le_circle hf.circleIntegrable_posLog_norm ?_
  intro z hz
  exact Real.posLog_le_posLog (norm_nonneg _) (hM z hz)

/-- **Proximity is bounded by the maximum modulus, stated by radius.** -/
theorem proximity_top_le_posLog_of_norm {f : ℂ → ℂ} {r M : ℝ} (hr : 0 ≤ r)
    (hf : MeromorphicOn f (sphere (0 : ℂ) r))
    (hM : ∀ z : ℂ, ‖z‖ = r → ‖f z‖ ≤ M) :
    proximity f ⊤ r ≤ Real.posLog M := by
  have habs : |r| = r := abs_of_nonneg hr
  refine proximity_top_le_posLog ?_ ?_
  · rw [habs]; exact hf
  · intro z hz
    rw [habs] at hz
    exact hM z (by simpa [mem_sphere_iff_norm] using hz)

/-! ## The shift -/

/-- **The shift costs one constant.**  A lower bound for the shifted composition gives one for the
composition itself. -/
theorem exists_le_norm_comp_sub_const {f g : ℂ → ℂ} {a : ℂ} {S K : ℝ}
    (h : ∃ z ∈ closedBall (0 : ℂ) S, K ≤ ‖f (g z) - a‖) :
    ∃ z ∈ closedBall (0 : ℂ) S, K - ‖a‖ ≤ ‖f (g z)‖ := by
  obtain ⟨z, hz, hK⟩ := h
  refine ⟨z, hz, ?_⟩
  have htri : ‖f (g z) - a‖ ≤ ‖f (g z)‖ + ‖a‖ := norm_sub_le _ _
  linarith

/-- The shift preserves analyticity, and its zeros are the `a`-points. -/
theorem analyticOnNhd_sub_const {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (a : ℂ) :
    AnalyticOnNhd ℂ (fun z => f z - a) U :=
  hf.sub analyticOnNhd_const

theorem sub_const_eq_zero_iff {f : ℂ → ℂ} {a z : ℂ} : f z - a = 0 ↔ f z = a :=
  sub_eq_zero

/-- A nonconstant entire function is nowhere locally equal to a constant, so every shift satisfies
the nondegeneracy hypothesis of the minimum-modulus theorem. -/
theorem not_eventually_sub_const_zero {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    {w₀ w₁ : ℂ} (hne : f w₀ ≠ f w₁) (a : ℂ) (b : ℂ) :
    ¬ ∀ᶠ z in nhds b, f z - a = 0 := by
  intro hcon
  have hconst : ∀ᶠ z in nhds b, f z = a := by
    filter_upwards [hcon] with z hz
    exact sub_eq_zero.mp hz
  have hshift : AnalyticOnNhd ℂ (fun z => f z - a) Set.univ := hf.sub analyticOnNhd_const
  have hev : (fun z => f z - a) =ᶠ[nhds b] 0 := by
    filter_upwards [hcon] with z hz
    exact hz
  have heq := hshift.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ b) hev
  have h₀ : f w₀ = a := by
    have := heq (Set.mem_univ w₀)
    simpa using sub_eq_zero.mp this
  have h₁ : f w₁ = a := by
    have := heq (Set.mem_univ w₁)
    simpa using sub_eq_zero.mp this
  exact hne (h₀.trans h₁.symm)

end GaloisForLFunctions.HTGeometry
