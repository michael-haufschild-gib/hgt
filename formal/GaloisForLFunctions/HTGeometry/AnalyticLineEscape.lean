import GaloisForLFunctions.HTGeometry.OrbitEscapeCompactPatch
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Escaping a zero set along an analytic line

For a non-transitive translation group the orbit of a shift is a line, and escaping the degeneracy
locus along it is a one-variable question.

One complex variable is enough: an analytic function that vanishes on a neighbourhood of a point of a
preconnected open set vanishes on the whole set.  So a function nonzero somewhere is nonzero
arbitrarily near every point, and the escape exists — provided the restriction to the line is
analytic and not identically zero.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Escape arbitrarily near any point.**  An analytic function on a preconnected open set that is
nonzero somewhere is nonzero at points arbitrarily close to any given point of the set. -/
theorem exists_ne_zero_near_of_analytic
    {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    (hUopen : IsOpen U) {z₁ : ℂ} (hz₁ : z₁ ∈ U) (hfz₁ : f z₁ ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ U, dist z z₀ < ε ∧ f z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  -- Then `f` vanishes on a neighbourhood of `z₀`, hence on all of `U`.
  have hnhd : U ∩ Metric.ball z₀ ε ∈ nhds z₀ :=
    Filter.inter_mem (hUopen.mem_nhds hz₀) (Metric.ball_mem_nhds z₀ hε)
  have hev : f =ᶠ[nhds z₀] 0 := by
    filter_upwards [hnhd] with z hz
    exact hcon z hz.1 (by simpa [Metric.mem_ball] using hz.2)
  have hzero := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz₀ hev
  exact hfz₁ (hzero hz₁)

/-- **Escape along a line.**  If the restriction of a value to an analytic line through a shift is
nonzero somewhere, some point of the line escapes the zero set. -/
theorem exists_ne_zero_on_line
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    {t₁ : ℂ} (hft₁ : f t₁ ≠ 0) (t₀ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, dist t t₀ < ε ∧ f t ≠ 0 := by
  obtain ⟨t, _, hdist, hne⟩ :=
    exists_ne_zero_near_of_analytic hf isPreconnected_univ isOpen_univ
      (Set.mem_univ t₁) hft₁ (Set.mem_univ t₀) hε
  exact ⟨t, hdist, hne⟩

/-- **Pointwise escape is exactly one good point per line.**  No analyticity is involved: escaping
the degeneracy locus along the translation line of a shift *is* the existence of a translate at
which the value is nonzero.  Analyticity matters only for deriving that existence from weaker
information, such as the restriction to the line not vanishing identically. -/
theorem escape_of_line_ne_zero
    {S : Type*} (act : ℂ → S → S) (D : Set S) (val : S → ℂ)
    (hD : D = {s : S | val s = 0})
    (K : Set S)
    (hne : ∀ s ∈ K, ∃ t₁ : ℂ, val (act t₁ s) ≠ 0) :
    ∀ s ∈ K, ∃ t : ℂ, act t s ∉ D := by
  intro s hs
  obtain ⟨t₁, ht₁⟩ := hne s hs
  refine ⟨t₁, ?_⟩
  rw [hD]
  exact ht₁

end

end GaloisForLFunctions.HTGeometry
