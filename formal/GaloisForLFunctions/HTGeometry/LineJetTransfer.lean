import GaloisForLFunctions.HTGeometry.StripRelationPropagation
import Mathlib.Analysis.Complex.Convex

/-!
# Jets of a line restriction, and the identity theorem on a strip

Restricting a holomorphic function to a vertical line turns complex differentiation into real
differentiation twisted by `i`: the `k`-th derivative of `t ↦ g(σ + it)` is `iᵏ` times the `k`-th
complex derivative at `σ + it`.  So a differential relation on the strip becomes a differential
relation in the real parameter, with the same order and a right-hand side twisted by powers of `i`.

The strip is convex, hence connected, so two holomorphic functions agreeing on the central line agree
on the whole strip — the line accumulates at its own points, which is all the identity theorem needs.
-/

open Filter Topology Metric Set

namespace GaloisForLFunctions

variable {σ R : ℝ}

theorem mem_verticalStrip_line (hR : 0 < R) (σ t : ℝ) :
    ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ verticalStrip σ R := by
  show |((σ : ℂ) + (t : ℂ) * Complex.I).re - σ| < R
  have : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  rw [this]
  simpa using hR

/-- Holomorphy on the strip passes to every iterated derivative. -/
theorem differentiableOn_iteratedDeriv_verticalStrip {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) :
    ∀ k : ℕ, DifferentiableOn ℂ (iteratedDeriv k g) (verticalStrip σ R) := by
  intro k
  induction k with
  | zero => simpa [iteratedDeriv_zero] using hg
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact ((ih.analyticOnNhd (isOpen_verticalStrip σ R)).deriv).differentiableOn

/-- The derivative of a vertical-line restriction is `i` times the complex derivative. -/
theorem hasDerivAt_line_restriction {g : ℂ → ℂ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I))
      (Complex.I * deriv g ((σ : ℂ) + (t : ℂ) * Complex.I)) t := by
  have hofReal := (hasDerivAt_id t).ofReal_comp
  have hline : HasDerivAt (fun s : ℝ => ((σ : ℂ) + (s : ℂ) * Complex.I)) Complex.I t := by
    have h := (hofReal.mul_const Complex.I).const_add ((σ : ℂ))
    simpa using h
  have hgd : HasDerivAt g (deriv g ((σ : ℂ) + (t : ℂ) * Complex.I))
      ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    (hg.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds
      (mem_verticalStrip_line hR σ t))).hasDerivAt
  have hcomp := HasDerivAt.scomp t hgd hline
  simp only [smul_eq_mul] at hcomp
  exact hcomp

/-- **The jet of the line restriction is the complex jet, twisted by powers of `i`.** -/
theorem iteratedDeriv_line_restriction {g : ℂ → ℂ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) : ∀ (k : ℕ) (t : ℝ),
      iteratedDeriv k (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t
        = Complex.I ^ k * iteratedDeriv k g ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  intro k
  induction k with
  | zero =>
      intro t
      simp [iteratedDeriv_zero]
  | succ j ih =>
      intro t
      have hjd : DifferentiableOn ℂ (iteratedDeriv j g) (verticalStrip σ R) :=
        differentiableOn_iteratedDeriv_verticalStrip hg j
      have hstep : HasDerivAt
          (fun s : ℝ => Complex.I ^ j * iteratedDeriv j g ((σ : ℂ) + (s : ℂ) * Complex.I))
          (Complex.I ^ j * (Complex.I * deriv (iteratedDeriv j g)
            ((σ : ℂ) + (t : ℂ) * Complex.I))) t :=
        (hasDerivAt_line_restriction hR hjd t).const_mul _
      have hfun : (iteratedDeriv j fun w : ℝ => g ((σ : ℂ) + (w : ℂ) * Complex.I))
          = fun s : ℝ => Complex.I ^ j * iteratedDeriv j g ((σ : ℂ) + (s : ℂ) * Complex.I) := by
        funext s
        exact ih s
      rw [iteratedDeriv_succ, hfun]
      rw [hstep.deriv, iteratedDeriv_succ]
      ring

theorem convex_verticalStrip (σ R : ℝ) : Convex ℝ (verticalStrip σ R) := by
  have hset : verticalStrip σ R = {z : ℂ | z.re < σ + R} ∩ {z : ℂ | σ - R < z.re} := by
    ext z
    simp only [verticalStrip, Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
    constructor
    · intro h; exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · intro h; exact ⟨by linarith [h.2], by linarith [h.1]⟩
  rw [hset]
  exact (convex_halfSpace_re_lt _).inter (convex_halfSpace_re_gt _)

/-- **Identity theorem on a strip.**  Two holomorphic functions agreeing on the central line agree
on the whole strip. -/
theorem eqOn_of_eqOn_line {g h : ℂ → ℂ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    (hline : ∀ t : ℝ, g ((σ : ℂ) + (t : ℂ) * Complex.I) = h ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  have hga : AnalyticOnNhd ℂ g (verticalStrip σ R) := hg.analyticOnNhd (isOpen_verticalStrip σ R)
  have hha : AnalyticOnNhd ℂ h (verticalStrip σ R) := hh.analyticOnNhd (isOpen_verticalStrip σ R)
  have hpre : IsPreconnected (verticalStrip σ R) := (convex_verticalStrip σ R).isPreconnected
  have hmem : (σ : ℂ) ∈ verticalStrip σ R := by
    have := mem_verticalStrip_line hR σ 0
    simpa using this
  refine hga.eqOn_of_preconnected_of_frequently_eq hha hpre hmem ?_
  -- the line accumulates at `σ`
  have htend : Tendsto (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhdsWithin (σ : ℂ) {(σ : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      have := hcont.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      apply ht
      have : (t : ℂ) * Complex.I = 0 := by
        have := hcon
        simpa using congrArg (fun w : ℂ => w - (σ : ℂ)) this
      have ht0 : (t : ℂ) = 0 := by
        simpa using this
      exact_mod_cast ht0
  refine htend.frequently ?_
  refine Filter.Eventually.frequently ?_
  filter_upwards with t
  exact hline t

section LocalIdentity

/-- Identity theorem from agreement near one point of the central line. -/
theorem eqOn_of_eventuallyEq_line {g h : ℂ → ℂ} (hR : 0 < R) {t₀ : ℝ}
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    (hline : (fun t : ℝ => g ((σ : ℂ) + (t : ℂ) * Complex.I))
      =ᶠ[nhds t₀] fun t : ℝ => h ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  have hga : AnalyticOnNhd ℂ g (verticalStrip σ R) := hg.analyticOnNhd (isOpen_verticalStrip σ R)
  have hha : AnalyticOnNhd ℂ h (verticalStrip σ R) := hh.analyticOnNhd (isOpen_verticalStrip σ R)
  have hpre : IsPreconnected (verticalStrip σ R) := (convex_verticalStrip σ R).isPreconnected
  have hmem : ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ∈ verticalStrip σ R := mem_verticalStrip_line hR σ t₀
  refine hga.eqOn_of_preconnected_of_frequently_eq hha hpre hmem ?_
  have htend : Tendsto (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) (nhdsWithin t₀ {t₀}ᶜ)
      (nhdsWithin ((σ : ℂ) + (t₀ : ℂ) * Complex.I) {((σ : ℂ) + (t₀ : ℂ) * Complex.I)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      exact (hcont.tendsto t₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      apply ht
      have hsub : ((t : ℂ) - (t₀ : ℂ)) * Complex.I = 0 := by
        have := congrArg (fun w : ℂ => w - ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) hcon
        simp only [sub_self] at this
        rw [← this]
        ring
      have ht0 : (t : ℂ) = (t₀ : ℂ) := by
        rcases mul_eq_zero.mp hsub with hz | hz
        · exact sub_eq_zero.mp hz
        · exact absurd hz Complex.I_ne_zero
      exact_mod_cast ht0
  refine htend.frequently (Filter.Eventually.frequently ?_)
  exact hline.filter_mono nhdsWithin_le_nhds

end LocalIdentity

end GaloisForLFunctions
