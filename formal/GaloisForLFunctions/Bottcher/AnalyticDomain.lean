/-
# Analytic functions on a connected set form an integral domain

Foundation of the meromorphic function FIELD needed to package the geometric `σ_n`
(`deckPrecomp₁`) as an automorphism of a field containing the actual Böttcher coordinates. By the
identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`), if a product of two
functions analytic on a preconnected open `U` vanishes on `U`, one of them vanishes on `U` — so the
analytic functions on `U` (modulo agreement) form an integral domain, whose fraction field is the
field of meromorphic functions on `U`. The same argument applies to a connected analytic cover, the
field on which `σ_n` acts.
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic

open Set Filter Topology

namespace Bottcher

/-- **Analytic functions on a connected set are a domain.** If `f`, `g` are analytic on a
preconnected open `U ⊆ ℂ` and `f·g = 0` on `U`, then `f = 0` on `U` or `g = 0` on `U`. (Identity
theorem: where `f ≠ 0`, `g = 0`; that neighbourhood propagates to all of `U`.) The fraction field
of this domain is the meromorphic function field of `U` — the field structure the monodromy
automorphism `σ_n` must live on. -/
theorem analyticOnNhd_domain {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) (hUo : IsOpen U) (hfg : EqOn (fun z => f z * g z) 0 U) :
    EqOn f 0 U ∨ EqOn g 0 U := by
  by_cases h : EqOn f 0 U
  · exact Or.inl h
  · right
    simp only [EqOn, not_forall] at h
    obtain ⟨z₀, hz₀U, hz₀⟩ := h
    have hz₀ne : f z₀ ≠ 0 := fun hc => hz₀ (by simp [hc])
    have hcont : ContinuousAt f z₀ := (hf z₀ hz₀U).continuousAt
    have hg0 : ∀ᶠ z in 𝓝 z₀, g z = 0 := by
      filter_upwards [hcont.eventually_ne hz₀ne, hUo.mem_nhds hz₀U] with z hzne hzU
      have hz := hfg hzU
      simp only [Pi.zero_apply] at hz
      exact (mul_eq_zero.mp hz).resolve_left hzne
    exact hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hz₀U hg0

/-- The reciprocal of a nowhere-zero analytic function is analytic — invertibility within the
analytic functions away from zeros (toward the meromorphic fraction field). -/
theorem analyticOnNhd_inv {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0) :
    AnalyticOnNhd ℂ (fun z => (f z)⁻¹) U :=
  fun z hz => (hf z hz).inv (hne z hz)

/-- A nonzero analytic function on a preconnected open set is generically nonzero (its zero set is
codiscrete in `U`). Hence its reciprocal is meromorphic on `U` — the inverse in the field of
meromorphic functions, the field structure `σ_n` must act on. -/
theorem analyticOnNhd_eventually_ne_zero {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (hne : ¬ EqOn f 0 U) :
    ∀ᶠ x in codiscreteWithin U, f x ≠ 0 :=
  (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hU).resolve_left hne

/-- **Uniqueness of analytic continuation (open-agreement form).** Two functions analytic on a
preconnected open `U` that agree on a nonempty open `V ⊆ U` agree on all of `U`. So a function on a
connected analytic cover is determined by its restriction to any chart — the rigidity that makes the
deck-precomposition `σ_n` well-defined on the meromorphic field of the cover. -/
theorem analyticOnNhd_eqOn_of_eqOn_isOpen {U V : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U)
    (hVU : V ⊆ U) (hVo : IsOpen V) (hVne : V.Nonempty) (hfg : EqOn f g V) :
    EqOn f g U := by
  obtain ⟨z₀, hz₀V⟩ := hVne
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hU (hVU hz₀V) ?_
  filter_upwards [hVo.mem_nhds hz₀V] with z hz using hfg hz

/-- **Meromorphic inverse.** For `f` analytic on `U`, its reciprocal is analytic on the (open)
subset `{z ∈ U | f z ≠ 0}`. With `analyticOnNhd_eventually_ne_zero` (that subset is codiscrete when
`f ≠ 0`), this is the inverse in the field of meromorphic functions: every nonzero meromorphic
function is invertible off a codiscrete set. -/
theorem analyticOnNhd_inv_on_ne {U : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    AnalyticOnNhd ℂ (fun z => (f z)⁻¹) {z | z ∈ U ∧ f z ≠ 0} :=
  fun z hz => (hf z hz.1).inv hz.2

/-- **Multiplicative closure (no nonzero zero-divisors).** The product of two functions analytic on
a preconnected open `U`, neither identically zero, is not identically zero — the multiplicative form
of `analyticOnNhd_domain`, confirming the analytic functions on `U` are an integral domain. -/
theorem analyticOnNhd_mul_ne_zero {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) (hUo : IsOpen U)
    (hfne : ¬ EqOn f 0 U) (hgne : ¬ EqOn g 0 U) : ¬ EqOn (fun z => f z * g z) 0 U :=
  fun hfg => (analyticOnNhd_domain hf hg hU hUo hfg).elim hfne hgne

/-- **Division in the meromorphic field.** For `f, g` analytic on `U`, the quotient `f/g` is analytic
on `{z ∈ U | g z ≠ 0}` — the field-of-fractions division, meromorphic off the (codiscrete) zeros of
`g`. -/
theorem analyticOnNhd_div_on_ne {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) :
    AnalyticOnNhd ℂ (fun z => f z / g z) {z | z ∈ U ∧ g z ≠ 0} := by
  intro z hz
  rw [show (fun z => f z / g z) = (fun z => f z * (g z)⁻¹) by funext w; rw [div_eq_mul_inv]]
  exact (hf z hz.1).mul ((hg z hz.1).inv hz.2)

end Bottcher
