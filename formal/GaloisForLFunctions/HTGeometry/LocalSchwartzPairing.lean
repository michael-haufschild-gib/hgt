import GaloisForLFunctions.HTGeometry.ExponentialTwist
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Local Schwartz pairings and integration by parts without global growth assumptions. -/
open MeasureTheory Set
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- A Schwartz test vanishing outside a bounded interval has compact support. -/
theorem schwartz_compact_of_zero_outside_Ioo (ψ : 𝓢(ℝ,ℂ)) (a b : ℝ)
    (hs : ∀ x, x ∉ Ioo a b → ψ x = 0) : HasCompactSupport (ψ : ℝ → ℂ) :=
  HasCompactSupport.intro isCompact_Icc (fun x hx => hs x (fun h => hx ⟨h.1.le,h.2.le⟩))

/-- The interval integral retains the whole integral of the actual supported test. -/
theorem schwartz_interval_integral (ψ : 𝓢(ℝ,ℂ)) (a b : ℝ)
    (hs : ∀ x, x ∉ Ioo a b → ψ x = 0) :
    (∫ x in a..b, ψ x) = ∫ x : ℝ, ψ x := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  by_contra hn
  exact hx (hs x (fun h => hn ⟨h.1,h.2.le⟩))

/-- A compact test pairs integrably with every continuous function, without growth restrictions. -/
theorem schwartz_pair_integrable (ψ : 𝓢(ℝ,ℂ)) (hs : HasCompactSupport (ψ : ℝ → ℂ))
    (f : ℝ → ℂ) (hf : Continuous f) : Integrable (fun x : ℝ => ψ x*f x) :=
  (ψ.continuous.mul hf).integrable_of_hasCompactSupport hs.mul_right

/-- Integration by parts is justified by the compact test, not by an assumed global domain. -/
theorem schwartz_pair_derivative (ψ : 𝓢(ℝ,ℂ)) (hs : HasCompactSupport (ψ : ℝ → ℂ))
    (f g : ℝ → ℂ) (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) :
    (∫ x : ℝ, ψ x*g x) = -∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ ψ) x*f x := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  apply integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := (ψ : ℝ → ℂ)) (u' := (SchwartzMap.derivCLM ℂ ℂ ψ : ℝ → ℂ)) (v := f) (v' := g)
  · intro x _
    simpa only [SchwartzMap.derivCLM_apply] using ψ.differentiableAt.hasDerivAt
  · exact fun x _ => hf x
  · exact schwartz_pair_integrable ψ hs g hg
  · apply schwartz_pair_integrable _ _ f hfc
    convert hs.deriv using 1 <;> rfl
  · exact schwartz_pair_integrable ψ hs f hfc

/-- Twice integrating a compact test by parts recovers the actual second derivative. -/
theorem schwartz_pair_second_derivative (ψ : 𝓢(ℝ,ℂ)) (hs : HasCompactSupport (ψ : ℝ → ℂ))
    (f g h : ℝ → ℂ) (hf : ∀ x, HasDerivAt f (g x) x)
    (hg : ∀ x, HasDerivAt g (h x) x) (hh : Continuous h) :
    (∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ ψ)) x*f x) =
      ∫ x : ℝ, ψ x*h x := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hs' : HasCompactSupport (SchwartzMap.derivCLM ℂ ℂ ψ : ℝ → ℂ) := by
    convert hs.deriv using 1 <;> rfl
  have h₁ := schwartz_pair_derivative (SchwartzMap.derivCLM ℂ ℂ ψ) hs' f g hf hc
  have h₂ := schwartz_pair_derivative ψ hs g h hg hh
  linear_combination h₁-h₂

/-- Compact-test pairings are linear without any growth assumption on the continuous density. -/
theorem schwartz_pair_sub (φ χ : 𝓢(ℝ,ℂ))
    (hφ : HasCompactSupport (φ : ℝ → ℂ)) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (f : ℝ → ℂ) (hf : Continuous f) (c : ℂ) :
    (∫ x : ℝ, (φ-c • χ) x*f x) = (∫ x : ℝ, φ x*f x)-c*(∫ x : ℝ, χ x*f x) := by
  simp only [sub_apply,smul_apply,smul_eq_mul,sub_mul,mul_assoc]
  rw [integral_sub (schwartz_pair_integrable φ hφ f hf)
    ((schwartz_pair_integrable χ hχ f hf).const_mul c),integral_const_mul]

end
end GaloisForLFunctions.HTGeometry
