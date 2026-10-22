import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Lemma 11.1: convolution preserves the support on a subgroup

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 11.1.

Functions supported on a subgroup `Γ` of a group `G` are closed under convolution, so that
extension by zero embeds them as a subalgebra of the functions on `G`.  The reason is pointwise:
for `r ∉ Γ` the integrand `s ↦ f (s) g (s⁻¹ r)` vanishes identically — if `s ∈ Γ` then
`s⁻¹ r ∉ Γ`, since otherwise `r = s (s⁻¹ r)` would lie in `Γ`.
-/

namespace RHTower

open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) (Γ : Subgroup G)

/-- **Deninger, Lemma 11.1.**  The convolution of two functions supported on a subgroup is
supported on that subgroup: the integrand vanishes identically outside it. -/
theorem deningerConvolution_eq_zero_of_notMem (f g : G → ℂ)
    (hf : ∀ s : G, s ∉ Γ → f s = 0) (hg : ∀ s : G, s ∉ Γ → g s = 0)
    (r : G) (hr : r ∉ Γ) :
    ∫ s, f s * g (s⁻¹ * r) ∂μ = 0 := by
  have h : ∀ s : G, f s * g (s⁻¹ * r) = 0 := by
    intro s
    by_cases hs : s ∈ Γ
    · have hmem : s⁻¹ * r ∉ Γ := by
        intro hmem
        refine hr ?_
        have : s * (s⁻¹ * r) ∈ Γ := Γ.mul_mem hs hmem
        rwa [mul_inv_cancel_left] at this
      rw [hg _ hmem, mul_zero]
    · rw [hf s hs, zero_mul]
  simp only [h, integral_zero]

/-- **Deninger, Lemma 11.1.**  The support of the convolution of two functions supported on a
subgroup is contained in that subgroup. -/
theorem deningerConvolution_support_subset (f g : G → ℂ)
    (hf : ∀ s : G, s ∉ Γ → f s = 0) (hg : ∀ s : G, s ∉ Γ → g s = 0) :
    Function.support (fun r : G => ∫ s, f s * g (s⁻¹ * r) ∂μ) ⊆ (Γ : Set G) := by
  intro r hr
  by_contra hmem
  exact hr (deningerConvolution_eq_zero_of_notMem μ Γ f g hf hg r hmem)

end RHTower
