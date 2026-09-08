import GaloisForLFunctions.HTGeometry.LocalSchwartzPairing
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos

/-! A continuous function with vanishing weak second derivative is locally affine. -/
open MeasureTheory Set Filter
open scoped SchwartzMap ContDiff
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

private theorem continuous_zero_of_interval_pairings (f : ℝ → ℂ) (hf : Continuous f) (a b : ℝ)
    (h : ∀ ψ : 𝓢(ℝ,ℂ), (∀ x, x ∉ Ioo a b → ψ x = 0) → (∫ x : ℝ, ψ x*f x) = 0) :
    ∀ x ∈ Ioo a b, f x = 0 := by
  have he := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := (volume : Measure ℝ))
    (hf.locallyIntegrable.locallyIntegrableOn (Ioo a b)) (fun g hg hk hs => ?_)
  · have ha : f =ᵐ[volume.restrict (Ioo a b)] (fun _ => (0:ℂ)) := by
      filter_upwards [ae_restrict_of_ae he,ae_restrict_mem measurableSet_Ioo] with x hx hi
      exact hx hi
    exact Measure.eqOn_open_of_ae_eq ha isOpen_Ioo hf.continuousOn continuousOn_const
  · let ψ : 𝓢(ℝ,ℂ) := (hk.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
    have hp : ∀ x, x ∉ Ioo a b → ψ x = 0 := by
      intro x hx
      change (g x : ℂ) = 0
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)),Complex.ofReal_zero]
    have hh := h ψ hp
    change (∫ x : ℝ, (g x:ℂ)*f x) = 0 at hh
    simpa only [Complex.real_smul] using hh

/-- The exact local affine classification requires no growth assumption on the continuous density. -/
theorem continuous_weak_second_eq_affine (f : ℝ → ℂ) (hf : Continuous f) (a b : ℝ) (hab : a < b)
    (h₂ : ∀ ψ : 𝓢(ℝ,ℂ), (∀ x, x ∉ Ioo a b → ψ x = 0) →
      (∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ ψ)) x*f x) = 0) :
    ∃ A B : ℂ, ∀ x ∈ Ioo a b, f x = A+B*(x:ℂ) := by
  let D := SchwartzMap.derivCLM ℂ ℂ
  let H : 𝓢(ℝ,ℂ) → ℂ := fun ψ => ∫ x : ℝ, (D ψ) x*f x
  obtain ⟨χ,hχ,hiχ⟩ := exists_normalised_test hab
  have hc (ψ : 𝓢(ℝ,ℂ)) (hs : ∀ x, x ∉ Ioo a b → ψ x = 0) :
      HasCompactSupport (ψ : ℝ → ℂ) := schwartz_compact_of_zero_outside_Ioo ψ a b hs
  have hd (ψ : 𝓢(ℝ,ℂ)) (hs : ∀ x, x ∉ Ioo a b → ψ x = 0) :
      HasCompactSupport (D ψ : ℝ → ℂ) := by
    convert (hc ψ hs).deriv using 1 <;> rfl
  have hlin : ∀ (φ ψ : 𝓢(ℝ,ℂ)) (c : ℂ), (∀ x, x ∉ Ioo a b → φ x = 0) → (∀ x, x ∉ Ioo a b → ψ x = 0) →
      H (φ-c • ψ) = H φ-c • H ψ := by
    intro φ ψ c hφ hψ
    dsimp only [H]
    rw [map_sub,map_smul]
    exact schwartz_pair_sub (D φ) (D ψ) (hd φ hφ) (hd ψ hψ) f hf c
  have hD := apply_eq_integral_smul_of_deriv_zero_of_linearOn hlin h₂ hχ hiχ
  let C := H χ
  let F : ℝ → ℂ := fun x => f x+C*(x:ℂ)
  have hF : Continuous F := by unfold F; fun_prop
  let K : 𝓢(ℝ,ℂ) → ℂ := fun ψ => ∫ x : ℝ, ψ x*F x
  have hKlin : ∀ (φ ψ : 𝓢(ℝ,ℂ)) (c : ℂ), (∀ x, x ∉ Ioo a b → φ x = 0) → (∀ x, x ∉ Ioo a b → ψ x = 0) →
      K (φ-c • ψ) = K φ-c • K ψ := by
    intro φ ψ c hφ hψ
    exact schwartz_pair_sub φ ψ (hc φ hφ) (hc ψ hψ) F hF c
  have hKzero : ∀ ψ : 𝓢(ℝ,ℂ), (∀ x, x ∉ Ioo a b → ψ x = 0) → K (D ψ) = 0 := by
    intro ψ hs
    have hd' := hD ψ hs
    rw [schwartz_interval_integral ψ a b hs] at hd'
    have hx := schwartz_pair_derivative ψ (hc ψ hs) (fun x : ℝ => (x:ℂ)) (fun _ => (1:ℂ))
      (fun x => Complex.ofRealCLM.hasDerivAt) continuous_const
    simp only [mul_one] at hx
    change (∫ x : ℝ, (D ψ) x*(f x+C*(x:ℂ))) = 0
    simp only [mul_add,mul_left_comm ((D ψ) _) C]
    rw [integral_add (schwartz_pair_integrable (D ψ) (hd ψ hs) f hf)
      ((schwartz_pair_integrable (D ψ) (hd ψ hs) (fun x : ℝ => (x:ℂ)) Complex.continuous_ofReal).const_mul C),integral_const_mul]
    change (∫ x : ℝ, (D ψ) x*f x) = (∫ x : ℝ, ψ x)*C at hd'
    rw [hd']
    change (∫ x : ℝ, ψ x) = -(∫ x : ℝ, (D ψ) x*(x:ℂ)) at hx
    linear_combination C*hx
  have hK := apply_eq_integral_smul_of_deriv_zero_of_linearOn hKlin hKzero hχ hiχ
  have hz : ∀ x ∈ Ioo a b, F x-K χ = 0 := by
    apply continuous_zero_of_interval_pairings _ (hF.sub continuous_const) a b
    intro ψ hs
    have h := hK ψ hs
    rw [schwartz_interval_integral ψ a b hs] at h
    change (∫ x : ℝ, ψ x*(F x-K χ)) = 0
    simp only [mul_sub]
    rw [integral_sub (schwartz_pair_integrable ψ (hc ψ hs) F hF)
      (schwartz_pair_integrable ψ (hc ψ hs) (fun _ => K χ) continuous_const),integral_mul_const]
    exact sub_eq_zero.mpr h
  refine ⟨K χ,-C,?_⟩
  intro x hx
  have h := hz x hx
  dsimp only [F] at h
  linear_combination h

end
end GaloisForLFunctions.HTGeometry
