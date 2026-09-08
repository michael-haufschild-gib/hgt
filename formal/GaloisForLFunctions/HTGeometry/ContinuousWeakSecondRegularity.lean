import GaloisForLFunctions.HTGeometry.ContinuousWeakSecondAffine

/-! Continuous weak second derivatives give actual classical interior derivatives. -/
open MeasureTheory Set Filter
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- Local weak second differentiation with a continuous density is classical in the interior. -/
theorem continuous_weak_second_hasDerivAt (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) (hab : a < b)
    (hw : ∀ ψ : 𝓢(ℝ,ℂ), (∀ x, x ∉ Ioo a b → ψ x = 0) →
      (∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ ψ)) x*f x) = ∫ x : ℝ, ψ x*g x) :
    ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x ∧ HasDerivAt (deriv f) (g x) x := by
  let G : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, g t
  have hG (x : ℝ) : HasDerivAt G (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 x)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have hGc : Continuous G := continuous_iff_continuousAt.mpr (fun x => (hG x).continuousAt)
  let H : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, G t
  have hH (x : ℝ) : HasDerivAt H (G x) x :=
    intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable 0 x)
      (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt
  have hHc : Continuous H := continuous_iff_continuousAt.mpr (fun x => (hH x).continuousAt)
  have hz : ∀ ψ : 𝓢(ℝ,ℂ), (∀ x, x ∉ Ioo a b → ψ x = 0) →
      (∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ ψ)) x*(f x-H x)) = 0 := by
    intro ψ hs
    have hk := schwartz_compact_of_zero_outside_Ioo ψ a b hs
    have hkd : HasCompactSupport (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ ψ) : ℝ → ℂ) := by
      convert hk.deriv.deriv using 1 <;> rfl
    simp only [mul_sub]
    rw [integral_sub (schwartz_pair_integrable _ hkd f hf) (schwartz_pair_integrable _ hkd H hHc),
      hw ψ hs,schwartz_pair_second_derivative ψ hk H G g hH hG hg,sub_self]
  obtain ⟨A,B,hAB⟩ := continuous_weak_second_eq_affine (fun x => f x-H x) (hf.sub hHc) a b hab hz
  have he (x : ℝ) (hx : x ∈ Ioo a b) : f x = H x+A+B*(x:ℂ) := by
    have h := hAB x hx
    linear_combination h
  have hfirst (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt f (G x+B) x := by
    have hd : HasDerivAt (fun x : ℝ => H x+A+B*(x:ℂ)) (G x+B) x := by
      have h := ((hH x).add_const A).add ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul B)
      convert h using 1 <;> first | rfl | simp
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact he t ht
  intro x hx
  refine ⟨(hfirst x hx).differentiableAt,?_⟩
  apply ((hG x).add_const B).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  exact (hfirst t ht).deriv

end
end GaloisForLFunctions.HTGeometry
