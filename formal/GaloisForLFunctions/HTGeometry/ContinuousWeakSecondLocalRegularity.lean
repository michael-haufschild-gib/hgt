import GaloisForLFunctions.HTGeometry.ContinuousWeakSecondRegularity

/-! Interior classical regularity needs continuity of the weak density only on its original interval. -/
open MeasureTheory Set Filter
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A continuous weak second density on an open interval gives the actual two interior derivatives.
No extension or endpoint regularity of the density is assumed. -/
theorem continuousOn_weak_second_hasDerivAt (f g : ℝ → ℂ) (hf : Continuous f)
    (a b : ℝ) (hg : ContinuousOn g (Ioo a b))
    (hw : ∀ ψ : 𝓢(ℝ,ℂ), (∀ x, x ∉ Ioo a b → ψ x = 0) →
      (∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ ψ)) x*f x) =
        ∫ x : ℝ, ψ x*g x) :
    ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x ∧ HasDerivAt (deriv f) (g x) x := by
  intro x hx
  let l := (a+x)/2
  let r := (x+b)/2
  have hl : a < l := by dsimp [l]; linarith [hx.1]
  have hlx : l < x := by dsimp [l]; linarith [hx.1]
  have hxr : x < r := by dsimp [r]; linarith [hx.2]
  have hr : r < b := by dsimp [r]; linarith [hx.2]
  have hlr : l < r := hlx.trans hxr
  let c : ℝ → ℝ := fun t => max l (min r t)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcr (t : ℝ) : c t ∈ Ioo a b := by
    exact ⟨hl.trans_le (le_max_left _ _),
      (max_le hlr.le (min_le_left _ _)).trans_lt hr⟩
  have hce (t : ℝ) (ht : t ∈ Ioo l r) : c t = t := by
    simp only [c,min_eq_right ht.2.le,max_eq_right ht.1.le]
  have hgc : Continuous (g ∘ c) := hg.comp_continuous hc hcr
  have hwc : ∀ ψ : 𝓢(ℝ,ℂ), (∀ t, t ∉ Ioo l r → ψ t = 0) →
      (∫ t : ℝ, (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ ψ)) t*f t) =
        ∫ t : ℝ, ψ t*(g ∘ c) t := by
    intro ψ hs
    rw [hw ψ (fun t ht => hs t (fun h => ht ⟨hl.trans h.1,h.2.trans hr⟩))]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Ioo l r
    · rw [Function.comp_apply,hce t ht]
    · rw [hs t ht,zero_mul,zero_mul]
  have h := continuous_weak_second_hasDerivAt f (g ∘ c) hf hgc l r hlr hwc x ⟨hlx,hxr⟩
  simpa only [Function.comp_apply,hce x ⟨hlx,hxr⟩] using h

end
end GaloisForLFunctions.HTGeometry
