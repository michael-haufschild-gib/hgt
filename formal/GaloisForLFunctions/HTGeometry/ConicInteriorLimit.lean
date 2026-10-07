import GaloisForLFunctions.HTGeometry.EvenlyCoveredLimit
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Interior limits of the exponential image of a conic

The identities `zw = C` and `z + conj w = H` exclude infinity when `H` has a
finite limit. Applied to `z = a + I*b`, this gives the conic interior step using
two affine charts, without a quadratic estimate.
-/

namespace GaloisForLFunctions.HTGeometry.ConicInteriorLimit

open Filter Topology Set Complex
open scoped ComplexConjugate OnePoint

theorem finite_limit_of_onePoint {A : Type*} {l : Filter A} {f : A → ℂ} {z : ℂ}
    (h : Tendsto (fun t ↦ (f t : OnePoint ℂ)) l (𝓝 (z : OnePoint ℂ))) :
    Tendsto f l (𝓝 z) := by
  rw [← OnePoint.comap_coe_nhds]
  exact tendsto_comap_iff.mpr h

theorem escape_of_onePoint {A : Type*} {l : Filter A} {f : A → ℂ}
    (h : Tendsto (fun t ↦ (f t : OnePoint ℂ)) l (𝓝 (∞ : OnePoint ℂ))) :
    Tendsto f l (cocompact ℂ) := by
  rw [← coclosedCompact_eq_cocompact, ← OnePoint.comap_coe_nhds_infty]
  exact tendsto_comap_iff.mpr h

theorem finite_or_escape {A : Type*} (U : Ultrafilter A) (f : A → ℂ) :
    (∃ z, Tendsto f U (𝓝 z)) ∨ Tendsto f U (cocompact ℂ) := by
  let V := U.map (fun t ↦ (f t : OnePoint ℂ))
  have h : Tendsto (fun t ↦ (f t : OnePoint ℂ)) U (𝓝 V.lim) := V.le_nhds_lim
  cases hz : V.lim using OnePoint.rec with
  | infty => exact Or.inr (escape_of_onePoint (hz ▸ h))
  | coe z => exact Or.inl ⟨z, finite_limit_of_onePoint (hz ▸ h)⟩

theorem not_finite_and_escape {A X : Type*} [TopologicalSpace X] [T2Space X]
    [WeaklyLocallyCompactSpace X] {l : Filter A} [l.NeBot] {f : A → X} {z : X}
    (hf : Tendsto f l (𝓝 z)) (he : Tendsto f l (cocompact X)) : False := by
  have h₁ := OnePoint.continuous_coe.continuousAt.tendsto.comp hf
  have h₂ := OnePoint.tendsto_coe_infty.comp (he.mono_right cocompact_le_coclosedCompact)
  exact OnePoint.coe_ne_infty z (tendsto_nhds_unique h₁ h₂)

theorem mixed_product_limits {A : Type*} (U : Ultrafilter A) {z w : A → ℂ} {C H : ℂ}
    (hp : ∀ t, z t * w t = C)
    (hh : Tendsto (fun t ↦ z t + conj (w t)) U (𝓝 H)) :
    ∃ z₀ w₀, Tendsto z U (𝓝 z₀) ∧ Tendsto w U (𝓝 w₀) := by
  rcases finite_or_escape U z with ⟨z₀, hz⟩ | hz
  · refine ⟨z₀, conj (H - z₀), hz, ?_⟩
    have hw := Complex.continuous_conj.continuousAt.tendsto.comp (hh.sub hz)
    simpa only [Function.comp_def, add_sub_cancel_left, starRingEnd_self_apply] using hw
  · have hi : Tendsto (fun t ↦ (z t)⁻¹) U (𝓝 0) := by
      apply tendsto_inv₀_cobounded.comp
      simpa only [Metric.cobounded_eq_cocompact] using hz
    have hne : ∀ᶠ t in (U : Filter A), z t ≠ 0 :=
      hz isCompact_singleton.compl_mem_cocompact
    have hw : Tendsto w U (𝓝 0) := by
      have hc : Tendsto (fun t ↦ C * (z t)⁻¹) U (𝓝 0) := by
        simpa using hi.const_mul C
      apply hc.congr'
      filter_upwards [hne] with t ht
      rw [← hp t]
      field_simp
    have hf : Tendsto z U (𝓝 H) := by
      have ht := hh.sub (Complex.continuous_conj.continuousAt.tendsto.comp hw)
      simpa only [Function.comp_apply, map_zero, sub_zero, add_sub_cancel_right] using ht
    exact (not_finite_and_escape hf hz).elim

theorem realPart_limit_of_exp {A : Type*} {l : Filter A} {a : A → ℂ} {x : ℂ}
    (hx : x ≠ 0) (h : Tendsto (fun t ↦ exp (a t)) l (𝓝 x)) :
    Tendsto (fun t ↦ (a t).re) l (𝓝 (Real.log ‖x‖)) := by
  have hh := (Real.continuousAt_log (norm_ne_zero_iff.mpr hx)).tendsto.comp h.norm
  simpa only [Function.comp_def, norm_exp, Real.log_exp] using hh

theorem conic_interior_limits {A : Type*} (U : Ultrafilter A) {a b : A → ℂ}
    {C x y : ℂ} (hconic : ∀ t, a t ^ 2 + b t ^ 2 = C)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxa : Tendsto (fun t ↦ exp (a t)) U (𝓝 x))
    (hyb : Tendsto (fun t ↦ exp (b t)) U (𝓝 y)) :
    ∃ a₀ b₀, Tendsto a U (𝓝 a₀) ∧ Tendsto b U (𝓝 b₀) := by
  let z : A → ℂ := fun t ↦ a t + I * b t
  let w : A → ℂ := fun t ↦ a t - I * b t
  have hp (t : A) : z t * w t = C := by
    calc
      z t * w t = a t ^ 2 - (I * b t) ^ 2 := by dsimp [z, w]; ring
      _ = a t ^ 2 + b t ^ 2 := by simp [mul_pow, I_sq]
      _ = C := hconic t
  have hrealA := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (realPart_limit_of_exp hx hxa)
  have hrealB := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (realPart_limit_of_exp hy hyb)
  have hH : Tendsto (fun t ↦ z t + conj (w t)) U
      (𝓝 (2 * (Real.log ‖x‖ : ℂ) + (2 * I) * (Real.log ‖y‖ : ℂ))) := by
    convert (hrealA.const_mul 2).add (hrealB.const_mul (2 * I)) using 1
    ext t
    apply Complex.ext <;> simp [z, w, mul_re, mul_im] <;> ring
  obtain ⟨z₀, w₀, hz, hw⟩ := mixed_product_limits U hp hH
  refine ⟨(z₀ + w₀) / 2, (z₀ - w₀) / (2 * I), ?_, ?_⟩
  · have hh := (hz.add hw).div_const 2
    apply hh.congr'
    exact Eventually.of_forall fun t ↦ by dsimp [z, w]; ring
  · have hh := (hz.sub hw).div_const (2 * I)
    apply hh.congr'
    exact Eventually.of_forall fun t ↦ by dsimp [z, w]; field_simp; ring

end GaloisForLFunctions.HTGeometry.ConicInteriorLimit
