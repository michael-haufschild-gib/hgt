import Mathlib

/-!
# Stokes' theorem for compactly supported forms on a finite-dimensional space

Let `E` be a finite-dimensional real normed space with a Haar measure `μ` and let
`F : E → E [⋀^Fin k]→L[ℝ] ℝ` be a `C¹` differential `k`-form of compact support.  Then for every
tuple `v` the top-degree evaluation of its exterior derivative integrates to zero:

`∫ (dF)(y; v₀, …, v_k) dμ(y) = 0`.

By `extDeriv_apply`, `(dF)(y; v) = Σ_i (−1)^i ∂_{v_i} [F(·)(v̂_i)](y)`, and each directional
derivative of a compactly supported `C¹` function integrates to zero (integration by parts
against the constant `1`).
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A directional derivative of a compactly supported `C¹` function integrates to zero. -/
theorem integral_fderiv_apply_eq_zero_of_hasCompactSupport {g : E → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (w : E) :
    ∫ y, fderiv ℝ g y w ∂μ = 0 := by
  have hg' : Continuous fun y => fderiv ℝ g y w :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcg' : HasCompactSupport fun y => fderiv ℝ g y w :=
    (hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L w) rfl
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ)
    (f := fun _ : E => (1 : ℝ)) (g := g) (v := w)
    (by simp) (by simpa using hg'.integrable_of_hasCompactSupport hcg')
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const _)
    (fun y _ => (hg.differentiable one_ne_zero) y)
  simpa using h

/-- **Euclidean Stokes**: the exterior derivative of a compactly supported `C¹` form has zero
integral against any tuple of vectors. -/
theorem integral_extDeriv_apply_eq_zero {k : ℕ} {F : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) (v : Fin (k + 1) → E) :
    ∫ y, extDeriv F y v ∂μ = 0 := by
  have hterm : ∀ i : Fin (k + 1), ContDiff ℝ 1 (fun y => F y (i.removeNth v)) :=
    fun i => (ContinuousAlternatingMap.apply ℝ E ℝ (i.removeNth v)).contDiff.comp hF
  have hcterm : ∀ i : Fin (k + 1), HasCompactSupport (fun y => F y (i.removeNth v)) :=
    fun i => hc.comp_left (g := fun L : E [⋀^Fin k]→L[ℝ] ℝ => L (i.removeNth v)) rfl
  have hrepr : (fun y => extDeriv F y v) = fun y => ∑ i : Fin (k + 1),
      (-1 : ℝ) ^ (i : ℕ) * fderiv ℝ (fun y => F y (i.removeNth v)) y (v i) := by
    funext y
    rw [extDeriv_apply ((hF.differentiable one_ne_zero) y) v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zsmul_eq_mul]
    push_cast
    rfl
  have hint : ∀ i : Fin (k + 1), Integrable
      (fun y => (-1 : ℝ) ^ (i : ℕ) * fderiv ℝ (fun y => F y (i.removeNth v)) y (v i)) μ := by
    intro i
    have h := (((hterm i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport
      (((hcterm i).fderiv ℝ).comp_left
        (g := fun L : E →L[ℝ] ℝ => L (v i)) rfl) (μ := μ)
    exact h.const_mul _
  rw [hrepr, integral_finsetSum _ (fun i _ => hint i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, integral_fderiv_apply_eq_zero_of_hasCompactSupport μ (hterm i)
    (hcterm i), mul_zero]

end GaloisForLFunctions.HTGeometry
