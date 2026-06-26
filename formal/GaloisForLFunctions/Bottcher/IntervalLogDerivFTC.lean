/-
# Interval closed-loop FTC for the logarithmic derivative

The interval form of `ClosedLoopFTC.exp_integral_logDeriv` (which is global, `∀ t`): on an open convex
`U ⊇ [a,b]` where `g` is differentiable, nonvanishing, with continuous derivative,
`exp(∫ₐᵇ g'/g) = g(b)/g(a)`.  Needed for the per-arc winding integrals of the `∂F` contour (the arcs
live on bounded sub-intervals of `(0,∞)`, where `λ(it)` is defined).
-/
import Mathlib
open Complex intervalIntegral

theorem exp_integral_logDeriv_interval {g g' : ℝ → ℂ} {a b : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hab : Set.uIcc a b ⊆ U)
    (hderiv : ∀ t ∈ U, HasDerivAt g (g' t) t) (hg : ∀ t ∈ U, g t ≠ 0)
    (hcont' : ContinuousOn g' U) :
    Complex.exp (∫ t in a..b, g' t / g t) = g b / g a := by
  have hgcont : ContinuousOn g U := fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hLcont : ContinuousOn (fun t => g' t / g t) U := hcont'.div hgcont (fun t ht => hg t ht)
  have haU : a ∈ U := hab Set.left_mem_uIcc
  set G : ℝ → ℂ := fun t => ∫ s in a..t, g' s / g s with hGdef
  have hGderiv : ∀ t ∈ U, HasDerivAt G (g' t / g t) t := by
    intro t ht
    have hsub : Set.uIcc a t ⊆ U := by rw [← segment_eq_uIcc]; exact hUc.segment_subset haU ht
    have hct : ContinuousAt (fun s => g' s / g s) t := hLcont.continuousAt (hU.mem_nhds ht)
    exact intervalIntegral.integral_hasDerivAt_right ((hLcont.mono hsub).intervalIntegrable)
      (ContinuousAt.stronglyMeasurableAtFilter hU
        (fun z hz => hLcont.continuousAt (hU.mem_nhds hz)) t ht) hct
  set ψ : ℝ → ℂ := fun t => g t * Complex.exp (-G t) with hψdef
  have hψderiv : ∀ t ∈ U, HasDerivAt ψ 0 t := by
    intro t ht
    have hexp : HasDerivAt (fun u => Complex.exp (-G u)) (Complex.exp (-G t) * (-(g' t / g t))) t :=
      ((hGderiv t ht).neg).cexp
    have hmul := (hderiv t ht).mul hexp
    have hzero : g' t * Complex.exp (-G t) + g t * (Complex.exp (-G t) * (-(g' t / g t))) = 0 := by
      field_simp [hg t ht]; ring
    rw [hzero] at hmul; exact hmul
  have hconst : ψ b = ψ a := by
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hψderiv t (hab ht)) (intervalIntegrable_const (c := (0:ℂ)))
    simp only [intervalIntegral.integral_zero] at hint
    linear_combination -hint
  have hGa : G a = 0 := by simp [hGdef]
  have hψa : ψ a = g a := by simp [hψdef, hGa]
  rw [hψa] at hconst
  have e1 : g b * (Complex.exp (G b))⁻¹ = g a := by rw [← Complex.exp_neg]; exact hconst
  rw [eq_div_iff (hg a haU)]
  have hexpne : Complex.exp (G b) ≠ 0 := Complex.exp_ne_zero _
  field_simp at e1
  linear_combination -e1
