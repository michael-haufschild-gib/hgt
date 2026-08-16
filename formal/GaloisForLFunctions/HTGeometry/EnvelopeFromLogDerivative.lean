import Mathlib

/-!
# Exponential envelopes from bounds on a logarithmic derivative

A positive function whose logarithmic derivative is bounded below by `L` grows at least like
`exp ∫ L`, and one bounded above by `U` grows at most like `exp ∫ U`:

```text
f a · exp (∫_a^b L) ≤ f b ≤ f a · exp (∫_a^b U) .
```

Both are the mean value theorem applied to `log f − ∫ L` and to `∫ U − log f`, whose derivatives
are `f′/f − L` and `U − f′/f`.

This is the direction opposite to reading a logarithmic derivative off an envelope: here the
derivative bound is the input and the envelope is the output.  It is what converts an exact
differential relation for a spectral quantity — a leakage, a concentration defect — into two-sided
bounds on that quantity itself.
-/

open Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Monotonicity from a nonnegative derivative on a closed interval. -/
theorem le_of_hasDerivAt_nonneg {F F' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (F' t) t)
    (hnn : ∀ t ∈ Icc a b, 0 ≤ F' t) : F a ≤ F b := by
  have hcont : ContinuousOn F (Icc a b) := fun t ht =>
    ((hF t ht).continuousAt).continuousWithinAt
  have hsub : interior (Icc a b) ⊆ Icc a b := by
    rw [interior_Icc]
    exact Ioo_subset_Icc_self
  have hdiff : DifferentiableOn ℝ F (interior (Icc a b)) := fun t ht =>
    ((hF t (hsub ht)).differentiableAt).differentiableWithinAt
  have hderiv : ∀ t ∈ interior (Icc a b), 0 ≤ deriv F t := by
    intro t ht
    rw [(hF t (hsub ht)).deriv]
    exact hnn t (hsub ht)
  exact monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff hderiv
    (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

/-- **Lower envelope.**  A positive function whose derivative dominates `L · f` grows at least like
the exponential of the integral of `L`. -/
theorem mul_exp_integral_le_of_logDeriv_ge {f f' L : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Icc a b, 0 < f t)
    (hL : Continuous L)
    (hbound : ∀ t ∈ Icc a b, L t * f t ≤ f' t) :
    f a * Real.exp (∫ t in a..b, L t) ≤ f b := by
  set F : ℝ → ℝ := fun t => Real.log (f t) - ∫ s in a..t, L s with hFdef
  have hFderiv : ∀ t ∈ Icc a b, HasDerivAt F (f' t / f t - L t) t := by
    intro t ht
    have h1 : HasDerivAt (fun u => Real.log (f u)) (f' t / f t) t :=
      (hf t ht).log (hpos t ht).ne'
    have h2 : HasDerivAt (fun u => ∫ s in a..u, L s) (L t) t :=
      integral_hasDerivAt_right (hL.intervalIntegrable a t)
        (hL.stronglyMeasurableAtFilter _ _) hL.continuousAt
    exact h1.sub h2
  have hnn : ∀ t ∈ Icc a b, 0 ≤ f' t / f t - L t := by
    intro t ht
    have hp := hpos t ht
    have hb := hbound t ht
    rw [sub_nonneg, le_div_iff₀ hp]
    exact hb
  have hmono := le_of_hasDerivAt_nonneg hab hFderiv hnn
  have hFa : F a = Real.log (f a) := by simp [hFdef]
  rw [hFa] at hmono
  have hlog : Real.log (f a) + (∫ s in a..b, L s) ≤ Real.log (f b) := by
    have : Real.log (f a) ≤ Real.log (f b) - ∫ s in a..b, L s := hmono
    linarith
  have hfa := hpos a (left_mem_Icc.2 hab)
  have hfb := hpos b (right_mem_Icc.2 hab)
  have := Real.exp_le_exp.2 hlog
  rwa [Real.exp_add, Real.exp_log hfa, Real.exp_log hfb] at this

/-- **Upper envelope.**  A positive function whose derivative is dominated by `U · f` grows at most
like the exponential of the integral of `U`. -/
theorem le_mul_exp_integral_of_logDeriv_le {f f' U : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Icc a b, 0 < f t)
    (hU : Continuous U)
    (hbound : ∀ t ∈ Icc a b, f' t ≤ U t * f t) :
    f b ≤ f a * Real.exp (∫ t in a..b, U t) := by
  set F : ℝ → ℝ := fun t => (∫ s in a..t, U s) - Real.log (f t) with hFdef
  have hFderiv : ∀ t ∈ Icc a b, HasDerivAt F (U t - f' t / f t) t := by
    intro t ht
    have h1 : HasDerivAt (fun u => Real.log (f u)) (f' t / f t) t :=
      (hf t ht).log (hpos t ht).ne'
    have h2 : HasDerivAt (fun u => ∫ s in a..u, U s) (U t) t :=
      integral_hasDerivAt_right (hU.intervalIntegrable a t)
        (hU.stronglyMeasurableAtFilter _ _) hU.continuousAt
    exact h2.sub h1
  have hnn : ∀ t ∈ Icc a b, 0 ≤ U t - f' t / f t := by
    intro t ht
    have hp := hpos t ht
    have hb := hbound t ht
    rw [sub_nonneg, div_le_iff₀ hp]
    exact hb
  have hmono := le_of_hasDerivAt_nonneg hab hFderiv hnn
  have hFa : F a = -Real.log (f a) := by simp [hFdef]
  rw [hFa] at hmono
  have hlog : Real.log (f b) ≤ Real.log (f a) + ∫ s in a..b, U s := by
    have : -Real.log (f a) ≤ (∫ s in a..b, U s) - Real.log (f b) := hmono
    linarith
  have hfa := hpos a (left_mem_Icc.2 hab)
  have hfb := hpos b (right_mem_Icc.2 hab)
  have := Real.exp_le_exp.2 hlog
  rwa [Real.exp_add, Real.exp_log hfa, Real.exp_log hfb] at this

/-- **Two-sided envelope.**  Bounding a logarithmic derivative on both sides traps the function
between the two exponentials. -/
theorem envelope_of_logDeriv_bounds {f f' L U : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Icc a b, 0 < f t)
    (hL : Continuous L) (hU : Continuous U)
    (hlow : ∀ t ∈ Icc a b, L t * f t ≤ f' t)
    (hup : ∀ t ∈ Icc a b, f' t ≤ U t * f t) :
    f a * Real.exp (∫ t in a..b, L t) ≤ f b ∧
      f b ≤ f a * Real.exp (∫ t in a..b, U t) :=
  ⟨mul_exp_integral_le_of_logDeriv_ge hab hf hpos hL hlow,
    le_mul_exp_integral_of_logDeriv_le hab hf hpos hU hup⟩

/-! ## The same with the bound continuous only on the window -/

/-- A continuous extension of a function continuous on a closed interval. -/
theorem exists_continuous_eqOn_Icc {L : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hL : ContinuousOn L (Icc a b)) :
    ∃ M : ℝ → ℝ, Continuous M ∧ ∀ t ∈ Icc a b, M t = L t := by
  refine ⟨Set.IccExtend hab fun x : Icc a b => L x, ?_, ?_⟩
  · exact (continuous_IccExtend_iff (h := hab)).mpr hL.restrict
  · intro t ht
    exact Set.IccExtend_val hab (fun x : Icc a b => L x) ⟨t, ht⟩

/-- **Lower envelope, windowed bound.** -/
theorem mul_exp_integral_le_of_logDeriv_ge' {f f' L : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Icc a b, 0 < f t)
    (hL : ContinuousOn L (Icc a b))
    (hbound : ∀ t ∈ Icc a b, L t * f t ≤ f' t) :
    f a * Real.exp (∫ t in a..b, L t) ≤ f b := by
  obtain ⟨M, hMc, hMeq⟩ := exists_continuous_eqOn_Icc hab hL
  have hint : (∫ t in a..b, M t) = ∫ t in a..b, L t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hab] at ht
    exact hMeq t ht
  rw [← hint]
  refine mul_exp_integral_le_of_logDeriv_ge hab hf hpos hMc fun t ht => ?_
  rw [hMeq t ht]
  exact hbound t ht

/-- **Upper envelope, windowed bound.** -/
theorem le_mul_exp_integral_of_logDeriv_le' {f f' U : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Icc a b, 0 < f t)
    (hU : ContinuousOn U (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f' t ≤ U t * f t) :
    f b ≤ f a * Real.exp (∫ t in a..b, U t) := by
  obtain ⟨M, hMc, hMeq⟩ := exists_continuous_eqOn_Icc hab hU
  have hint : (∫ t in a..b, M t) = ∫ t in a..b, U t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hab] at ht
    exact hMeq t ht
  rw [← hint]
  refine le_mul_exp_integral_of_logDeriv_le hab hf hpos hMc fun t ht => ?_
  rw [hMeq t ht]
  exact hbound t ht

/-- **Monotonicity from an interior derivative.**  The derivative is only required on the open
interval, continuity carrying the conclusion to the endpoints.  This is the form needed when the
derivative blows up at an endpoint. -/
theorem le_of_continuousOn_of_deriv_nonneg {F F' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn F (Icc a b))
    (hF : ∀ t ∈ Ioo a b, HasDerivAt F (F' t) t)
    (hnn : ∀ t ∈ Ioo a b, 0 ≤ F' t) : F a ≤ F b := by
  have hdiff : DifferentiableOn ℝ F (interior (Icc a b)) := by
    rw [interior_Icc]
    exact fun t ht => ((hF t ht).differentiableAt).differentiableWithinAt
  have hderiv : ∀ t ∈ interior (Icc a b), 0 ≤ deriv F t := by
    rw [interior_Icc]
    intro t ht
    rw [(hF t ht).deriv]
    exact hnn t ht
  exact monotoneOn_of_deriv_nonneg (convex_Icc a b) hc hdiff hderiv
    (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

end GaloisForLFunctions.HTGeometry
