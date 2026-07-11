import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Exact cutoff for correlations of aperture-supported functions

If a function is supported in `[-a, a]`, its correlation with a translate by more than `2 * a`
vanishes identically.  For the logarithmic aperture `[-log λ, log λ]`, every dilation shift
`log q` with `q > λ²` therefore contributes exactly zero.  This is the finite-aperture reduction
used before estimating the prime-weighted first row of the CCM Gram form.
-/

open Set MeasureTheory

namespace RHTower

/-- Two copies of a function supported in `[-a, a]` cannot overlap after a shift larger than
`2 * a`. -/
theorem intervalShiftProduct_eq_zero
    {a t : ℝ} {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Set.Icc (-a) a)
    (ht : 2 * a < t) :
    ∀ x, (starRingEnd ℂ) (f x) * f (x + t) = 0 := by
  intro x
  by_cases hx : f x = 0
  · simp [hx]
  by_cases hxt : f (x + t) = 0
  · simp [hxt]
  have hxmem := hf hx
  have hxtmem := hf hxt
  have hxlo : -a ≤ x := hxmem.1
  have hxthi : x + t ≤ a := hxtmem.2
  exfalso
  linarith

/-- The translation correlation of an interval-supported function is exactly zero beyond the
aperture diameter. -/
theorem intervalShiftCorrelation_eq_zero
    {a t : ℝ} {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Set.Icc (-a) a)
    (ht : 2 * a < t) :
    ∫ x, (starRingEnd ℂ) (f x) * f (x + t) = 0 := by
  have hzero : (fun x => (starRingEnd ℂ) (f x) * f (x + t)) = fun _ => 0 :=
    funext (intervalShiftProduct_eq_zero hf ht)
  rw [hzero]
  simp

/-- Two copies of a function supported in `[-a, a]` cannot overlap after a negative shift whose
magnitude is larger than `2 * a`. -/
theorem intervalNegativeShiftProduct_eq_zero
    {a t : ℝ} {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Set.Icc (-a) a)
    (ht : t < -(2 * a)) :
    ∀ x, (starRingEnd ℂ) (f x) * f (x + t) = 0 := by
  intro x
  by_cases hx : f x = 0
  · simp [hx]
  by_cases hxt : f (x + t) = 0
  · simp [hxt]
  have hxmem := hf hx
  have hxtmem := hf hxt
  have hxhi : x ≤ a := hxmem.2
  have hxtlo : -a ≤ x + t := hxtmem.1
  exfalso
  linarith

/-- The translation correlation of an interval-supported function is exactly zero beyond the
negative aperture diameter. -/
theorem intervalNegativeShiftCorrelation_eq_zero
    {a t : ℝ} {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Set.Icc (-a) a)
    (ht : t < -(2 * a)) :
    ∫ x, (starRingEnd ℂ) (f x) * f (x + t) = 0 := by
  have hzero : (fun x => (starRingEnd ℂ) (f x) * f (x + t)) = fun _ => 0 :=
    funext (intervalNegativeShiftProduct_eq_zero hf ht)
  rw [hzero]
  simp

/-- A function supported in the logarithmic aperture `[-log λ, log λ]` has zero dilation
correlation for every `q > λ²`. -/
theorem logApertureDilationCorrelation_eq_zero
    {lambda q : ℝ} {f : ℝ → ℂ}
    (hlambda : 1 < lambda)
    (hq : lambda ^ 2 < q)
    (hf : Function.support f ⊆ Set.Icc (-Real.log lambda) (Real.log lambda)) :
    ∫ x, (starRingEnd ℂ) (f x) * f (x + Real.log q) = 0 := by
  apply intervalShiftCorrelation_eq_zero hf
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  have hlambda_sq_pos : 0 < lambda ^ 2 := sq_pos_of_pos hlambda_pos
  have hqpos : 0 < q := lt_trans hlambda_sq_pos hq
  calc
    2 * Real.log lambda = Real.log (lambda ^ 2) := by
      rw [Real.log_pow]
      norm_num
    _ < Real.log q := Real.strictMonoOn_log
      (Set.mem_Ioi.mpr hlambda_sq_pos) (Set.mem_Ioi.mpr hqpos) hq

/-- The reverse dilation correlation also vanishes outside the logarithmic aperture. Together
with `logApertureDilationCorrelation_eq_zero`, this covers both shifts in an even Weil form. -/
theorem logApertureReverseDilationCorrelation_eq_zero
    {lambda q : ℝ} {f : ℝ → ℂ}
    (hlambda : 1 < lambda)
    (hq : lambda ^ 2 < q)
    (hf : Function.support f ⊆ Set.Icc (-Real.log lambda) (Real.log lambda)) :
    ∫ x, (starRingEnd ℂ) (f x) * f (x - Real.log q) = 0 := by
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  have hlambda_sq_pos : 0 < lambda ^ 2 := sq_pos_of_pos hlambda_pos
  have hqpos : 0 < q := lt_trans hlambda_sq_pos hq
  have hlog : 2 * Real.log lambda < Real.log q := by
    calc
      2 * Real.log lambda = Real.log (lambda ^ 2) := by
        rw [Real.log_pow]
        norm_num
      _ < Real.log q := Real.strictMonoOn_log
        (Set.mem_Ioi.mpr hlambda_sq_pos) (Set.mem_Ioi.mpr hqpos) hq
  simpa [sub_eq_add_neg] using
    (intervalNegativeShiftCorrelation_eq_zero hf (neg_lt_neg hlog))

end RHTower
