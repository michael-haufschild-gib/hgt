import GaloisForLFunctions.RHTower.Sieve.DampedSizeFloor

/-!
# The uniform distance cannot exceed the prime mass

`DampedSizeFloor` bounds the damping by twice the prime mass, using only `1 − Re(f(p)·conj(g(p))) ≤ 2`.
That is attained at a single frequency — for `f(p) = −1` at `t = 0` — but a damped route needs a
distance *uniform* over a whole range of frequencies, and averaging shows the uniform level is at most
the prime mass itself, not twice it.

For each prime the oscillatory average is small: expanding
`Re(f(p)·conj(n^{it}))|_{n=p} = Re(f(p))cos(t log p) + Im(f(p))sin(t log p)` and integrating,

`|∫_0^T Re(f(p)·conj(charFn t p)) dt| ≤ 3/log p`.

Summing against `1/p`, the average of the distance over `[0,T]` is at most
`∑_{p ∈ P}1/p + (3/T)∑_{p ∈ P}1/(p log p)`, so some frequency in the range attains that.  Hence in
`dampedSize`, `e^{−δ²}` can never be smaller than `≍ e^{−∑_p 1/p} ≍ (log z)^{-1}` once `T` is large, and
the first part of the damped size is `≳ (log z/A)e^{2A}(log z)^{-1}`, whose minimum over `A = (σ−1)log z`
is `Θ(1)`.  So even with the truncation tail removed, the damped analytic term is `Θ(x^σ)` — exactly the
trivial size, never below it.  The borderline is a theorem about the distance, not a defect of the Euler
bound.
-/

noncomputable section
namespace RHTower.Sieve
open Finset MeasureTheory

/-- The real part of the paired term, expanded. -/
theorem re_mul_conj_charFn (f : ℕ → ℂ) (t : ℝ) (p : ℕ) :
    (f p * (starRingEnd ℂ) (charFn t p)).re
      = (f p).re * Real.cos (t * Real.log (p : ℝ))
        + (f p).im * Real.sin (t * Real.log (p : ℝ)) := by
  rw [charFn, ← Complex.exp_conj, Complex.mul_re]
  have hconj : (starRingEnd ℂ) (((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)
      = -(((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hneg : -(((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)
      = (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hconj, hneg, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
    Real.sin_neg]
  ring

/-- **The oscillatory average at one prime.**  Both `∫_0^T cos(ta)dt` and `∫_0^T sin(ta)dt` are
`O(1/|a|)`, so the paired real part averages to `O(1/log p)`. -/
theorem abs_integral_re_mul_conj_charFn_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : 2 ≤ p)
    (T : ℝ) :
    |∫ t in (0 : ℝ)..T, (f p * (starRingEnd ℂ) (charFn t p)).re| ≤ 3 / Real.log (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlog : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by linarith)
  set a : ℝ := Real.log (p : ℝ) with ha
  have hane : a ≠ 0 := hlog.ne'
  have hcos : (∫ t in (0 : ℝ)..T, Real.cos (t * a)) = Real.sin (T * a) / a := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun s : ℝ => Real.sin (s * a) / a) (Real.cos (t * a)) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => s * a) a t := by
        simpa using (hasDerivAt_id t).mul_const a
      have h2 : HasDerivAt (fun s : ℝ => Real.sin (s * a)) (Real.cos (t * a) * a) t := h1.sin
      have h3 := h2.div_const a
      have hval : Real.cos (t * a) * a / a = Real.cos (t * a) := by field_simp
      rwa [hval] at h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable
        (μ := volume) _ _)]
    simp
  have hsin : (∫ t in (0 : ℝ)..T, Real.sin (t * a)) = (1 - Real.cos (T * a)) / a := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun s : ℝ => -(Real.cos (s * a)) / a) (Real.sin (t * a)) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => s * a) a t := by
        simpa using (hasDerivAt_id t).mul_const a
      have h2 : HasDerivAt (fun s : ℝ => Real.cos (s * a)) (-Real.sin (t * a) * a) t := h1.cos
      have h3 := (h2.neg).div_const a
      have hval : -(-Real.sin (t * a) * a) / a = Real.sin (t * a) := by field_simp
      rwa [hval] at h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Real.continuous_sin.comp (continuous_id.mul continuous_const)).intervalIntegrable
        (μ := volume) _ _)]
    simp
    ring
  have hsplit : (∫ t in (0 : ℝ)..T,
        ((f p).re * Real.cos (t * a) + (f p).im * Real.sin (t * a)))
      = (f p).re * (∫ t in (0 : ℝ)..T, Real.cos (t * a))
        + (f p).im * (∫ t in (0 : ℝ)..T, Real.sin (t * a)) := by
    have hc1 : IntervalIntegrable (fun t : ℝ => (f p).re * Real.cos (t * a)) volume 0 T := by
      refine Continuous.intervalIntegrable ?_ _ _
      fun_prop
    have hc2 : IntervalIntegrable (fun t : ℝ => (f p).im * Real.sin (t * a)) volume 0 T := by
      refine Continuous.intervalIntegrable ?_ _ _
      fun_prop
    rw [intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hcongr : (∫ t in (0 : ℝ)..T, (f p * (starRingEnd ℂ) (charFn t p)).re)
      = (f p).re * (Real.sin (T * a) / a) + (f p).im * ((1 - Real.cos (T * a)) / a) := by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      (f p).re * Real.cos (t * a) + (f p).im * Real.sin (t * a))
      (fun t _ => by rw [re_mul_conj_charFn]), hsplit, hcos, hsin]
  rw [hcongr]
  have hre : |(f p).re| ≤ 1 := le_trans (Complex.abs_re_le_norm (f p)) (hf p)
  have him : |(f p).im| ≤ 1 := le_trans (Complex.abs_im_le_norm (f p)) (hf p)
  have hs : |Real.sin (T * a)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |1 - Real.cos (T * a)| ≤ 2 := by
    have h1 := Real.neg_one_le_cos (T * a)
    have h2 := Real.cos_le_one (T * a)
    rw [abs_le]
    constructor <;> linarith
  have h1 : |(f p).re * (Real.sin (T * a) / a)| ≤ 1 / a := by
    rw [abs_mul, abs_div, abs_of_pos hlog]
    calc |(f p).re| * (|Real.sin (T * a)| / a) ≤ 1 * (1 / a) := by
          refine mul_le_mul hre (div_le_div_of_nonneg_right hs hlog.le) (by positivity) zero_le_one
      _ = 1 / a := one_mul _
  have h2 : |(f p).im * ((1 - Real.cos (T * a)) / a)| ≤ 2 / a := by
    rw [abs_mul, abs_div, abs_of_pos hlog]
    calc |(f p).im| * (|1 - Real.cos (T * a)| / a) ≤ 1 * (2 / a) := by
          refine mul_le_mul him (div_le_div_of_nonneg_right hc hlog.le) (by positivity) zero_le_one
      _ = 2 / a := one_mul _
  calc |(f p).re * (Real.sin (T * a) / a) + (f p).im * ((1 - Real.cos (T * a)) / a)|
      ≤ |(f p).re * (Real.sin (T * a) / a)| + |(f p).im * ((1 - Real.cos (T * a)) / a)| :=
        abs_add_le _ _
    _ ≤ 1 / a + 2 / a := by linarith [h1, h2]
    _ = 3 / a := by ring

end RHTower.Sieve
end
