import GaloisForLFunctions.RHTower.VanDerCorputLocal

/-!
# The log-chirp integral, with an explicit rate

The phase `t ↦ c · t log t` is the Riemann–von Mangoldt main term: it is the smooth part of every
zero-counting function in the Selberg class, with `c = d_F/2π`.  Averages of `exp(i c t log t)` are
the geometric side of any argument that plays integrality of the counting function against an
arithmetic evaluation, and what such arguments use is that the average vanishes.

Vanishing is not the sharp statement.  Since `φ''(t) = c/t`, the second-derivative test gives the
rate

`‖∫_T^R exp(i c t log t) dt‖ ≤ 64 √R / √c`,

so on `[T, 2T]` the *normalized* average is `O((cT)^{-1/2})`.  The estimate is unconditional and
uniform in `c`, which is what makes it usable when `c` itself is a parameter — for instance when `c`
is an integer multiple of a degree, and one needs the bound to hold uniformly in that multiple.

The log-chirp is exactly the case the global van der Corput cannot reach: `t log t` is not `C²` at
`t = 0`, so the phase is smooth only on the open ray.  This file uses the local test.
-/

open MeasureTheory Set Complex

namespace RHTower

noncomputable section

/-- **The log-chirp is nonstationary at rate `√(R/c)`, with an amplitude.** -/
theorem norm_integral_logChirp_le {c T R : ℝ} (hc : 0 < c) (hT : 0 < T) (hTR : T ≤ R)
    {A A' : ℝ → ℂ} (hA : ∀ x ∈ Icc T R, HasDerivAt A (A' x) x)
    (hA'c : ContinuousOn A' (Icc T R)) :
    ‖∫ t in T..R, A t * Complex.exp (Complex.I * ((c * (t * Real.log t) : ℝ) : ℂ))‖
      ≤ 32 * (‖A R‖ + ‖A T‖ + ∫ t in T..R, ‖A' t‖) * Real.sqrt R / Real.sqrt c := by
  have hR : 0 < R := hT.trans_le hTR
  have hmu : 0 < c / R := div_pos hc hR
  have hpos : ∀ x ∈ Icc T R, 0 < x := fun x hx => hT.trans_le hx.1
  have hφ : ∀ x ∈ Icc T R,
      HasDerivAt (fun t : ℝ => c * (t * Real.log t)) (c * (Real.log x + 1)) x := by
    intro x hx
    have hx0 : 0 < x := hpos x hx
    have h1 : HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x := by
      have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0.ne')
      simpa [mul_inv_cancel₀ hx0.ne'] using! h
    exact h1.const_mul c
  have hφ' : ∀ x ∈ Icc T R,
      HasDerivAt (fun t : ℝ => c * (Real.log t + 1)) (c / x) x := by
    intro x hx
    have hx0 : 0 < x := hpos x hx
    have h := ((Real.hasDerivAt_log hx0.ne').add_const 1).const_mul c
    simpa [div_eq_mul_inv] using h
  have hφ''c : ContinuousOn (fun t : ℝ => c / t) (Icc T R) :=
    continuousOn_const.div continuousOn_id (fun x hx => (hpos x hx).ne')
  have hbound : ∀ x ∈ Icc T R, c / R ≤ c / x := fun x hx =>
    div_le_div_of_nonneg_left hc.le (hpos x hx) hx.2
  have hkey := secondDerivTestOn hTR hmu hφ hφ' hφ''c hA hA'c hbound
  have hsqrt : Real.sqrt (c / R) = Real.sqrt c / Real.sqrt R := Real.sqrt_div hc.le R
  rw [hsqrt] at hkey
  have hbud : 0 ≤ ‖A R‖ + ‖A T‖ + ∫ t in T..R, ‖A' t‖ := by
    have : 0 ≤ ∫ t in T..R, ‖A' t‖ :=
      intervalIntegral.integral_nonneg hTR (fun x _ => norm_nonneg _)
    linarith [norm_nonneg (A R), norm_nonneg (A T)]
  have hcR : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hRR : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
  have hrw : 32 * (‖A R‖ + ‖A T‖ + ∫ t in T..R, ‖A' t‖) / (Real.sqrt c / Real.sqrt R)
      = 32 * (‖A R‖ + ‖A T‖ + ∫ t in T..R, ‖A' t‖) * Real.sqrt R / Real.sqrt c := by
    field_simp
  rwa [hrw] at hkey

/-- **The bare log-chirp bound.**  With unit amplitude the budget is `2`, so the estimate reads
`‖∫_T^R exp(i c t log t)‖ ≤ 64 √R/√c`.  On `[T, 2T]` this makes the normalized average
`O((cT)^{-1/2})`, uniformly in `c`. -/
theorem norm_integral_logChirp_const_le {c T R : ℝ} (hc : 0 < c) (hT : 0 < T) (hTR : T ≤ R) :
    ‖∫ t in T..R, Complex.exp (Complex.I * ((c * (t * Real.log t) : ℝ) : ℂ))‖
      ≤ 64 * Real.sqrt R / Real.sqrt c := by
  have h := norm_integral_logChirp_le (A := fun _ => (1 : ℂ)) (A' := fun _ => (0 : ℂ))
    hc hT hTR (fun x _ => hasDerivAt_const x 1) continuousOn_const
  rw [show (64 : ℝ) = 32 * (1 + 1) by norm_num]
  simpa using h

end

end RHTower

namespace RHTower

noncomputable section

open MeasureTheory Set Complex

/-- **The sharp log-chirp bound away from the stationary point.**  For `T ≥ 1` the phase derivative
`c(log t + 1)` is bounded below by `c(log T + 1)` and increasing, so the *first*-derivative test
applies and gives `8/(c(log T + 1))` — far stronger than the second-derivative bound
`64 √R/√c` once `R` is large, since it does not grow with the length of the interval.

This is the form that appears as the geometric side of the characteristic-function method: with
`c = k d_F / 2π` it gives `O(1/(k d_F log T))` on `[T, R]`, uniformly in `k`. -/
theorem norm_integral_logChirp_const_le_of_one_le {c T R : ℝ} (hc : 0 < c) (hT : 1 ≤ T)
    (hTR : T ≤ R) :
    ‖∫ t in T..R, Complex.exp (Complex.I * ((c * (t * Real.log t) : ℝ) : ℂ))‖
      ≤ 8 / (c * (Real.log T + 1)) := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlam : 0 < c * (Real.log T + 1) := by positivity
  have hpos : ∀ x ∈ Icc T R, 0 < x := fun x hx => hT0.trans_le hx.1
  have hφ : ∀ x ∈ Icc T R,
      HasDerivAt (fun t : ℝ => c * (t * Real.log t)) (c * (Real.log x + 1)) x := by
    intro x hx
    have hx0 : 0 < x := hpos x hx
    have h1 : HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x := by
      have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0.ne')
      simpa [mul_inv_cancel₀ hx0.ne'] using! h
    exact h1.const_mul c
  have hφ' : ∀ x ∈ Icc T R, HasDerivAt (fun t : ℝ => c * (Real.log t + 1)) (c / x) x := by
    intro x hx
    have hx0 : 0 < x := hpos x hx
    have h := ((Real.hasDerivAt_log hx0.ne').add_const 1).const_mul c
    simpa [div_eq_mul_inv] using h
  have hφ''c : ContinuousOn (fun t : ℝ => c / t) (Icc T R) :=
    continuousOn_const.div continuousOn_id (fun x hx => (hpos x hx).ne')
  have hnn : ∀ x ∈ Icc T R, 0 ≤ c / x := fun x hx => (div_pos hc (hpos x hx)).le
  have hbound : ∀ x ∈ Icc T R, c * (Real.log T + 1) ≤ |c * (Real.log x + 1)| := by
    intro x hx
    have hlogx : Real.log T ≤ Real.log x :=
      Real.log_le_log hT0 hx.1
    have hle : c * (Real.log T + 1) ≤ c * (Real.log x + 1) := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    exact hle
  have h := firstDerivTestOn (A := fun _ => (1 : ℂ)) (A' := fun _ => (0 : ℂ))
    hTR hlam hφ hφ' hφ''c (fun x _ => hasDerivAt_const x 1) continuousOn_const hnn hbound
  rw [show (8 : ℝ) = 4 * (1 + 1) by norm_num]
  simpa using h

end

end RHTower
