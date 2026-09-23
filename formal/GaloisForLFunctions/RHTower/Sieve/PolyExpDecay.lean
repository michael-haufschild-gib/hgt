import GaloisForLFunctions.RHTower.Sieve.EdgeBoundAtChoice

/-!
# Polynomial against exponential

The last comparison in the contour argument.  Every term of the bound is a polynomial in
`t = (log x)^{1/10}` times `exp(-κt)` with `κ > 0`, and the elementary fact below settles all of
them at once.

The polynomials appearing are `(1 + a t⁹)` and `(1 + a t⁹)(b + ct)`, so the version for a general
product of that shape is stated as well.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **A power against a decaying exponential.** -/
theorem tendsto_pow_mul_exp_neg_mul (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t : ℝ => t ^ n * Real.exp (-(κ * t))) atTop (𝓝 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hmul : Tendsto (fun t : ℝ => κ * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hκ tendsto_id
  have hcomp : Tendsto (fun t : ℝ => (κ * t) ^ n * Real.exp (-(κ * t))) atTop (𝓝 0) :=
    hbase.comp hmul
  have hscale : Tendsto (fun t : ℝ => (κ ^ n)⁻¹ * ((κ * t) ^ n * Real.exp (-(κ * t))))
      atTop (𝓝 0) := by
    simpa using hcomp.const_mul (κ ^ n)⁻¹
  refine hscale.congr fun t => ?_
  rw [mul_pow]
  field_simp

/-- **A degree-nine polynomial against a decaying exponential.** -/
theorem tendsto_poly9_mul_exp_neg {a κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t : ℝ => (1 + a * t ^ (9 : ℕ)) * Real.exp (-(κ * t))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => t ^ (0 : ℕ) * Real.exp (-(κ * t))) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_mul 0 hκ
  have h9 : Tendsto (fun t : ℝ => t ^ (9 : ℕ) * Real.exp (-(κ * t))) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_mul 9 hκ
  have hsum : Tendsto (fun t : ℝ =>
      t ^ (0 : ℕ) * Real.exp (-(κ * t)) + a * (t ^ (9 : ℕ) * Real.exp (-(κ * t))))
      atTop (𝓝 (0 + a * 0)) := h0.add (h9.const_mul a)
  simp only [add_zero, mul_zero] at hsum
  refine hsum.congr fun t => ?_
  ring

/-- **The full polynomial shape against a decaying exponential.** -/
theorem tendsto_polyEdge_mul_exp_neg {a b c κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t : ℝ => (1 + a * t ^ (9 : ℕ)) * (b + c * t) * Real.exp (-(κ * t)))
      atTop (𝓝 0) := by
  have h0 := tendsto_pow_mul_exp_neg_mul 0 hκ
  have h1 := tendsto_pow_mul_exp_neg_mul 1 hκ
  have h9 := tendsto_pow_mul_exp_neg_mul 9 hκ
  have h10 := tendsto_pow_mul_exp_neg_mul 10 hκ
  have hsum : Tendsto (fun t : ℝ =>
      b * (t ^ (0 : ℕ) * Real.exp (-(κ * t)))
        + c * (t ^ (1 : ℕ) * Real.exp (-(κ * t)))
        + a * b * (t ^ (9 : ℕ) * Real.exp (-(κ * t)))
        + a * c * (t ^ (10 : ℕ) * Real.exp (-(κ * t))))
      atTop (𝓝 (b * 0 + c * 0 + a * b * 0 + a * c * 0)) :=
    (((h0.const_mul b).add (h1.const_mul c)).add (h9.const_mul (a * b))).add
      (h10.const_mul (a * c))
  simp only [mul_zero, add_zero] at hsum
  refine hsum.congr fun t => ?_
  ring

end RHTower.Sieve
