import GaloisForLFunctions.HTGeometry.TunableStep

/-!
# The tuned chain still covers only a bounded region

A tunable step with parameters `(ε, δ)` multiplies the kernel bounds by `√((1+ε)/(1−δ))` and, by the
smallness condition `4(1+ε⁻¹)D²S²P² ≤ δ`, admits a displacement with `D² ≲ δ·ε` for small `ε` — so
`D ≲ √(δε)`, not `√ε`.

Bounded accumulated growth forces `∑ εₖ < ∞` and `∑ δₖ < ∞`.  But `√(δε) ≤ (δ+ε)/2`, so the total
displacement is at most `(∑ δₖ + ∑ εₖ)/2`, which is then finite.  **No choice of parameters lets a
chain of tunable steps travel arbitrarily far while keeping the bounds under control.**

The arithmetic mean--geometric mean inequality below is the whole obstruction.
-/

open scoped BigOperators

namespace HTGeometry

/-- **AM--GM.**  A geometric mean is at most the arithmetic mean. -/
theorem sqrt_mul_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have hnn : 0 ≤ a * b := mul_nonneg ha hb
  have hsq : Real.sqrt (a * b) ^ (2 : ℕ) = a * b := Real.sq_sqrt hnn
  have hmid : (0:ℝ) ≤ (a + b) / 2 := by linarith
  nlinarith [Real.sqrt_nonneg (a * b), hsq, sq_nonneg (a - b), sq_nonneg (Real.sqrt (a * b))]

/-- **The total displacement of a tuned chain is bounded by the parameter sums.**  Summable
parameters — which bounded growth requires — give a finite total reach. -/
theorem sum_sqrt_mul_le (n : ℕ) {d e : ℕ → ℝ} (hd : ∀ k, 0 ≤ d k) (he : ∀ k, 0 ≤ e k) :
    ∑ k ∈ Finset.range n, Real.sqrt (d k * e k)
      ≤ (∑ k ∈ Finset.range n, d k + ∑ k ∈ Finset.range n, e k) / 2 := by
  have hterm : ∀ k ∈ Finset.range n,
      Real.sqrt (d k * e k) ≤ (d k + e k) / 2 :=
    fun k _ => sqrt_mul_le_add_div_two (hd k) (he k)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_div, Finset.sum_add_distrib]

end HTGeometry
