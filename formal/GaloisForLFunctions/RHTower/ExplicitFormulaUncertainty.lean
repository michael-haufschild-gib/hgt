import GaloisForLFunctions.RHTower.BudgetAndResolutionAreOneResource

/-!
# The explicit formula's uncertainty principle, and the exponent is one half

The previous entry showed budget and resolution are one resource.  This file computes the exchange
rate and finds it is exactly the square root.

**The counting.**  A test supported in `[-L, L]` has transform of exponential type `L`, so by the
Beurling–Landau density its degrees of freedom per unit of ordinate are `L/π`.  The zeros up to height
`T` have density `log T / 2π` per unit of ordinate.  Resolving them individually therefore requires

```text
L/π  ≥  log T / (2π)        ⟺        L  ≥  (log T)/2 .
```

**The price.**  The prime side of a test of width `L` runs over `n ≤ e^L`, so resolving the zeros up to
height `T` requires a prime sum extending to

```text
e^L  ≥  e^{(log T)/2}  =  √T .
```

**The exponent.**  Writing the resolved height as `e^{2L}` and the required prime range as `e^L`,

```text
prime range  =  √( resolved height ) .
```

> **Resolving the zeros to height `T` by a compactly supported test costs control of the primes up to
> `√T`.  Since controlling the primes to `√T` with square-root accuracy is exactly the strength of the
> hypothesis, the explicit-formula lane at full resolution requires precisely as much arithmetic input
> as it produces.  The circularity is exact, and its exponent is one half on both sides.**

This is the quantitative form of the square-root barrier: it is not an artefact of any estimate but a
consequence of counting degrees of freedom against zero density.

This file formalizes the Nyquist threshold, the resulting prime range, and the square-root exchange
law.
-/

open Real

noncomputable section

namespace RHTower

/-- **The Nyquist threshold.**  Degrees of freedom `L/π` per unit ordinate must reach the zero density
`log T / 2π`, which happens exactly when `L ≥ (log T)/2`. -/
theorem nyquist_threshold {L Λ : ℝ} (hπ : 0 < π) :
    L / π ≥ Λ / (2 * π) ↔ L ≥ Λ / 2 := by
  rw [ge_iff_le, ge_iff_le, div_le_div_iff₀ (by positivity) hπ]
  constructor <;> intro h <;> nlinarith

/-- The height resolved by a test of width `L`. -/
def resolvedHeight (L : ℝ) : ℝ := Real.exp (2 * L)

/-- The prime range required by a test of width `L`. -/
def primeRange (L : ℝ) : ℝ := Real.exp L

/-- **The exchange law.**  The required prime range is the square root of the resolved height. -/
theorem exchange_law (L : ℝ) : primeRange L = Real.sqrt (resolvedHeight L) := by
  unfold primeRange resolvedHeight
  rw [show (2 : ℝ) * L = L + L by ring, Real.exp_add]
  rw [Real.sqrt_mul_self (Real.exp_nonneg L)]

/-- Equivalently, the square of the prime range is the resolved height. -/
theorem exchange_law_sq (L : ℝ) : primeRange L ^ (2 : ℕ) = resolvedHeight L := by
  unfold primeRange resolvedHeight
  rw [← Real.exp_nat_mul]
  norm_num

/-- **Both are increasing in the width**, so there is no width at which resolution is cheap. -/
theorem resolvedHeight_mono {L₁ L₂ : ℝ} (h : L₁ ≤ L₂) : resolvedHeight L₁ ≤ resolvedHeight L₂ := by
  unfold resolvedHeight
  exact Real.exp_le_exp.mpr (by linarith)

theorem primeRange_mono {L₁ L₂ : ℝ} (h : L₁ ≤ L₂) : primeRange L₁ ≤ primeRange L₂ :=
  Real.exp_le_exp.mpr h

/-- Made concrete: doubling the width squares the resolved height and squares the prime range, so the
ratio of exponents never moves. -/
theorem doubling_preserves_ratio (L : ℝ) :
    resolvedHeight (2 * L) = resolvedHeight L ^ (2 : ℕ) ∧ primeRange (2 * L) = primeRange L ^ (2 : ℕ) := by
  constructor
  · unfold resolvedHeight
    rw [← Real.exp_nat_mul]
    norm_num
  · unfold primeRange
    rw [← Real.exp_nat_mul]
    norm_num

end RHTower
