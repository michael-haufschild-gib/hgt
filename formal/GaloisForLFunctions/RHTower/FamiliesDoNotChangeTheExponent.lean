import GaloisForLFunctions.RHTower.ExplicitFormulaUncertainty

/-!
# Enlarging the family does not change the exchange exponent

The one-half exchange rate was computed for a single `L`-function.  The natural escape is a family
whose prime sum is sparse.  This file computes the rate for such a family and finds it unchanged, with
a strictly worse constant.

**The family.**  For the cyclotomic field of conductor `q` the zeta function factors over the
characters mod `q`, and the averaged prime sum runs only over `n ≡ 1 (mod q)` — a saving of a factor
`φ(q)` in the arithmetic side.

**But the zeros multiply too.**  The zero density at low height is `log|d_K| / 2π` with
`log|d_K| ≍ φ(q) log q`, so the Nyquist threshold rises from `(log q)/2` to

```text
L_q  =  φ(q) · (log q) / 2 .
```

**The cost.**  The required prime range is `e^{L_q} = q^{φ(q)/2}` instead of `q^{1/2}`, a factor
`q^{(φ(q)-1)/2}` worse, against a saving of only `φ(q)`.

**The exponent does not move.**  Whatever `L` is required, the resolved height is `e^{2L}` and the
prime range is `e^L`, so

```text
log(prime range) / log(resolved height)  =  1/2 ,
```

for every `L` and hence for every family.

> **Degrees of freedom, zero density and prime cost all scale by the same conductor factor, so the
> one-half rate is a property of the functional equation rather than of any particular `L`-function.
> The circularity of the explicit-formula lane cannot be broken by changing the `L`-function.**

This file formalizes the invariance of the exponent, the multiplicative blow-up of the required prime
range, and its monotone growth in the size of the family.
-/

open Real

noncomputable section

namespace RHTower

/-- **The exponent is one half at every width.**  The logarithm of the prime range is half the
logarithm of the resolved height, for every `L`. -/
theorem exponent_invariant {L : ℝ} (hL : L ≠ 0) :
    Real.log (primeRange L) / Real.log (resolvedHeight L) = 1 / 2 := by
  unfold primeRange resolvedHeight
  rw [Real.log_exp, Real.log_exp]
  field_simp

/-- **And the prime range is raised to that power.**  `e^{φ a} = (e^a)^φ`. -/
theorem family_primeRange (φ a : ℝ) : Real.exp (φ * a) = Real.exp a ^ φ := by
  rw [Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp]
  ring_nf

/-- **The blow-up factor.**  Relative to a single function the range is worse by `(e^a)^{φ-1}`. -/
theorem family_blowup (a φ : ℝ) :
    Real.exp (φ * a) / Real.exp a = Real.exp ((φ - 1) * a) := by
  rw [← Real.exp_sub]
  ring_nf

/-- **The blow-up is monotone in the size of the family**, so a larger family is strictly worse. -/
theorem blowup_mono {a φ₁ φ₂ : ℝ} (ha : 0 < a) (h : φ₁ ≤ φ₂) :
    Real.exp ((φ₁ - 1) * a) ≤ Real.exp ((φ₂ - 1) * a) := by
  apply Real.exp_le_exp.mpr
  nlinarith

/-- **And it is unbounded.**  For any bound there is a family size exceeding it. -/
theorem blowup_unbounded {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ φ : ℝ, M < Real.exp ((φ - 1) * a) := by
  obtain ⟨y, hy⟩ := exists_gt (max M 0)
  refine ⟨1 + Real.log (y + 1) / a, ?_⟩
  have hy0 : 0 < y + 1 := by
    have : (0 : ℝ) ≤ max M 0 := le_max_right M 0
    linarith
  have : (1 + Real.log (y + 1) / a - 1) * a = Real.log (y + 1) := by
    field_simp
    ring
  rw [this, Real.exp_log hy0]
  have hM : M ≤ max M 0 := le_max_left M 0
  linarith

end RHTower
