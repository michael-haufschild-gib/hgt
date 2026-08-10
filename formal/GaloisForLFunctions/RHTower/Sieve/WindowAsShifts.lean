import GaloisForLFunctions.RHTower.Sieve.DyadicSignedForm

/-!
# A window is a sum of translates

The entry point to the Fourier side.  The window of length `ℓ` after `z` is the sum of the `ℓ`
translates of `f`:

```text
∑_{b ∈ (z, z+ℓ]} f(b) = ∑_{j = 1}^{ℓ} f(z + j) .
```

Read as an operator on sequences this is convolution with the indicator of `[1, ℓ]`, so on the
Fourier side the window sum is `F(θ)` times a Dirichlet kernel, and the signed quadratic form of
`DyadicSignedForm` becomes `∫₀¹ |F(θ)|²·|D_ℓ(θ)|²` — the shape in which the large-values machinery
acts.

The identity is a reindexing and costs nothing; it is recorded because every later step uses the
window in this form rather than as an interval sum.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **A window is a sum of translates.** -/
theorem window_eq_sum_shifts (f : ℕ → ℝ) (ℓ z : ℕ) :
    ∑ b ∈ Finset.Icc (z + 1) (z + ℓ), f b = ∑ j ∈ Finset.Icc 1 ℓ, f (z + j) := by
  classical
  refine (Finset.sum_nbij' (fun j => z + j) (fun b => b - z) ?_ ?_ ?_ ?_ ?_).symm
  · intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    omega
  · intro b hb
    rw [Finset.mem_Icc] at hb ⊢
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    omega
  · intro b hb
    rw [Finset.mem_Icc] at hb
    omega
  · intro j _
    rfl

/-- The fixed-length window square, as a square of translates. -/
theorem fixedWindowSq_eq_shifts (f : ℕ → ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (z : ℕ) :
    fixedWindowSq f ℓ z = (∑ j ∈ Finset.Icc 1 ℓ, f (z + j)) ^ 2 := by
  rw [fixedWindowSq_eq f hℓ z, window_eq_sum_shifts f ℓ z]

/-- The dyadic mean square, in translate form. -/
theorem dyadicMeanSquare_eq_shifts (f : ℕ → ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A B : ℕ) :
    dyadicMeanSquare f ℓ A B
      = ∑ z ∈ Finset.Icc A B, (∑ j ∈ Finset.Icc 1 ℓ, f (z + j)) ^ 2 := by
  rw [dyadicMeanSquare]
  exact Finset.sum_congr rfl fun z _ => fixedWindowSq_eq_shifts f hℓ z

end RHTower.Sieve

end
