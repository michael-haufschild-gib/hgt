import GaloisForLFunctions.RHTower.Sieve.AbelInequality

/-!
# Abel's inequality on a tail

Restricting the weighted sum to indices beyond `a` costs only a factor two: the partial sums of the
shifted summand are differences of two original partial sums, so they are capped by `2B`, and the
shifted weight starts at `w a`.  Hence

`|∑_{a ≤ i < n} w i · g i| ≤ 2 B · w a`.

For a weight like `w d = 1/(d+1)` this is the decisive gain — the tail bound carries the factor
`w a = 1/(a+1)`, which is what makes the harmonic-weighted sine sum bounded *uniformly* once the
range is split at `a ≍ 1/|θ|`.  Below that split the terms are individually small, above it the
partial sums cancel.
-/

namespace RHTower.Sieve

open Finset

/-- Shifted partial sums are differences of original ones. -/
theorem sum_range_shift (g : ℕ → ℝ) (a K : ℕ) :
    ∑ k ∈ Finset.range K, g (a + k)
      = (∑ j ∈ Finset.range (a + K), g j) - ∑ j ∈ Finset.range a, g j := by
  rw [Finset.sum_range_add]
  ring

/-- **Abel's inequality on a tail.** -/
theorem abs_sum_Ico_mul_le_of_bounded_partial {g w : ℕ → ℝ} {B : ℝ} (a n : ℕ)
    (hB : ∀ k, |∑ j ∈ Finset.range k, g j| ≤ B)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : ∀ i, w (i + 1) ≤ w i) :
    |∑ i ∈ Finset.Ico a n, w i * g i| ≤ 2 * B * w a := by
  have hreindex : ∑ i ∈ Finset.Ico a n, w i * g i
      = ∑ k ∈ Finset.range (n - a), w (a + k) * g (a + k) := by
    rw [Finset.sum_Ico_eq_sum_range]
  rw [hreindex]
  have hB' : ∀ k, |∑ j ∈ Finset.range k, g (a + j)| ≤ 2 * B := by
    intro k
    rw [sum_range_shift g a k]
    have h1 := hB (a + k)
    have h2 := hB a
    have := abs_sub (∑ j ∈ Finset.range (a + k), g j) (∑ j ∈ Finset.range a, g j)
    linarith
  have hw0' : ∀ i, 0 ≤ w (a + i) := fun i => hw0 (a + i)
  have hwanti' : ∀ i, w (a + (i + 1)) ≤ w (a + i) := by
    intro i
    have : a + (i + 1) = (a + i) + 1 := by omega
    rw [this]
    exact hwanti (a + i)
  have hmain := abs_sum_mul_le_of_bounded_partial (g := fun k => g (a + k))
    (w := fun k => w (a + k)) (B := 2 * B) (n - a) hB' hw0' hwanti'
  simpa using hmain

/-- **Harmonic-weighted sine sums, tail form.**  Composing the Dirichlet kernel bound with Abel. -/
theorem abs_sum_sin_div_le {θ : ℝ} (hθ : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1) (M : ℕ) :
    |∑ d ∈ Finset.range M, (1 / ((d : ℝ) + 1)) * Real.sin ((d : ℝ) * θ)|
      ≤ 1 / |Real.sin (θ / 2)| := by
  have hw0 : ∀ i : ℕ, (0 : ℝ) ≤ 1 / ((i : ℝ) + 1) := by
    intro i
    positivity
  have hwanti : ∀ i : ℕ, (1 : ℝ) / (((i : ℕ) + 1 : ℕ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
    intro i
    have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have h2 : ((i : ℝ) + 1) ≤ (((i + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      linarith
    exact one_div_le_one_div_of_le h1 h2
  have hmain := abs_sum_mul_le_of_bounded_partial
    (g := fun d : ℕ => Real.sin ((d : ℝ) * θ)) (w := fun d : ℕ => 1 / ((d : ℝ) + 1))
    (B := 1 / |Real.sin (θ / 2)|) M (fun k => abs_sum_sin_le hθ k) hw0 hwanti
  simpa using hmain

end RHTower.Sieve
