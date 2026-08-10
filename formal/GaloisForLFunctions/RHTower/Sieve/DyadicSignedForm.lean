import GaloisForLFunctions.RHTower.Sieve.OverlapExact

/-!
# The signed quadratic form

Every term of `dyadicMeanSquare` is a square, so enlarging the range of starting points only
increases it.  Enlarging it far enough to contain every start that sees the support of `f` turns the
exact kernel into Gallagher's `(ℓ − |m − n|)₊` at every pair that contributes, and leaves

```text
dyadicMeanSquare f ℓ A B ≤ ∑_{m, n} f(m)·f(n)·(ℓ − |m − n|)₊ ,
```

**with the signs intact**.  That is the point: the same inequality with `|f(m)|·|f(n)|` is the
trivial bound and can prove nothing, whereas this form is the one `gallagher_identity` evaluates as
`∫ ‖logWindowSum‖²`, where the cancellation lives.

The price of enlarging the range is nothing at all — the discarded starting points contribute
squares, which only help.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- Enlarging the range of starting points increases the mean square. -/
theorem dyadicMeanSquare_mono (f : ℕ → ℝ) (ℓ : ℕ) {A B A' B' : ℕ} (h1 : A' ≤ A) (h2 : B ≤ B') :
    dyadicMeanSquare f ℓ A B ≤ dyadicMeanSquare f ℓ A' B' := by
  rw [dyadicMeanSquare, dyadicMeanSquare]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc h1 h2) ?_
  intro z _ _
  exact fixedWindowSq_nonneg f ℓ z

/-- **The full-range mean square is the signed Gallagher form.** -/
theorem dyadicMeanSquare_full_eq (f : ℕ → ℝ) {ℓ M : ℕ} (hℓ : 1 ≤ ℓ)
    (hsupp : ∀ b : ℕ, f b ≠ 0 → ℓ ≤ b ∧ b ≤ M) :
    dyadicMeanSquare f ℓ 0 M
      = ∑ m ∈ Finset.Icc 1 (M + ℓ), ∑ n ∈ Finset.Icc 1 (M + ℓ),
          f m * f n * (((min m n + ℓ) - max m n : ℕ) : ℝ) := by
  classical
  rw [dyadicMeanSquare_eq_count f hℓ 0 M]
  simp only [Nat.zero_add]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hm hn
  by_cases hfm : f m = 0
  · rw [hfm]; ring
  by_cases hfn : f n = 0
  · rw [hfn]; ring
  obtain ⟨hmℓ, hmM⟩ := hsupp m hfm
  obtain ⟨hnℓ, hnM⟩ := hsupp n hfn
  congr 2
  refine overlap_card_interior ℓ 0 M (by omega) (by omega) ?_ (by omega) (by omega)
  omega

/-- **The signed comparison.**  The dyadic mean square is dominated by the full quadratic form. -/
theorem dyadicMeanSquare_le_signed_form (f : ℕ → ℝ) {ℓ A B M : ℕ} (hℓ : 1 ≤ ℓ)
    (hBM : B ≤ M) (hsupp : ∀ b : ℕ, f b ≠ 0 → ℓ ≤ b ∧ b ≤ M) :
    dyadicMeanSquare f ℓ A B
      ≤ ∑ m ∈ Finset.Icc 1 (M + ℓ), ∑ n ∈ Finset.Icc 1 (M + ℓ),
          f m * f n * (((min m n + ℓ) - max m n : ℕ) : ℝ) := by
  rw [← dyadicMeanSquare_full_eq f hℓ hsupp]
  exact dyadicMeanSquare_mono f ℓ (Nat.zero_le A) hBM

end RHTower.Sieve

end
