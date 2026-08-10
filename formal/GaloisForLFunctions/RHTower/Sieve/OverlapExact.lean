import GaloisForLFunctions.RHTower.Sieve.AdditiveLogMatching

/-!
# The overlap kernel, exactly

`overlap_card_le` bounds the kernel; a signed argument needs its value.  The starting points that
serve both `m` and `n` are exactly an interval:

```text
{ z ∈ [A,B] : m, n ∈ (z, z+ℓ] } = [ max(A, max(m,n) − ℓ), min(B, min(m,n) − 1) ] .
```

Both constraints are one-sided — `z + 1 ≤ min(m,n)` from below on the windows' right ends, and
`max(m,n) ≤ z + ℓ` from above on their left ends — so the admissible set is the intersection of two
rays with `[A,B]`, and its cardinality is an explicit truncated difference rather than a bound.

This matters because the pair expansion `dyadicMeanSquare_eq_count` is an identity with *signed*
products `f(m)·f(n)`.  Replacing them by `|f(m)|·|f(n)|`, as `dyadicMeanSquare_le_band` does,
destroys the cancellation and can only return the trivial size; any route to the
Matomäki–Radziwiłł estimate has to keep the signs, hence has to work with the kernel's value.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The admissible starting points form an interval.** -/
theorem overlap_filter_eq (ℓ A B : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ((Finset.Icc A B).filter
        (fun z => m ∈ Finset.Icc (z + 1) (z + ℓ) ∧ n ∈ Finset.Icc (z + 1) (z + ℓ)))
      = Finset.Icc (max A (max m n - ℓ)) (min B (min m n - 1)) := by
  classical
  ext z
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hA, hB⟩, ⟨hm1, hm2⟩, ⟨hn1, hn2⟩⟩
    omega
  · rintro ⟨h1, h2⟩
    omega

/-- The kernel's exact value. -/
theorem overlap_card_eq (ℓ A B : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ((Finset.Icc A B).filter
        (fun z => m ∈ Finset.Icc (z + 1) (z + ℓ)
          ∧ n ∈ Finset.Icc (z + 1) (z + ℓ))).card
      = (min B (min m n - 1) + 1) - max A (max m n - ℓ) := by
  rw [overlap_filter_eq ℓ A B hm hn, Nat.card_Icc]

/-- On the interior of the range the kernel is the full overlap `(ℓ − |m − n|)₊`. -/
theorem overlap_card_interior (ℓ A B : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hℓ : ℓ ≤ max m n) (hlow : A ≤ max m n - ℓ) (hhigh : min m n - 1 ≤ B) :
    ((Finset.Icc A B).filter
        (fun z => m ∈ Finset.Icc (z + 1) (z + ℓ)
          ∧ n ∈ Finset.Icc (z + 1) (z + ℓ))).card
      = (min m n + ℓ) - max m n := by
  rw [overlap_card_eq ℓ A B hm hn]
  omega

end RHTower.Sieve

end
