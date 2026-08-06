import GaloisForLFunctions.RHTower.Sieve.DirichletBlockTrivialBound

/-!
# The two-regime shape of the partial sum

Below the point where the derivative test starts to pay, the Dirichlet sum on the line `Re s = 1` is
controlled by the harmonic bound alone; above it, block by block, by whatever per-block bound the
schedule supplies.  Splitting there gives the shape the Littlewood estimate is built from:

```text
‖∑_{n < C·2^R} n^(-1-it)‖  ≤  (1 + log (C-1))  +  ∑_{r < R} b r,
```

with the whole harmonic contribution collapsed into the single term `log (C-1)`.  The head bound and
the trivial block bounds have already merged: no telescoping over the low blocks is needed, because
the harmonic bound over the low range is applied once, to the whole range.
-/

namespace RHTower.Sieve

open Finset

/-- **Two-regime bound.**  A single harmonic term for everything below `C`, plus one term per
dyadic block above it. -/
theorem norm_dirichlet_partial_of_blockBound {t : ℝ} {C R : ℕ} (hC : 1 ≤ C) (b : ℕ → ℝ)
    (hb : ∀ r < R,
      ‖∑ n ∈ Finset.Ico (C * 2 ^ r) (C * 2 ^ (r + 1)),
          (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ ≤ b r) :
    ‖∑ n ∈ Finset.Ico 1 (C * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((C - 1 : ℕ) : ℝ)) + ∑ r ∈ Finset.range R, b r := by
  have hCle : C ≤ C * 2 ^ R := by
    calc C = C * 1 := (Nat.mul_one C).symm
      _ ≤ C * 2 ^ R := Nat.mul_le_mul_left C Nat.one_le_two_pow
  have hsplit :
      (∑ n ∈ Finset.Ico 1 C, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)))
        + (∑ n ∈ Finset.Ico C (C * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)))
      = ∑ n ∈ Finset.Ico 1 (C * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)) :=
    Finset.sum_Ico_consecutive _ hC hCle
  rw [← hsplit]
  refine le_trans (norm_add_le _ _) ?_
  exact add_le_add (norm_dirichlet_head_le hC t)
    (dirichlet_tail_dyadic_of_blockBound b hb)

/-- **Two-regime bound with the split point named separately.**  Everything below `A · 2^S` is
harmonic; the blocks from `S` to `R` carry their own bounds. -/
theorem norm_dirichlet_partial_two_regime {t : ℝ} {A S R : ℕ} (hA : 1 ≤ A) (hSR : S ≤ R)
    (b : ℕ → ℝ)
    (hb : ∀ r, S ≤ r → r < R →
      ‖∑ n ∈ Finset.Ico (A * 2 ^ r) (A * 2 ^ (r + 1)),
          (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ ≤ b r) :
    ‖∑ n ∈ Finset.Ico 1 (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((A * 2 ^ S - 1 : ℕ) : ℝ)) + ∑ r ∈ Finset.Ico S R, b r := by
  have hC : 1 ≤ A * 2 ^ S := by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ S := Nat.mul_le_mul hA Nat.one_le_two_pow
  have hpow : A * 2 ^ S * 2 ^ (R - S) = A * 2 ^ R := by
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  have hshift : ∀ j, A * 2 ^ S * 2 ^ (j + 1) = A * 2 ^ (S + j + 1) := by
    intro j
    rw [mul_assoc, ← pow_add, Nat.add_assoc]
  have hshift0 : ∀ j, A * 2 ^ S * 2 ^ j = A * 2 ^ (S + j) := by
    intro j
    rw [mul_assoc, ← pow_add]
  have hmain := norm_dirichlet_partial_of_blockBound (t := t) (C := A * 2 ^ S) (R := R - S) hC
    (fun j => b (S + j)) (fun j hj => by
      have hjR : S + j < R := by omega
      rw [hshift0 j, hshift j]
      exact hb (S + j) (by omega) hjR)
  have heq : ∑ r ∈ Finset.range (R - S), b (S + r) = ∑ r ∈ Finset.Ico S R, b r :=
    (Finset.sum_Ico_eq_sum_range b S R).symm
  rw [hpow, heq] at hmain
  exact hmain

end RHTower.Sieve
