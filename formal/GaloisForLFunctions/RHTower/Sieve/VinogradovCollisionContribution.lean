import GaloisForLFunctions.RHTower.Sieve.VinogradovCollisionBlock

/-!
# Vinogradov mean value: contribution of colliding leading blocks

Let `J_{b,k}(N)` count pairs of `b`-tuples in `[0, N)` with equal power sums of orders `1..k`
(`VinogradovDiagonalSolution N b k`). Split a `(k + b)`-tuple into a leading `k`-block and a tail of
length `b`. This module bounds the solutions modulo `q` whose two leading blocks both have a repeated
entry: there are at most `(k^2 - k) N^(k-1)` such blocks, and for each fixed pair of blocks the tails
contribute at most the fibre energy of the tail power-sum signature. When `q > 2 b N^k`, that energy
equals `J_{b,k}(N)`.

## Main results

- `card_vinogradovCollidingBlockCompletion_le_energy`: the colliding completions number at most
  `((k^2 - k) N^(k-1))^2` times the fibre energy of the length-`b` power signature modulo `q`.
- `card_vinogradovCollidingBlockCompletion_le_moment`: if `N ≠ 0` and `2 b N^k < q`, they number at
  most `((k^2 - k) N^(k-1))^2 · J_{b,k}(N)`.
- `full_vinogradovMomentModulus_large_for_tail`: the full modulus `2 (k + b) N^k + 1` exceeds `2 b N^k`.
- `card_vinogradovCollidingBlockCompletion_le_tailMoment`: the bound by `J_{b,k}(N)` at the full modulus.

## Hypotheses

Unconditional. The moment form assumes `N ≠ 0` and `2 b N^k < q`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The `k`-tuples in `[0, N)` with at least one repeated entry. -/
abbrev VinogradovNoninjectiveBlock (N k : ℕ) :=
  {x : Fin k → Fin N // ¬Function.Injective x}

/-- Pairs of non-injective leading `k`-blocks together with tails `u, v` of length `b` such that the
concatenated `(k + b)`-tuples have the same first `k` power sums modulo `q`. -/
abbrev VinogradovCollidingBlockCompletion (q N k b : ℕ) :=
  Σ xy : VinogradovNoninjectiveBlock N k × VinogradovNoninjectiveBlock N k,
    {uv : (Fin b → Fin N) × (Fin b → Fin N) //
      vinogradovPowerSignatureMod q k (Fin.append xy.1.1 uv.1) =
        vinogradovPowerSignatureMod q k (Fin.append xy.2.1 uv.2)}

/-- The number of colliding completions is at most `((k^2 - k) N^(k-1))^2` times the fibre energy of
the power-sum signature modulo `q` on tails of length `b`. -/
theorem card_vinogradovCollidingBlockCompletion_le_energy
    {q N k b : ℕ} [NeZero q] :
    Fintype.card (VinogradovCollidingBlockCompletion q N k b) ≤
      ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
        finiteFiberEnergy
          (vinogradovPowerSignatureMod q k :
            (Fin b → Fin N) → Fin k → ZMod q) := by
  rw [Fintype.card_sigma]
  calc
    (∑ xy : VinogradovNoninjectiveBlock N k × VinogradovNoninjectiveBlock N k,
        Fintype.card {uv : (Fin b → Fin N) × (Fin b → Fin N) //
          vinogradovPowerSignatureMod q k (Fin.append xy.1.1 uv.1) =
            vinogradovPowerSignatureMod q k (Fin.append xy.2.1 uv.2)}) ≤
        ∑ _xy : VinogradovNoninjectiveBlock N k × VinogradovNoninjectiveBlock N k,
          finiteFiberEnergy
            (vinogradovPowerSignatureMod q k :
              (Fin b → Fin N) → Fin k → ZMod q) := by
      apply Finset.sum_le_sum
      intro xy _
      exact card_vinogradovFixedBlocks_le_finiteFiberEnergy xy.1.1 xy.2.1
    _ = Fintype.card (VinogradovNoninjectiveBlock N k ×
          VinogradovNoninjectiveBlock N k) *
        finiteFiberEnergy
          (vinogradovPowerSignatureMod q k :
            (Fin b → Fin N) → Fin k → ZMod q) := by simp
    _ ≤ ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
        finiteFiberEnergy
          (vinogradovPowerSignatureMod q k :
            (Fin b → Fin N) → Fin k → ZMod q) := by
      apply Nat.mul_le_mul_right
      rw [Fintype.card_prod, pow_two]
      exact Nat.mul_le_mul
        (card_noninjective_tuples_le N k)
        (card_noninjective_tuples_le N k)

/-- Assuming `N ≠ 0` and `2 b N^k < q`, the colliding completions number at most
`((k^2 - k) N^(k-1))^2 · J_{b,k}(N)`. -/
theorem card_vinogradovCollidingBlockCompletion_le_moment
    {q N k b : ℕ} [NeZero q] (hN : N ≠ 0)
    (hq : 2 * b * N ^ k < q) :
    Fintype.card (VinogradovCollidingBlockCompletion q N k b) ≤
      ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
        Fintype.card (VinogradovDiagonalSolution N b k) := by
  calc
    Fintype.card (VinogradovCollidingBlockCompletion q N k b) ≤
        ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
          finiteFiberEnergy
            (vinogradovPowerSignatureMod q k :
              (Fin b → Fin N) → Fin k → ZMod q) :=
      card_vinogradovCollidingBlockCompletion_le_energy
    _ = ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
        Fintype.card (VinogradovDiagonalSolution N b k) := by
      rw [← vinogradovModularMomentAt_eq_card_of_large hN hq]
      rfl

/-- The modulus `vinogradovMomentModulus N (k + b) k = 2 (k + b) N^k + 1` exceeds `2 b N^k`. -/
theorem full_vinogradovMomentModulus_large_for_tail
    {N k b : ℕ} :
    2 * b * N ^ k < vinogradovMomentModulus N (k + b) k := by
  unfold vinogradovMomentModulus
  apply Nat.lt_succ_of_le
  exact Nat.mul_le_mul_right (N ^ k)
    (Nat.mul_le_mul_left 2 (Nat.le_add_left b k))

/-- For `N ≠ 0`, at the modulus attached to length `k + b`, the colliding completions number at most
`((k^2 - k) N^(k-1))^2 · J_{b,k}(N)`. -/
theorem card_vinogradovCollidingBlockCompletion_le_tailMoment
    {N k b : ℕ} (hN : N ≠ 0) :
    Fintype.card (VinogradovCollidingBlockCompletion
      (vinogradovMomentModulus N (k + b) k) N k b) ≤
      ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
        Fintype.card (VinogradovDiagonalSolution N b k) :=
  card_vinogradovCollidingBlockCompletion_le_moment hN
    full_vinogradovMomentModulus_large_for_tail

end

end RHTower.Sieve
