import GaloisForLFunctions.RHTower.Sieve.VinogradovCollisionBlock

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

abbrev VinogradovNoninjectiveBlock (N k : ℕ) :=
  {x : Fin k → Fin N // ¬Function.Injective x}

abbrev VinogradovCollidingBlockCompletion (q N k b : ℕ) :=
  Σ xy : VinogradovNoninjectiveBlock N k × VinogradovNoninjectiveBlock N k,
    {uv : (Fin b → Fin N) × (Fin b → Fin N) //
      vinogradovPowerSignatureMod q k (Fin.append xy.1.1 uv.1) =
        vinogradovPowerSignatureMod q k (Fin.append xy.2.1 uv.2)}

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

theorem full_vinogradovMomentModulus_large_for_tail
    {N k b : ℕ} :
    2 * b * N ^ k < vinogradovMomentModulus N (k + b) k := by
  unfold vinogradovMomentModulus
  apply Nat.lt_succ_of_le
  exact Nat.mul_le_mul_right (N ^ k)
    (Nat.mul_le_mul_left 2 (Nat.le_add_left b k))

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
