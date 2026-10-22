import GaloisForLFunctions.RHTower.Sieve.FiniteFiberPartition
import GaloisForLFunctions.RHTower.Sieve.VinogradovCollisionContribution

/-!
# Vinogradov mean value: the collision recurrence

Splits each `(k + b)`-tuple in `[0, N)` into a leading `k`-block and a tail of length `b`, and
partitions the fibre energy of the power-sum signature by whether the leading block is injective.
Combined with the colliding-block bound this gives a recurrence for the Vinogradov mean value:
`J_{k+b,k}(N)` is at most twice the energy restricted to injective leading blocks plus
`((k^2 - k) N^(k-1))^2 J_{b,k}(N)`.

## Main results

- `vinogradovSplitPowerSignature`: power-sum signature modulo `q` of a concatenated pair `(x, u)`.
- `finiteFiberEnergy_vinogradovSplitPowerSignature_eq`: its fibre energy equals that of the signature
  on `(k + b)`-tuples.
- `vinogradov_moment_collision_partition`: the energy is at most twice the sum of the
  injective-block energy and the number of colliding completions.
- `vinogradov_moment_collision_recurrence`: for `N ≠ 0`,
  `J_{k+b,k}(N) ≤ 2 (E_inj + ((k^2 - k) N^(k-1))^2 J_{b,k}(N))`.

## Hypotheses

Unconditional. The recurrence assumes `N ≠ 0`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Power-sum signature modulo `q` (orders `1..k`) of the concatenation of a leading `k`-block and a
tail of length `b`. -/
def vinogradovSplitPowerSignature (q N k b : ℕ) [NeZero q] :
    ((Fin k → Fin N) × (Fin b → Fin N)) → Fin k → ZMod q :=
  fun z => vinogradovPowerSignatureMod q k (Fin.append z.1 z.2)

/-- Splitting a `(k + b)`-tuple into block and tail does not change the fibre energy of the power-sum
signature modulo `q`. -/
theorem finiteFiberEnergy_vinogradovSplitPowerSignature_eq
    {q N k b : ℕ} [NeZero q] :
    finiteFiberEnergy (vinogradovSplitPowerSignature q N k b) =
      finiteFiberEnergy
        (vinogradovPowerSignatureMod q k :
          (Fin (k + b) → Fin N) → Fin k → ZMod q) := by
  let append : ((Fin k → Fin N) × (Fin b → Fin N)) ≃
      (Fin (k + b) → Fin N) := Fin.appendEquiv k b
  let leftSignature := vinogradovSplitPowerSignature q N k b
  let rightSignature : (Fin (k + b) → Fin N) → Fin k → ZMod q :=
    vinogradovPowerSignatureMod q k
  let e : {z : ((Fin k → Fin N) × (Fin b → Fin N)) ×
          ((Fin k → Fin N) × (Fin b → Fin N)) //
        leftSignature z.1 = leftSignature z.2} ≃
      {z : (Fin (k + b) → Fin N) × (Fin (k + b) → Fin N) //
        rightSignature z.1 = rightSignature z.2} :=
    { toFun := fun z => ⟨(append z.1.1, append z.1.2), z.2⟩
      invFun := fun z => ⟨(append.symm z.1.1, append.symm z.1.2), by
        change rightSignature (append (append.symm z.1.1)) =
          rightSignature (append (append.symm z.1.2))
        rw [append.apply_symm_apply, append.apply_symm_apply]
        exact z.2⟩
      left_inv := fun z => Subtype.ext (Prod.ext (append.symm_apply_apply z.1.1)
        (append.symm_apply_apply z.1.2))
      right_inv := fun z => Subtype.ext (Prod.ext (append.apply_symm_apply z.1.1)
        (append.apply_symm_apply z.1.2)) }
  rw [finiteFiberEnergy_eq_card, finiteFiberEnergy_eq_card]
  exact Fintype.card_congr e

/-- The fibre energy restricted to non-injective leading blocks counts exactly the colliding
completions `VinogradovCollidingBlockCompletion q N k b`. -/
theorem finiteFiberEnergyWith_noninjective_split_eq_card
    {q N k b : ℕ} [NeZero q] :
    finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
      (fun z => ¬Function.Injective z.1) =
      Fintype.card (VinogradovCollidingBlockCompletion q N k b) := by
  rw [finiteFiberEnergyWith_eq_card]
  let e : {z : ((Fin k → Fin N) × (Fin b → Fin N)) ×
          ((Fin k → Fin N) × (Fin b → Fin N)) //
        ¬Function.Injective z.1.1 ∧ ¬Function.Injective z.2.1 ∧
          vinogradovSplitPowerSignature q N k b z.1 =
            vinogradovSplitPowerSignature q N k b z.2} ≃
      VinogradovCollidingBlockCompletion q N k b :=
    { toFun := fun z => ⟨
        (⟨z.1.1.1, z.2.1⟩, ⟨z.1.2.1, z.2.2.1⟩),
        ⟨(z.1.1.2, z.1.2.2), z.2.2.2⟩⟩
      invFun := fun z => ⟨
        ((z.1.1.1, z.2.1.1), (z.1.2.1, z.2.1.2)),
        ⟨z.1.1.2, z.1.2.2, z.2.2⟩⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Sigma.ext rfl (by simp) }
  exact Fintype.card_congr e

/-- The power-sum fibre energy on `(k + b)`-tuples modulo `q` is at most twice the sum of the energy
with injective leading block and the number of colliding completions. -/
theorem vinogradov_moment_collision_partition
    {q N k b : ℕ} [NeZero q] :
    finiteFiberEnergy
        (vinogradovPowerSignatureMod q k :
          (Fin (k + b) → Fin N) → Fin k → ZMod q) ≤
      2 * (finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
          (fun z => Function.Injective z.1) +
        Fintype.card (VinogradovCollidingBlockCompletion q N k b)) := by
  rw [← finiteFiberEnergy_vinogradovSplitPowerSignature_eq]
  calc
    finiteFiberEnergy (vinogradovSplitPowerSignature q N k b) ≤
        2 * (finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
            (fun z => Function.Injective z.1) +
          finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
            (fun z => ¬Function.Injective z.1)) :=
      finiteFiberEnergy_le_partition _ _
    _ = 2 * (finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
          (fun z => Function.Injective z.1) +
        Fintype.card (VinogradovCollidingBlockCompletion q N k b)) := by
      rw [finiteFiberEnergyWith_noninjective_split_eq_card]

/-- Collision recurrence: for `N ≠ 0`, `J_{k+b,k}(N) ≤ 2 (E_inj + ((k^2 - k) N^(k-1))^2 J_{b,k}(N))`,
where `E_inj` is the split-signature energy restricted to injective leading blocks. -/
theorem vinogradov_moment_collision_recurrence
    {N k b : ℕ} (hN : N ≠ 0) :
    Fintype.card (VinogradovDiagonalSolution N (k + b) k) ≤
      2 * (finiteFiberEnergyWith
          (vinogradovSplitPowerSignature
            (vinogradovMomentModulus N (k + b) k) N k b)
          (fun z => Function.Injective z.1) +
        ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
          Fintype.card (VinogradovDiagonalSolution N b k)) := by
  let q := vinogradovMomentModulus N (k + b) k
  calc
    Fintype.card (VinogradovDiagonalSolution N (k + b) k) =
        finiteFiberEnergy
          (vinogradovPowerSignatureMod q k :
            (Fin (k + b) → Fin N) → Fin k → ZMod q) := by
      symm
      exact vinogradovModularMomentAt_eq_card_of_large
        (q := q) (N := N) (b := k + b) (k := k) hN (by
          dsimp [q, vinogradovMomentModulus]
          omega)
    _ ≤ 2 * (finiteFiberEnergyWith
          (vinogradovSplitPowerSignature q N k b)
          (fun z => Function.Injective z.1) +
        Fintype.card (VinogradovCollidingBlockCompletion q N k b)) :=
      vinogradov_moment_collision_partition
    _ ≤ 2 * (finiteFiberEnergyWith
          (vinogradovSplitPowerSignature q N k b)
          (fun z => Function.Injective z.1) +
        ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
          Fintype.card (VinogradovDiagonalSolution N b k)) := by
      gcongr
      exact card_vinogradovCollidingBlockCompletion_le_tailMoment hN

end

end RHTower.Sieve

