import GaloisForLFunctions.RHTower.Sieve.VinogradovShiftedCompatibility

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def VinogradovResidueGoodCompletion
    (q N p k b : ℕ) [NeZero q] [NeZero p] (a : ZMod p) :=
  {z :
      (VinogradovInjectiveBlock N p k ×
        (Fin b → VinogradovResidueClass N p a)) ×
      (VinogradovInjectiveBlock N p k ×
        (Fin b → VinogradovResidueClass N p a)) //
    vinogradovPowerSignatureMod q k
        (Fin.append z.1.1.1 (fun i => (z.1.2 i).1)) =
      vinogradovPowerSignatureMod q k
        (Fin.append z.2.1.1 (fun i => (z.2.2 i).1))}

noncomputable instance vinogradovResidueGoodCompletionFinite
    (q N p k b : ℕ) [NeZero q] [NeZero p] (a : ZMod p) :
    Finite (VinogradovResidueGoodCompletion q N p k b a) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance vinogradovResidueGoodCompletionFintype
    (q N p k b : ℕ) [NeZero q] [NeZero p] (a : ZMod p) :
    Fintype (VinogradovResidueGoodCompletion q N p k b a) := Fintype.ofFinite _

abbrev VinogradovResidueGoodDecomposition
    {q N p k b : ℕ} [NeZero q] [NeZero p]
    (hp : p.Prime) (hNp : N < p ^ k) (_hN : N ≠ 0)
    (_hq : 2 * (k + b) * N ^ k < q) (a : ZMod p) :=
  Σ x : VinogradovInjectiveBlock N p k,
    Σ y : VinogradovShiftedCompatiblePartner hp hNp a x,
      {uv :
          (Fin b → VinogradovResidueClass N p a) ×
            (Fin b → VinogradovResidueClass N p a) //
        vinogradovPowerSignatureMod q k
            (Fin.append x.1 (fun i => (uv.1 i).1)) =
          vinogradovPowerSignatureMod q k
            (Fin.append y.1.1 (fun i => (uv.2 i).1))}

def vinogradovResidueGoodCompletionEquiv
    {q N p k b : ℕ} [NeZero q] [NeZero p]
    (hp : p.Prime) (hNp : N < p ^ k) (hN : N ≠ 0)
    (hq : 2 * (k + b) * N ^ k < q) (a : ZMod p) :
    VinogradovResidueGoodCompletion q N p k b a ≃
      VinogradovResidueGoodDecomposition hp hNp hN hq a where
  toFun z := ⟨z.1.1.1,
    ⟨z.1.2.1,
      vinogradovShiftedNestedCompatible_of_residueTail_solution
        hp hNp hN hq a z.1.1.1 z.1.2.1 z.1.1.2 z.1.2.2 z.2⟩,
    ⟨(z.1.1.2, z.1.2.2), z.2⟩⟩
  invFun z := ⟨((z.1, z.2.2.1.1), (z.2.1.1, z.2.2.1.2)), z.2.2.2⟩
  left_inv := fun z => Subtype.ext rfl
  right_inv := by
    rintro ⟨x, y, uv⟩
    rfl

theorem card_vinogradovInjectiveBlock_le (N p k : ℕ) :
    Fintype.card (VinogradovInjectiveBlock N p k) ≤ N ^ k := by
  calc
    Fintype.card (VinogradovInjectiveBlock N p k) ≤
        Fintype.card (Fin k → Fin N) :=
      Fintype.card_le_of_embedding ⟨Subtype.val, Subtype.val_injective⟩
    _ = N ^ k := by rw [Fintype.card_fun]; simp

theorem card_vinogradovResidueGoodCompletion_le
    {q N p k b : ℕ} [NeZero q] [NeZero p]
    (hp : p.Prime) (hkp : k < p) (hNp : N < p ^ k) (hN : N ≠ 0)
    (hqfull : 2 * (k + b) * N ^ k < q)
    (hpunit : IsUnit (p : ZMod q)) (a : ZMod p)
    (hM : N ⌈/⌉ p ≠ 0) (hqtail : 2 * b * (N ⌈/⌉ p) ^ k < q) :
    Fintype.card (VinogradovResidueGoodCompletion q N p k b a) ≤
      N ^ k * (k.factorial * p ^ (k * (k - 1) / 2) *
        Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ p) b k)) := by
  classical
  let L := k.factorial * p ^ (k * (k - 1) / 2)
  let J := Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ p) b k)
  rw [Fintype.card_congr
    (vinogradovResidueGoodCompletionEquiv hp hNp hN hqfull a)]
  calc
    Fintype.card (VinogradovResidueGoodDecomposition hp hNp hN hqfull a) =
        ∑ x : VinogradovInjectiveBlock N p k,
          Fintype.card (Σ y : VinogradovShiftedCompatiblePartner hp hNp a x,
            {uv :
                (Fin b → VinogradovResidueClass N p a) ×
                  (Fin b → VinogradovResidueClass N p a) //
              vinogradovPowerSignatureMod q k
                  (Fin.append x.1 (fun i => (uv.1 i).1)) =
                vinogradovPowerSignatureMod q k
                  (Fin.append y.1.1 (fun i => (uv.2 i).1))}) := by
      exact Fintype.card_sigma
        (ι := VinogradovInjectiveBlock N p k)
        (α := fun x =>
          Σ y : VinogradovShiftedCompatiblePartner hp hNp a x,
            {uv :
                (Fin b → VinogradovResidueClass N p a) ×
                  (Fin b → VinogradovResidueClass N p a) //
              vinogradovPowerSignatureMod q k
                  (Fin.append x.1 (fun i => (uv.1 i).1)) =
                vinogradovPowerSignatureMod q k
                  (Fin.append y.1.1 (fun i => (uv.2 i).1))})
    (∑ x : VinogradovInjectiveBlock N p k,
        Fintype.card (Σ y : VinogradovShiftedCompatiblePartner hp hNp a x,
          {uv :
              (Fin b → VinogradovResidueClass N p a) ×
                (Fin b → VinogradovResidueClass N p a) //
            vinogradovPowerSignatureMod q k
                (Fin.append x.1 (fun i => (uv.1 i).1)) =
              vinogradovPowerSignatureMod q k
                (Fin.append y.1.1 (fun i => (uv.2 i).1))})) ≤
        ∑ _x : VinogradovInjectiveBlock N p k, L * J := by
      apply Finset.sum_le_sum
      intro x _
      rw [Fintype.card_sigma]
      calc
        (∑ y : VinogradovShiftedCompatiblePartner hp hNp a x,
            Fintype.card {uv :
                (Fin b → VinogradovResidueClass N p a) ×
                  (Fin b → VinogradovResidueClass N p a) //
              vinogradovPowerSignatureMod q k
                  (Fin.append x.1 (fun i => (uv.1 i).1)) =
                vinogradovPowerSignatureMod q k
                  (Fin.append y.1.1 (fun i => (uv.2 i).1))}) ≤
            ∑ _y : VinogradovShiftedCompatiblePartner hp hNp a x, J := by
          apply Finset.sum_le_sum
          intro y _
          exact card_vinogradovFixedBlocksResidueTails_le_moment
            hpunit a x.1 y.1.1 hM hqtail
        _ = Fintype.card (VinogradovShiftedCompatiblePartner hp hNp a x) * J := by simp
        _ ≤ L * J := Nat.mul_le_mul_right J
          (card_vinogradovShiftedCompatiblePartner_le hp hkp hNp a x)
    _ = Fintype.card (VinogradovInjectiveBlock N p k) * (L * J) := by simp
    _ ≤ N ^ k * (L * J) := Nat.mul_le_mul_right _
      (card_vinogradovInjectiveBlock_le N p k)

end

end RHTower.Sieve
