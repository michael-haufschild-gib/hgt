import GaloisForLFunctions.RHTower.Sieve.VinogradovResidueClass

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovResidueTupleEmbedding
    {N p : ℕ} [NeZero p] (a : ZMod p) (b : ℕ) :
    (Fin b → VinogradovResidueClass N p a) ↪
      (Fin b → Fin (N ⌈/⌉ p)) where
  toFun u i := vinogradovResidueQuotientFin (u i)
  inj' := by
    intro u v h
    funext i
    exact vinogradovResidueQuotientFin_injective (congrFun h i)

theorem card_vinogradovFixedBlocksResidueTails_le_energy
    {q N p k b : ℕ} [NeZero q] [NeZero p]
    (hpunit : IsUnit (p : ZMod q)) (a : ZMod p)
    (x y : Fin k → Fin N) :
    Fintype.card {uv :
        (Fin b → VinogradovResidueClass N p a) ×
          (Fin b → VinogradovResidueClass N p a) //
      vinogradovPowerSignatureMod q k
          (Fin.append x (fun i => (uv.1 i).1)) =
        vinogradovPowerSignatureMod q k
          (Fin.append y (fun i => (uv.2 i).1))} ≤
      finiteFiberEnergy
        (fun u : Fin b → VinogradovResidueClass N p a =>
          vinogradovPowerSignatureMod q k
            (fun i => vinogradovResidueQuotientFin (u i))) := by
  classical
  let f : (Fin b → VinogradovResidueClass N p a) → Fin k → ZMod q :=
    fun u => vinogradovPowerSignatureMod q k
      (fun i => vinogradovResidueQuotientFin (u i))
  let A := powerSumAffineLinearTransform q k (p : ZMod q) (a.val : ZMod q)
  let C := powerSumAffineConstant q k b (a.val : ZMod q)
  let cx := vinogradovPowerSignatureMod q k x + C
  let cy := vinogradovPowerSignatureMod q k y + C
  let e : {uv :
        (Fin b → VinogradovResidueClass N p a) ×
          (Fin b → VinogradovResidueClass N p a) //
      vinogradovPowerSignatureMod q k
          (Fin.append x (fun i => (uv.1 i).1)) =
        vinogradovPowerSignatureMod q k
          (Fin.append y (fun i => (uv.2 i).1))} ≃
      {uv :
        (Fin b → VinogradovResidueClass N p a) ×
          (Fin b → VinogradovResidueClass N p a) //
        cx + A (f uv.1) = cy + A (f uv.2)} :=
    { toFun := fun uv => ⟨uv.1, by
        have h := uv.2
        rw [vinogradovPowerSignatureMod_append,
          vinogradovPowerSignatureMod_append] at h
        rw [vinogradovResidue_powerSignature_affine,
          vinogradovResidue_powerSignature_affine] at h
        simpa [cx, cy, C, A, f, add_assoc] using h⟩
      invFun := fun uv => ⟨uv.1, by
        have h := uv.2
        dsimp [cx, cy, C, A, f] at h
        rw [vinogradovPowerSignatureMod_append,
          vinogradovPowerSignatureMod_append,
          vinogradovResidue_powerSignature_affine,
          vinogradovResidue_powerSignature_affine]
        simpa only [add_assoc] using h⟩
      left_inv := fun uv => Subtype.ext rfl
      right_inv := fun uv => Subtype.ext rfl }
  calc
    Fintype.card {uv :
        (Fin b → VinogradovResidueClass N p a) ×
          (Fin b → VinogradovResidueClass N p a) //
      vinogradovPowerSignatureMod q k
          (Fin.append x (fun i => (uv.1 i).1)) =
        vinogradovPowerSignatureMod q k
          (Fin.append y (fun i => (uv.2 i).1))} =
        Fintype.card {uv :
          (Fin b → VinogradovResidueClass N p a) ×
            (Fin b → VinogradovResidueClass N p a) //
          cx + A (f uv.1) = cy + A (f uv.2)} := Fintype.card_congr e
    _ ≤ finiteFiberEnergy f :=
      card_transformed_fixed_shift_le_energy f A
        (powerSumAffineLinearTransform_injective hpunit _) cx cy

theorem finiteFiberEnergy_residueQuotients_le
    {q N p k b : ℕ} [NeZero q] [NeZero p] (a : ZMod p) :
    finiteFiberEnergy
        (fun u : Fin b → VinogradovResidueClass N p a =>
          vinogradovPowerSignatureMod q k
            (fun i => vinogradovResidueQuotientFin (u i))) ≤
      finiteFiberEnergy
        (vinogradovPowerSignatureMod q k :
          (Fin b → Fin (N ⌈/⌉ p)) → Fin k → ZMod q) := by
  classical
  let E := vinogradovResidueTupleEmbedding (N := N) a b
  let f : (Fin b → Fin (N ⌈/⌉ p)) → Fin k → ZMod q :=
    vinogradovPowerSignatureMod q k
  have hfun :
      (fun u : Fin b → VinogradovResidueClass N p a =>
        vinogradovPowerSignatureMod q k
          (fun i => vinogradovResidueQuotientFin (u i))) = f ∘ E := by
    funext u j
    rfl
  rw [hfun]
  exact finiteFiberEnergy_le_of_domain_embedding E f

theorem card_vinogradovFixedBlocksResidueTails_le_moment
    {q N p k b : ℕ} [NeZero q] [NeZero p]
    (hpunit : IsUnit (p : ZMod q)) (a : ZMod p)
    (x y : Fin k → Fin N) (hM : N ⌈/⌉ p ≠ 0)
    (hq : 2 * b * (N ⌈/⌉ p) ^ k < q) :
    Fintype.card {uv :
        (Fin b → VinogradovResidueClass N p a) ×
          (Fin b → VinogradovResidueClass N p a) //
      vinogradovPowerSignatureMod q k
          (Fin.append x (fun i => (uv.1 i).1)) =
        vinogradovPowerSignatureMod q k
          (Fin.append y (fun i => (uv.2 i).1))} ≤
      Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ p) b k) := by
  classical
  calc
    _ ≤ finiteFiberEnergy
        (fun u : Fin b → VinogradovResidueClass N p a =>
          vinogradovPowerSignatureMod q k
            (fun i => vinogradovResidueQuotientFin (u i))) :=
      card_vinogradovFixedBlocksResidueTails_le_energy hpunit a x y
    _ ≤ finiteFiberEnergy
        (vinogradovPowerSignatureMod q k :
          (Fin b → Fin (N ⌈/⌉ p)) → Fin k → ZMod q) :=
      finiteFiberEnergy_residueQuotients_le a
    _ = Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ p) b k) :=
      vinogradovModularMomentAt_eq_card_of_large hM hq

end

end RHTower.Sieve

