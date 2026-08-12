import GaloisForLFunctions.RHTower.Sieve.VinogradovModularMoment

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

theorem vinogradovPowerSignatureMod_append
    {q k N a b : ℕ} (x : Fin a → Fin N) (y : Fin b → Fin N) :
    vinogradovPowerSignatureMod q k (Fin.append x y) =
      vinogradovPowerSignatureMod q k x + vinogradovPowerSignatureMod q k y := by
  funext j
  unfold vinogradovPowerSignatureMod
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.add_apply]

/-- For fixed leading blocks, the number of pairs of tails completing the
same power signature is bounded by the ordinary tail moment. -/
theorem card_vinogradovFixedBlocks_le_finiteFiberEnergy
    {q k N a b : ℕ} [NeZero q] (x y : Fin a → Fin N) :
    Fintype.card {p : (Fin b → Fin N) × (Fin b → Fin N) //
      vinogradovPowerSignatureMod q k (Fin.append x p.1) =
        vinogradovPowerSignatureMod q k (Fin.append y p.2)} ≤
      finiteFiberEnergy
        (vinogradovPowerSignatureMod q k :
          (Fin b → Fin N) → Fin k → ZMod q) := by
  let tailSignature : (Fin b → Fin N) → Fin k → ZMod q :=
    vinogradovPowerSignatureMod q k
  let shift : Fin k → ZMod q :=
    vinogradovPowerSignatureMod q k y - vinogradovPowerSignatureMod q k x
  let e : {p : (Fin b → Fin N) × (Fin b → Fin N) //
        vinogradovPowerSignatureMod q k (Fin.append x p.1) =
          vinogradovPowerSignatureMod q k (Fin.append y p.2)} ≃
      {p : (Fin b → Fin N) × (Fin b → Fin N) //
        tailSignature p.1 = tailSignature p.2 + shift} :=
    { toFun := fun p => ⟨p.1, by
        have hp := p.2
        rw [vinogradovPowerSignatureMod_append,
          vinogradovPowerSignatureMod_append] at hp
        dsimp [tailSignature, shift]
        calc
          vinogradovPowerSignatureMod q k p.1.1 =
              -vinogradovPowerSignatureMod q k x +
                (vinogradovPowerSignatureMod q k x +
                  vinogradovPowerSignatureMod q k p.1.1) := by abel
          _ = -vinogradovPowerSignatureMod q k x +
                (vinogradovPowerSignatureMod q k y +
                  vinogradovPowerSignatureMod q k p.1.2) := by rw [hp]
          _ = vinogradovPowerSignatureMod q k p.1.2 +
                (vinogradovPowerSignatureMod q k y -
                  vinogradovPowerSignatureMod q k x) := by abel⟩
      invFun := fun p => ⟨p.1, by
        rw [vinogradovPowerSignatureMod_append,
          vinogradovPowerSignatureMod_append]
        dsimp [tailSignature, shift] at p
        calc
          vinogradovPowerSignatureMod q k x +
              vinogradovPowerSignatureMod q k p.1.1 =
              vinogradovPowerSignatureMod q k x +
                (vinogradovPowerSignatureMod q k p.1.2 +
                  (vinogradovPowerSignatureMod q k y -
                    vinogradovPowerSignatureMod q k x)) := by rw [p.2]
          _ = vinogradovPowerSignatureMod q k y +
                vinogradovPowerSignatureMod q k p.1.2 := by abel⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun p => Subtype.ext rfl }
  calc
    Fintype.card {p : (Fin b → Fin N) × (Fin b → Fin N) //
        vinogradovPowerSignatureMod q k (Fin.append x p.1) =
          vinogradovPowerSignatureMod q k (Fin.append y p.2)} =
        Fintype.card {p : (Fin b → Fin N) × (Fin b → Fin N) //
          tailSignature p.1 = tailSignature p.2 + shift} := Fintype.card_congr e
    _ = finiteFiberCorrelation tailSignature shift :=
      (finiteFiberCorrelation_eq_card tailSignature shift).symm
    _ ≤ finiteFiberEnergy tailSignature :=
      finiteFiberCorrelation_le_energy tailSignature shift

end

end RHTower.Sieve
