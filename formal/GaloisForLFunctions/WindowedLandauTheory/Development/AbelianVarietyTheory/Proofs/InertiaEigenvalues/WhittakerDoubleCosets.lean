import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedLinearCharacterNorm

/-! The Whittaker projection of the Gelfand–Graev character counts
unitriangular double cosets compatible with the Whittaker character. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq.GGNorm

/-- The finite Gelfand–Graev norm is a count of intertwining double cosets. -/
theorem wh_gg_eq_doubleCoset_sum {g : ℕ} [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (n : ℕ) :
    let U := upperUnitriangular g n
    letI := doubleCosetFintype U
    wh ψ (gg ψ n) =
      ∑ q : DoubleCoset.Quotient (U : Set (Gn g n)) U,
        if (whittakerCharacter ψ n).Intertwines U q.out then (1 : ℂ) else 0 := by
  let U := upperUnitriangular g n
  have hclass : IsClass (gg ψ n) := by
    intro x y
    rw [gg_eq_inducedFunction]
    exact inducedFunction_conj U _ y x
  have hpair : ip (gg ψ n) (gg ψ n) = characterPairing (Gn g n) (gg ψ n) (gg ψ n) := by
    rw [ip, characterPairing, Nat.card_eq_fintype_card]
  rw [← ip_gg ψ n _ hclass, hpair, gg_eq_inducedFunction]
  exact characterPairing_inducedLinear_eq U (whittakerCharacter ψ n)

end GlobalTheory.GLq.GGNorm
