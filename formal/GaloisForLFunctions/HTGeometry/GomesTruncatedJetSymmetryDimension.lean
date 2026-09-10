import GaloisForLFunctions.HTGeometry.GomesTruncatedJetResonantCoordinates
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Exact dimension of the full geometric-clock symmetry algebra

The corpus's resonant coordinate space is identified with a finite set of
multiples. Mathlib's exact multiples count gives a uniform natural-division
formula, including order zero where only the constant coordinate survives.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The exact number of surviving phase weights includes the constant coefficient at every order. -/
theorem gomesTruncatedJetResonantIndex_card (n : ℕ) (z : ℂ) :
    Fintype.card (GomesTruncatedJetResonantIndex n z) = n / orderOf z + 1 := by
  let S := (Finset.range (n + 1)).filter (fun k => orderOf z ∣ k)
  let e : GomesTruncatedJetResonantIndex n z ≃ ↥S :=
    { toFun := fun k => ⟨k.val.val,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.val.isLt, k.property⟩⟩
      invFun := fun k => ⟨⟨k.val, Finset.mem_range.mp (Finset.mem_filter.mp k.property).1⟩,
        (Finset.mem_filter.mp k.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h0 : 0 ∈ S := by simp [S]
  have hs : S.erase 0 =
      (Finset.range (n + 1)).filter (fun k => k ≠ 0 ∧ orderOf z ∣ k) := by
    ext k
    simp only [S, Finset.mem_erase, Finset.mem_filter, and_left_comm]
  calc
    Fintype.card (GomesTruncatedJetResonantIndex n z) = S.card :=
      (Fintype.card_congr e).trans (Fintype.card_coe S)
    _ = (S.erase 0).card + 1 := (Finset.card_erase_add_one h0).symm
    _ = n / orderOf z + 1 := by rw [hs, Nat.card_multiples']

/-- The full actual joint symmetry algebra has the exact finite phase-order dimension, including order zero. -/
theorem gomesTruncatedJetJointAlgebra_finrank (n : ℕ) (z : ℂ) :
    Module.finrank ℂ (gomesTruncatedJetJointAlgebra n z) = n / orderOf z + 1 := by
  rw [gomesTruncatedJetJointAlgebra_finrank_card, gomesTruncatedJetResonantIndex_card]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
