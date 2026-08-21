import GaloisForLFunctions.HTGeometry.MilnorPolynomialGlobalReciprocity

/-!
# Finite profiles determine the reciprocal infinity profile

For the projective line over a field, global reciprocity supplies precisely one constraint on
finite-and-infinite Milnor residue data.  Given arbitrary finite-support finite-place data, the
infinite residue is forced to be the negative total Bass--Tate norm.  This makes the compatible
all-place profile group explicitly equivalent to the finite-place profile group.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {F : Type*} [Field F]

local instance milnorPolynomialGlobalProfileDecidableEqMonicIrred :
    DecidableEq (MonicIrred F) := Classical.decEq _

/-- Complete finite-place data with the unique infinity coordinate satisfying global reciprocity. -/
noncomputable def milnorPolynomialFiniteToGlobalSumKer (n : ℕ) :
    MilnorPolynomialTotalResidueTarget (F := F) n →+
      (milnorPolynomialGlobalSum (F := F) n).ker where
  toFun z := ⟨(z, -milnorPolynomialTotalNorm (F := F) n z), by
    change milnorPolynomialTotalNorm (F := F) n z +
      -milnorPolynomialTotalNorm (F := F) n z = 0
    exact add_neg_cancel _⟩
  map_zero' := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change -milnorPolynomialTotalNorm (F := F) n (x + y) =
        -milnorPolynomialTotalNorm (F := F) n x + -milnorPolynomialTotalNorm (F := F) n y
      rw [map_add, neg_add]

/-- Forget the forced infinity coordinate of a globally reciprocal profile. -/
noncomputable def milnorPolynomialGlobalSumKerToFinite (n : ℕ) :
    (milnorPolynomialGlobalSum (F := F) n).ker →+
      MilnorPolynomialTotalResidueTarget (F := F) n where
  toFun z := z.1.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **Global reciprocity as an additive equivalence.** Finite residue data are equivalent to
finite-and-infinite profiles whose total norm-sum vanishes. -/
noncomputable def milnorPolynomialFiniteGlobalProfileEquiv (n : ℕ) :
    MilnorPolynomialTotalResidueTarget (F := F) n ≃+
      (milnorPolynomialGlobalSum (F := F) n).ker :=
  { milnorPolynomialFiniteToGlobalSumKer (F := F) n with
    invFun := milnorPolynomialGlobalSumKerToFinite (F := F) n
    left_inv := by
      intro z
      rfl
    right_inv := by
      rintro ⟨⟨z, r⟩, h⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change milnorPolynomialTotalNorm (F := F) n z + r = 0 at h
        change -milnorPolynomialTotalNorm (F := F) n z = r
        exact neg_eq_of_add_eq_zero_left (by rw [add_comm]; exact h) }

/-- The equivalence appends the forced negative total norm as the infinity coordinate. -/
theorem milnorPolynomialFiniteGlobalProfileEquiv_apply (n : ℕ)
    (z : MilnorPolynomialTotalResidueTarget (F := F) n) :
    (milnorPolynomialFiniteGlobalProfileEquiv (F := F) n z).1 =
      (z, -milnorPolynomialTotalNorm (F := F) n z) := rfl

end

end GaloisForLFunctions.HTGeometry
