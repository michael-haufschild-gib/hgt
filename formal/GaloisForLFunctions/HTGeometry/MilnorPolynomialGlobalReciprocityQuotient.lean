import GaloisForLFunctions.HTGeometry.MilnorPolynomialGlobalReciprocity

/-!
# Quotient form of projective-line Milnor reciprocity

For the rational function field `F(t)`, all finite residues together with the residue at infinity
are constrained by one global condition: the total Bass--Tate norm-sum is zero.  The exact
residue sequence identifies this compatible local data with Milnor classes modulo constants.
This is the quotient-level local-to-global form of the projective-line reciprocity sequence.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {F : Type*} [Field F]

local instance : DecidableEq (MonicIrred F) := Classical.decEq _

/-- The all-place residue map, with codomain restricted to data satisfying global reciprocity. -/
noncomputable def milnorPolynomialAllResidueToGlobalSumKer (n : ℕ) :
    MilnorKDeg (RatFunc F) n.succ →+
      (milnorPolynomialGlobalSum (F := F) n).ker :=
  (milnorPolynomialAllResidue (F := F) n).codRestrict _ (by
    intro y
    exact (milnorPolynomialAllResidue_exact (F := F) n
      (milnorPolynomialAllResidue (F := F) n y)).mpr ⟨y, rfl⟩)

/-- The only all-place-residue classes which vanish are those coming from the constant field. -/
theorem milnorPolynomialAllResidueToGlobalSumKer_ker_eq_constRange (n : ℕ) :
    (milnorPolynomialAllResidueToGlobalSumKer (F := F) n).ker =
      AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n.succ) := by
  apply le_antisymm
  · intro y hy
    rw [← milnorPolynomialAllResidue_ker_eq_constRange]
    change milnorPolynomialAllResidue (F := F) n y = 0
    exact congrArg Subtype.val hy
  · intro y hy
    have hzero : y ∈ (milnorPolynomialAllResidue (F := F) n).ker := by
      rw [milnorPolynomialAllResidue_ker_eq_constRange]
      exact hy
    exact Subtype.ext hzero

/-- Every compatible collection of finite-and-infinite residues is globally realized. -/
theorem milnorPolynomialAllResidueToGlobalSumKer_surjective (n : ℕ) :
    Function.Surjective (milnorPolynomialAllResidueToGlobalSumKer (F := F) n) := by
  intro z
  have hz : z.1 ∈ AddMonoidHom.range (milnorPolynomialAllResidue (F := F) n) := by
    rw [milnorPolynomialAllResidue_range_eq_globalSum_ker]
    exact z.2
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact hy

/-- **Quotient local-global equivalence.** Milnor classes of `F(t)` modulo constant classes are
equivalent to all finite-and-infinite residue data whose global norm-sum vanishes. -/
noncomputable def milnorPolynomialGlobalResidueQuotientEquiv (n : ℕ) :
    MilnorKDeg (RatFunc F) n.succ ⧸
        AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n.succ) ≃+
      (milnorPolynomialGlobalSum (F := F) n).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (milnorPolynomialAllResidueToGlobalSumKer_ker_eq_constRange (F := F) n).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (milnorPolynomialAllResidueToGlobalSumKer (F := F) n)
        (milnorPolynomialAllResidueToGlobalSumKer_surjective (F := F) n))

/-- The quotient local-global equivalence sends a Milnor class to its all-place residues. -/
theorem milnorPolynomialGlobalResidueQuotientEquiv_mk (n : ℕ)
    (y : MilnorKDeg (RatFunc F) n.succ) :
    milnorPolynomialGlobalResidueQuotientEquiv (F := F) n (QuotientAddGroup.mk y) =
      milnorPolynomialAllResidueToGlobalSumKer (F := F) n y := by
  simp [milnorPolynomialGlobalResidueQuotientEquiv]
  change QuotientAddGroup.kerLift (milnorPolynomialAllResidueToGlobalSumKer (F := F) n)
    (QuotientAddGroup.mk y) = milnorPolynomialAllResidueToGlobalSumKer (F := F) n y
  rfl

end
