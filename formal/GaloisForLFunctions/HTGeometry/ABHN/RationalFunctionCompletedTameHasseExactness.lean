import GaloisForLFunctions.HTGeometry.ABHN.AdicTameResidueQuotientEquiv
import GaloisForLFunctions.HTGeometry.MilnorPolynomialGlobalReciprocityQuotient

/-!
# Completed-local tame Hasse exactness for a rational function field

For a finite field `F`, this file replaces every finite residue coordinate in the projective-line
Milnor reciprocity sequence by an actual completed local group

`K₂ᴹ(F(t)ᵥ) / ker(∂ᵥ)`.

The resulting sequence is exact, its final global sum is surjective, and global `K₂` classes
modulo constants are equivalent to the kernel of that sum.  Thus the finite-place terms are
literal completion-side objects, not merely source-side residue fields or chosen lifts.

This is a tame Milnor `K`-theory Hasse principle.  It is not yet the Brauer-group ABHN sequence:
that comparison additionally needs a norm-residue bridge from local `K₂` to local Brauer or
Galois-cohomology classes.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial WithZero WithZeroMulInt

universe u

noncomputable section

local instance completedTameHasseDecidableEqMonicIrred
    {F : Type*} [Field F] : DecidableEq (MonicIrred F) := Classical.decEq _

/-- The tame quotient of actual `q`-adic `K₂`, retaining exactly the residue coordinate. -/
abbrev RationalFunctionFiniteAdicTameQuotient
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F) :=
  MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2 ⧸
    (rationalFunctionFiniteAdicTameMilnorResidue F (polyPlace q.2.1)).ker

/-- Restricted direct sum of actual finite-adic tame quotients. -/
abbrev RationalFunctionCompletedFiniteTameProfile
    (F : Type u) [Field F] [Finite F] :=
  Π₀ q : MonicIrred F, RationalFunctionFiniteAdicTameQuotient F q

/-- Coordinatewise residue equivalence from completed tame quotients to global residue fields. -/
noncomputable def rationalFunctionCompletedFiniteTameProfileEquiv
    (F : Type u) [Field F] [Finite F] :
    RationalFunctionCompletedFiniteTameProfile F ≃+
      MilnorPolynomialTotalResidueTarget (F := F) 1 :=
  DFinsupp.mapRange.addEquiv fun q ↦
    rationalFunctionFiniteAdicTameQuotientEquivGlobalResidue F (polyPlace q.2.1)

/-- Completed finite tame data, together with the `K₁(F)` coordinate at infinity. -/
abbrev RationalFunctionCompletedTameAllLocalData
    (F : Type u) [Field F] [Finite F] :=
  RationalFunctionCompletedFiniteTameProfile F × MilnorKDeg F 1

/-- Completed local data are equivalent to the usual finite-residue profile plus infinity. -/
noncomputable def rationalFunctionCompletedTameAllLocalDataEquiv
    (F : Type u) [Field F] [Finite F] :
    RationalFunctionCompletedTameAllLocalData F ≃+
      MilnorPolynomialTotalResidueTarget (F := F) 1 × MilnorKDeg F 1 :=
  AddEquiv.prodCongr (rationalFunctionCompletedFiniteTameProfileEquiv F)
    (AddEquiv.refl (MilnorKDeg F 1))

/-- All-place residue map with actual completed tame quotients at finite places. -/
noncomputable def rationalFunctionCompletedTameAllResidue
    (F : Type u) [Field F] [Finite F] :
    MilnorKDeg (RatFunc F) 2 →+ RationalFunctionCompletedTameAllLocalData F :=
  (rationalFunctionCompletedTameAllLocalDataEquiv F).symm.toAddMonoidHom.comp
    (milnorPolynomialAllResidue (F := F) 1)

/-- Global norm-sum on completed finite tame data and the place at infinity. -/
noncomputable def rationalFunctionCompletedTameGlobalSum
    (F : Type u) [Field F] [Finite F] :
    RationalFunctionCompletedTameAllLocalData F →+ MilnorKDeg F 1 :=
  (milnorPolynomialGlobalSum (F := F) 1).comp
    (rationalFunctionCompletedTameAllLocalDataEquiv F).toAddMonoidHom

/-- Every global class has globally reciprocal completed local tame residues. -/
theorem rationalFunctionCompletedTameGlobalSum_allResidue_eq_zero
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    rationalFunctionCompletedTameGlobalSum F
      (rationalFunctionCompletedTameAllResidue F y) = 0 := by
  change milnorPolynomialGlobalSum (F := F) 1
    (rationalFunctionCompletedTameAllLocalDataEquiv F
      ((rationalFunctionCompletedTameAllLocalDataEquiv F).symm
        (milnorPolynomialAllResidue (F := F) 1 y))) = 0
  rw [AddEquiv.apply_symm_apply]
  change milnorPolynomialTotalNorm (F := F) 1
      (milnorPolynomialTotalResidue (F := F) 1 y) + milnorResidueInfty 1 y = 0
  exact milnorPolynomialTotalResidue_reciprocity 1 y

/-- Vanishing at every completed tame quotient and at infinity detects constant classes. -/
theorem rationalFunctionCompletedTameAllResidue_ker_eq_constRange
    (F : Type u) [Field F] [Finite F] :
    (rationalFunctionCompletedTameAllResidue F).ker =
      AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) 2) := by
  ext y
  constructor
  · intro hy
    rw [← milnorPolynomialAllResidue_ker_eq_constRange (F := F) 1]
    change milnorPolynomialAllResidue (F := F) 1 y = 0
    change (rationalFunctionCompletedTameAllLocalDataEquiv F).symm
      (milnorPolynomialAllResidue (F := F) 1 y) = 0 at hy
    have h := congrArg (rationalFunctionCompletedTameAllLocalDataEquiv F) hy
    simpa using h
  · intro hy
    rw [← milnorPolynomialAllResidue_ker_eq_constRange (F := F) 1] at hy
    change (rationalFunctionCompletedTameAllLocalDataEquiv F).symm
      (milnorPolynomialAllResidue (F := F) 1 y) = 0
    rw [hy, map_zero]

/-- Compatible completed local tame data are exactly globally realized residue data. -/
theorem rationalFunctionCompletedTameAllResidue_range_eq_globalSum_ker
    (F : Type u) [Field F] [Finite F] :
    AddMonoidHom.range (rationalFunctionCompletedTameAllResidue F) =
      (rationalFunctionCompletedTameGlobalSum F).ker := by
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    exact rationalFunctionCompletedTameGlobalSum_allResidue_eq_zero F y
  · intro z hz
    have hez : rationalFunctionCompletedTameAllLocalDataEquiv F z ∈
        (milnorPolynomialGlobalSum (F := F) 1).ker := hz
    rw [← milnorPolynomialAllResidue_range_eq_globalSum_ker (F := F) 1] at hez
    obtain ⟨y, hy⟩ := hez
    refine ⟨y, ?_⟩
    change (rationalFunctionCompletedTameAllLocalDataEquiv F).symm
      (milnorPolynomialAllResidue (F := F) 1 y) = z
    rw [hy, AddEquiv.symm_apply_apply]

/-- The completed local global-sum map is surjective. -/
theorem rationalFunctionCompletedTameGlobalSum_surjective
    (F : Type u) [Field F] [Finite F] :
    Function.Surjective (rationalFunctionCompletedTameGlobalSum F) := by
  intro x
  obtain ⟨z, hz⟩ := milnorPolynomialGlobalSum_surjective (F := F) 1 x
  exact ⟨(rationalFunctionCompletedTameAllLocalDataEquiv F).symm z, by
    change milnorPolynomialGlobalSum (F := F) 1
      (rationalFunctionCompletedTameAllLocalDataEquiv F
        ((rationalFunctionCompletedTameAllLocalDataEquiv F).symm z)) = x
    rw [AddEquiv.apply_symm_apply, hz]⟩

/-- Exact completed-local tame projective-line Hasse sequence. -/
theorem rationalFunctionCompletedTameProjectiveLine_exact
    (F : Type u) [Field F] [Finite F] :
    Function.Injective (milnorKDegMap (ratFuncConstHom (F := F)) 2) ∧
      Function.Exact (milnorKDegMap (ratFuncConstHom (F := F)) 2)
        (rationalFunctionCompletedTameAllResidue F) ∧
      Function.Exact (rationalFunctionCompletedTameAllResidue F)
        (rationalFunctionCompletedTameGlobalSum F) ∧
      Function.Surjective (rationalFunctionCompletedTameGlobalSum F) := by
  refine ⟨milnorKDegMap_ratFuncConstHom_injective 2, ?_, ?_,
    rationalFunctionCompletedTameGlobalSum_surjective F⟩
  · rw [AddMonoidHom.exact_iff]
    exact rationalFunctionCompletedTameAllResidue_ker_eq_constRange F
  · rw [AddMonoidHom.exact_iff]
    exact (rationalFunctionCompletedTameAllResidue_range_eq_globalSum_ker F).symm

/-- Completed all-place tame residue map restricted to globally compatible local data. -/
noncomputable def rationalFunctionCompletedTameAllResidueToGlobalSumKer
    (F : Type u) [Field F] [Finite F] :
    MilnorKDeg (RatFunc F) 2 →+
      (rationalFunctionCompletedTameGlobalSum F).ker :=
  (rationalFunctionCompletedTameAllResidue F).codRestrict _ (by
    intro y
    exact rationalFunctionCompletedTameGlobalSum_allResidue_eq_zero F y)

/-- Kernel of the compatible-data map consists exactly of constants. -/
theorem rationalFunctionCompletedTameAllResidueToGlobalSumKer_ker_eq_constRange
    (F : Type u) [Field F] [Finite F] :
    (rationalFunctionCompletedTameAllResidueToGlobalSumKer F).ker =
      AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) 2) := by
  apply le_antisymm
  · intro y hy
    rw [← rationalFunctionCompletedTameAllResidue_ker_eq_constRange F]
    change rationalFunctionCompletedTameAllResidue F y = 0
    exact congrArg Subtype.val hy
  · intro y hy
    have hzero : y ∈ (rationalFunctionCompletedTameAllResidue F).ker := by
      rw [rationalFunctionCompletedTameAllResidue_ker_eq_constRange F]
      exact hy
    exact Subtype.ext hzero

/-- Every compatible completed local tame profile has a global realization. -/
theorem rationalFunctionCompletedTameAllResidueToGlobalSumKer_surjective
    (F : Type u) [Field F] [Finite F] :
    Function.Surjective (rationalFunctionCompletedTameAllResidueToGlobalSumKer F) := by
  intro z
  have hz : z.1 ∈ AddMonoidHom.range
      (rationalFunctionCompletedTameAllResidue F) := by
    rw [rationalFunctionCompletedTameAllResidue_range_eq_globalSum_ker F]
    exact z.2
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact hy

/-- Global Milnor `K₂` classes modulo constants are equivalent to globally compatible data
formed from actual finite adic completions modulo their tame-residue kernels, together with the
place at infinity. -/
noncomputable def rationalFunctionCompletedTameGlobalResidueQuotientEquiv
    (F : Type u) [Field F] [Finite F] :
    MilnorKDeg (RatFunc F) 2 ⧸
        AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) 2) ≃+
      (rationalFunctionCompletedTameGlobalSum F).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (rationalFunctionCompletedTameAllResidueToGlobalSumKer_ker_eq_constRange F).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (rationalFunctionCompletedTameAllResidueToGlobalSumKer F)
        (rationalFunctionCompletedTameAllResidueToGlobalSumKer_surjective F))

/-- The quotient equivalence sends a global class to its completed all-place tame residues. -/
theorem rationalFunctionCompletedTameGlobalResidueQuotientEquiv_mk
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    rationalFunctionCompletedTameGlobalResidueQuotientEquiv F (QuotientAddGroup.mk y) =
      rationalFunctionCompletedTameAllResidueToGlobalSumKer F y := by
  simp [rationalFunctionCompletedTameGlobalResidueQuotientEquiv]
  change QuotientAddGroup.kerLift
      (rationalFunctionCompletedTameAllResidueToGlobalSumKer F)
      (QuotientAddGroup.mk y) =
    rationalFunctionCompletedTameAllResidueToGlobalSumKer F y
  rfl

end
end GaloisForLFunctions.HTGeometry.ABHN
