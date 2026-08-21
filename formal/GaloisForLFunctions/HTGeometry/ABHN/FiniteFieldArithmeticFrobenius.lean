/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldNormSequence

/-!
# Arithmetic Frobenius at finite residue fields

For every finite field extension, arithmetic Frobenius is a specified generator of the Galois
group.  The cyclic Hilbert--90 and norm sequences can therefore be stated with this canonical
generator.  This is the finite-residue component that a local Artin map must lift; it is not that
lift or local class field theory itself.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Arithmetic Frobenius of a finite field extension. -/
noncomputable def finiteFieldArithmeticFrobenius
    (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L] [Finite L] : Gal(L/K) := by
  letI : Finite K := Finite.of_injective _ (algebraMap K L).injective
  letI : Fintype K := Fintype.ofFinite K
  exact FiniteField.frobeniusAlgEquivOfAlgebraic K L

/-- Arithmetic Frobenius acts by the cardinality power of the base finite field. -/
theorem finiteFieldArithmeticFrobenius_apply
    (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L] [Finite L] (x : L) :
    finiteFieldArithmeticFrobenius K L x = x ^ Nat.card K := by
  letI : Finite K := Finite.of_injective _ (algebraMap K L).injective
  letI : Fintype K := Fintype.ofFinite K
  change FiniteField.frobeniusAlgEquivOfAlgebraic K L x = x ^ Nat.card K
  rw [Nat.card_eq_fintype_card]
  exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic K L) x

/-- Arithmetic Frobenius has order equal to the extension degree. -/
theorem orderOf_finiteFieldArithmeticFrobenius
    (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L] [Finite L] :
    orderOf (finiteFieldArithmeticFrobenius K L) = Module.finrank K L := by
  letI : Finite K := Finite.of_injective _ (algebraMap K L).injective
  letI : Fintype K := Fintype.ofFinite K
  change orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic K L) = Module.finrank K L
  exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic K L

/-- Every finite-residue Galois automorphism is a power of arithmetic Frobenius. -/
theorem finiteFieldArithmeticFrobenius_generates
    (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L] [Finite L]
    (sigma : Gal(L/K)) : sigma ∈ Subgroup.zpowers (finiteFieldArithmeticFrobenius K L) := by
  letI : Finite K := Finite.of_injective _ (algebraMap K L).injective
  letI : Fintype K := Fintype.ofFinite K
  rw [Subgroup.mem_zpowers_iff]
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 sigma
  refine ⟨(n : ℕ), ?_⟩
  change FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ (n : ℕ) = sigma
  exact hn

/-- Hilbert 90 and norm surjectivity using arithmetic Frobenius. -/
theorem finiteFieldArithmeticFrobenius_normSequence
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L] :
    Function.Exact (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L))
      (cyclicGaloisAdditiveNormUnits K L) ∧
      Function.Surjective (cyclicGaloisAdditiveNormUnits K L) :=
  finiteField_cyclicGaloisNormSequence (finiteFieldArithmeticFrobenius_generates K L)

/-- The full exact norm sequence using arithmetic Frobenius. -/
theorem finiteFieldArithmeticFrobenius_fullNormSequence
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L] :
    Function.Injective (cyclicGaloisBaseUnitsMap (K := K) (L := L)) ∧
      Function.Exact (cyclicGaloisBaseUnitsMap (K := K) (L := L))
        (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L)) ∧
      Function.Exact (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L))
        (cyclicGaloisAdditiveNormUnits K L) ∧
      Function.Surjective (cyclicGaloisAdditiveNormUnits K L) :=
  finiteField_cyclicGaloisFullNormSequence (finiteFieldArithmeticFrobenius_generates K L)

end GaloisForLFunctions.HTGeometry.ABHN
