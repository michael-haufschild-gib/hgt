/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryNormQuotient
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionCircleCharacter

/-!
# Faithful torsion characters of literal cyclic carry classes

A finite norm-quotient coordinate transports the literal carry model of cyclic `H²` to the
corresponding torsion subgroup of `ℚ/ℤ`.  The standard circle character is faithful, is compatible
with the global `ℚ/ℤ` character, and detects exactly which base units are field norms.  This is the
multiplicative phase interface that retains local torsion information even though every additive
map from `ℚ/ℤ` to `ℂ` vanishes.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Literal carry `H²`, expressed as the finite torsion subgroup selected by a norm-quotient
coordinate. -/
noncomputable def cyclicGaloisCarryH2TorsionEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    cyclicGaloisH2 K L ≃+ ratModIntNTorsion n := by
  letI : NeZero n := ⟨hn⟩
  letI : Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :=
    Finite.of_injective qEquiv qEquiv.injective
  exact ((cyclicGaloisCarryNormQuotientEquiv K L).symm.trans qEquiv).trans
    (zmodRatModIntAddEquivNTorsion n hn)

/-- Torsion coordinate of a literal carry class is the supplied quotient coordinate embedded in
`ℚ/ℤ[n]`. -/
@[simp] theorem cyclicGaloisCarryH2TorsionEquiv_carryClass
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (a : Additive Kˣ) :
    cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv
        (cyclicGaloisCarryH2Class K L a) =
      zmodRatModIntAddEquivNTorsion n hn (qEquiv (QuotientAddGroup.mk a)) := by
  letI : NeZero n := ⟨hn⟩
  letI : Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :=
    Finite.of_injective qEquiv qEquiv.injective
  change zmodRatModIntAddEquivNTorsion n hn
      (qEquiv ((cyclicGaloisCarryNormQuotientEquiv K L).symm
        (cyclicGaloisCarryH2Class K L a))) = _
  rw [← cyclicGaloisCarryNormQuotientEquiv_mk K L a]
  rw [AddEquiv.symm_apply_apply]

/-- Faithful complex circle character of literal carry `H²`. -/
noncomputable def cyclicGaloisCarryH2TorsionStdAddChar
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    AddChar (cyclicGaloisH2 K L) ℂ :=
  (ratModIntNTorsionStdAddChar n hn).compAddMonoidHom
    (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv).toAddMonoidHom

/-- Carry `H²` standard character is faithful. -/
theorem cyclicGaloisCarryH2TorsionStdAddChar_injective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    Function.Injective (cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv) :=
  (ratModIntNTorsionStdAddChar_injective n hn).comp
    (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv).injective

/-- Carry `H²` phase is literally the global `ℚ/ℤ` character of its torsion invariant. -/
theorem cyclicGaloisCarryH2TorsionStdAddChar_eq_global_character
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv z =
      ratModIntStdAddChar
        (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv z : RatModInt) := by
  change ratModIntNTorsionStdAddChar n hn
      (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv z) = _
  exact (ratModIntStdAddChar_subtype_eq_ratModIntNTorsionStdAddChar n hn
    (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv z)).symm

/-- Every carry `H²` phase is an `n`th root of unity. -/
theorem cyclicGaloisCarryH2TorsionStdAddChar_pow_eq_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (z : cyclicGaloisH2 K L) :
    (cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv z) ^ n = 1 :=
  ratModIntNTorsionStdAddChar_pow_eq_one n hn
    (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv z)

/-- Carry `H²` phase equals one exactly at the zero cohomology class. -/
theorem cyclicGaloisCarryH2TorsionStdAddChar_eq_one_iff_eq_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv z = 1 ↔ z = 0 := by
  constructor
  · intro hz
    apply cyclicGaloisCarryH2TorsionStdAddChar_injective K L n hn qEquiv
    rw [hz]
    exact (cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv).map_zero_eq_one.symm
  · rintro rfl
    exact (cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv).map_zero_eq_one

/-- Local reciprocity character criterion: a base unit has trivial carry phase exactly when it is
a field norm. -/
theorem cyclicGaloisCarryH2TorsionStdAddChar_carryClass_eq_one_iff_mem_normImage
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (a : Additive Kˣ) :
    cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv
        (cyclicGaloisCarryH2Class K L a) = 1 ↔
      a ∈ cyclicGaloisH2BaseNormImage K L := by
  rw [cyclicGaloisCarryH2TorsionStdAddChar_eq_one_iff_eq_zero]
  exact cyclicGaloisCarryH2Class_eq_zero_iff_mem_normImage K L a

end

end GaloisForLFunctions.HTGeometry.ABHN
