/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisCohomology
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionCircleCharacter

/-!
# Character form of finite continuous Galois `H²` invariants

Whenever finite continuous unit cohomology in degree two is identified with `ℚ/ℤ[n]`, its
standard finite character is exactly the restriction of the canonical global `ℚ/ℤ` character.
This gives the finite local-class-field-theory layer a faithful complex phase with exact conductor
dividing `n`.

It does not identify continuous `H²` with a local Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- The faithful finite character on continuous unit `H²`, transported through a supplied
finite torsion invariant equivalence. -/
noncomputable def continuousGaloisH2TorsionStdAddChar
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    AddChar (continuousGaloisUnitCohomology 2 K L) ℂ :=
  (ratModIntNTorsionStdAddChar n hn).compAddMonoidHom e.toAddMonoidHom

/-- The transported continuous-cohomology character is faithful. -/
theorem continuousGaloisH2TorsionStdAddChar_injective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n) :
    Function.Injective (continuousGaloisH2TorsionStdAddChar K L n hn e) := by
  exact (ratModIntNTorsionStdAddChar_injective n hn).comp e.injective

/-- The finite continuous `H²` character is literally the global `ℚ/ℤ` character of its
torsion-valued invariant. -/
theorem continuousGaloisH2TorsionStdAddChar_eq_global_character
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : continuousGaloisUnitCohomology 2 K L) :
    continuousGaloisH2TorsionStdAddChar K L n hn e z =
      ratModIntStdAddChar (e z : RatModInt) := by
  change ratModIntNTorsionStdAddChar n hn (e z) = ratModIntStdAddChar (e z : RatModInt)
  exact (ratModIntStdAddChar_subtype_eq_ratModIntNTorsionStdAddChar n hn (e z)).symm

/-- Every finite continuous `H²` phase is an `n`th root of unity. -/
theorem continuousGaloisH2TorsionStdAddChar_pow_eq_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : continuousGaloisUnitCohomology 2 K L) :
    (continuousGaloisH2TorsionStdAddChar K L n hn e z) ^ n = 1 := by
  change (ratModIntNTorsionStdAddChar n hn (e z)) ^ n = 1
  exact ratModIntNTorsionStdAddChar_pow_eq_one n hn (e z)

/-- The continuous `H²` phase equals one exactly at the zero cohomology class. -/
theorem continuousGaloisH2TorsionStdAddChar_eq_one_iff_eq_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : continuousGaloisUnitCohomology 2 K L) :
    continuousGaloisH2TorsionStdAddChar K L n hn e z = 1 ↔ z = 0 := by
  constructor
  · intro hz
    apply continuousGaloisH2TorsionStdAddChar_injective K L n hn e
    rw [hz]
    exact (continuousGaloisH2TorsionStdAddChar K L n hn e).map_zero_eq_one.symm
  · intro hz
    rw [hz]
    exact (continuousGaloisH2TorsionStdAddChar K L n hn e).map_zero_eq_one

end

end GaloisForLFunctions.HTGeometry.ABHN
