import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialFiniteQuotients
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Residues over algebraically closed constants

Every nonzero prime of a finite free polynomial order has residue field
equal to the constant field. The resulting residue homomorphism recovers
the prime as its kernel.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain

variable (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [IsDedekindDomain B]
    [Algebra K B] [Algebra K[X] B] [IsScalarTower K K[X] B]
    [Module.Free K[X] B] [Module.Finite K[X] B]

/-- A geometric residue field consists precisely of constants. -/
theorem polynomialGeometric_residue_bijective (w : HeightOneSpectrum B) :
    Function.Bijective (algebraMap K (B ⧸ w.asIdeal)) := by
  letI : w.asIdeal.IsPrime := w.isPrime
  letI := polynomialOrder_quotient_finiteDimensional K B w.asIdeal w.ne_bot
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The residue homomorphism into the algebraically closed constant field. -/
noncomputable def polynomialGeometricResidue (w : HeightOneSpectrum B) : B →ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ w.asIdeal))
    (polynomialGeometric_residue_bijective K B w)).symm.toAlgHom.comp
      (Ideal.Quotient.mkₐ K w.asIdeal)

/-- The geometric residue homomorphism has exactly the given prime as kernel. -/
theorem polynomialGeometricResidue_ker (w : HeightOneSpectrum B) :
    RingHom.ker (polynomialGeometricResidue K B w) = w.asIdeal := by
  let e := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ w.asIdeal))
    (polynomialGeometric_residue_bijective K B w)
  ext b
  change e.symm (Ideal.Quotient.mk w.asIdeal b) = 0 ↔ b ∈ w.asIdeal
  constructor
  · intro h
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (e.symm.injective (h.trans (map_zero e.symm).symm))
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- A specified residue is equivalent to the corresponding constant difference lying in the prime. -/
theorem polynomialGeometricResidue_eq_iff (w : HeightOneSpectrum B) (b : B) (a : K) :
    polynomialGeometricResidue K B w b = a ↔ b - algebraMap K B a ∈ w.asIdeal := by
  rw [← polynomialGeometricResidue_ker K B w]
  change polynomialGeometricResidue K B w b = a ↔
    polynomialGeometricResidue K B w (b - algebraMap K B a) = 0
  rw [map_sub, AlgHom.commutes, sub_eq_zero]
  simp

/-- Subtracting the geometric residue gives a function vanishing at the actual finite place. -/
theorem polynomialGeometricResidue_sub_lt_one
    (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (w : HeightOneSpectrum B) (b : B) :
    w.valuation L (algebraMap B L (b - algebraMap K B (polynomialGeometricResidue K B w b))) < 1 := by
  exact (w.valuation_lt_one_iff_mem _).mpr
    ((polynomialGeometricResidue_eq_iff K B w b _).mp rfl)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
