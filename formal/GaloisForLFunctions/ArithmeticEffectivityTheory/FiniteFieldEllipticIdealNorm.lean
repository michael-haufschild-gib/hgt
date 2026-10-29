import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticIntegralClosure
import GaloisForLFunctions.HTGeometry.DedekindIdealNorm
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.FieldTheory.Finiteness

/-!
# Principal ideal norm and infinity degree of the actual curve

Every nonzero affine ideal has finite quotient. For a principal ideal the quotient
dimension is the degree of the polynomial algebra norm, so its cardinality is
exactly three raised to the pole degree at infinity.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

open Polynomial HTGeometry

noncomputable section

instance coordinateRing_infinite : Infinite CoordinateRing :=
  Infinite.of_injective (algebraMap Constants[X] CoordinateRing)
    (FaithfulSMul.algebraMap_injective Constants[X] CoordinateRing)

private def affineBasis : Module.Basis (Fin 2) Constants[X] CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.basis curve.toAffine

/-- Smith decomposition makes every nonzero affine ideal quotient finite-dimensional. -/
theorem affine_quotient_finiteDimensional (I : Ideal CoordinateRing) (hI : I ≠ ⊥) :
    Module.Finite Constants (CoordinateRing ⧸ I) := by
  letI (i : Fin 2) :
      Module.Finite Constants
        (Constants[X] ⧸ Ideal.span {I.smithCoeffs affineBasis hI i}) :=
    PowerBasis.finite (AdjoinRoot.powerBasis (I.smithCoeffs_ne_zero affineBasis hI i))
  let e := Ideal.quotientEquivDirectSum Constants affineBasis hI
  exact Module.Finite.equiv e.symm

theorem affine_quotient_finite (I : Ideal CoordinateRing) (hI : I ≠ ⊥) :
    Finite (CoordinateRing ⧸ I) := by
  letI := affine_quotient_finiteDimensional I hI
  exact Module.finite_of_finite Constants

/-- The actual affine ideal norm uses finite residue cardinalities in characteristic three. -/
def affineIdealNorm : Ideal CoordinateRing →*₀ ℕ := idealCardinality CoordinateRing

theorem affineIdealNorm_principal (a : CoordinateRing) (ha : a ≠ 0) :
    affineIdealNorm (Ideal.span {a}) = 3 ^ (Algebra.norm Constants[X] a).natDegree := by
  letI := affine_quotient_finiteDimensional (Ideal.span {a})
    (Ideal.span_singleton_eq_bot.not.mpr ha)
  change Nat.card (CoordinateRing ⧸ Ideal.span {a}) = _
  rw [Module.natCard_eq_pow_finrank (K := Constants),
    finrank_quotient_span_eq_natDegree_norm affineBasis ha]
  congr 1
  simpa only [Nat.card_eq_fintype_card] using ZMod.card 3

theorem affine_norm_ne_zero (a : CoordinateRing) (ha : a ≠ 0) :
    Algebra.norm Constants[X] a ≠ 0 := by
  intro h
  apply ha
  apply (poleDegree_eq_bot_iff a).mp
  simp only [poleDegree, h, Polynomial.degree_zero]

/-- The finite principal-ideal norm exponent is precisely the proved infinity pole degree. -/
theorem affine_principal_norm_exponent (a : CoordinateRing) (ha : a ≠ 0) :
    poleDegree a = ((Algebra.norm Constants[X] a).natDegree : WithBot ℕ) :=
  Polynomial.degree_eq_natDegree (affine_norm_ne_zero a ha)

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
