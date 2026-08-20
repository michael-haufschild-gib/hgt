import GaloisForLFunctions.RHTower.DeningerArithmeticCofiniteDivisorSplitting
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Quotient reconstruction for cofinite divisors

The cofinite divisor sequence identifies a global finitely supported divisor modulo the retained
prime coordinates with its residue profile on the complementary coordinates.  In the arithmetic
specialization `R = ℤ`, this is the quotient form of the divisor sequence on `Spec ℤ[S⁻¹]`.
-/

namespace RHTower

universe u v

noncomputable section

variable {R : Type u} {ι : Type v} [CommRing R]
variable (S : ι → Prop)

/-- **Cofinite divisor local-global equivalence.** A finitely supported divisor modulo the
coordinates retained by `S` is linearly equivalent to its finitely supported residue profile on
the complementary coordinates. -/
noncomputable def deningerCofiniteDivisorQuotientEquiv :
    ((ι →₀ R) ⧸ (LinearMap.range (deningerInsideDivisorEmbedding (R := R) S))) ≃ₗ[R]
      (DeningerOutsidePrime S →₀ R) :=
  (Submodule.quotEquivOfEq _ _
    (LinearMap.exact_iff.mp (deningerCofiniteDivisor_exact (R := R) S)).symm).trans
      (LinearMap.quotKerEquivOfSurjective (deningerOutsideResidue (R := R) S)
        (deningerOutsideResidue_surjective (R := R) S))

/-- The cofinite divisor quotient equivalence is induced by outside-coordinate restriction. -/
theorem deningerCofiniteDivisorQuotientEquiv_mk (x : ι →₀ R) :
    deningerCofiniteDivisorQuotientEquiv (R := R) S (Submodule.Quotient.mk x) =
      deningerOutsideResidue (R := R) S x := by
  simp [deningerCofiniteDivisorQuotientEquiv]

end
