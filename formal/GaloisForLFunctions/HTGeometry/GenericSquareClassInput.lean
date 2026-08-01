import GaloisForLFunctions.HTGeometry.SymmetricPartRadical
import GaloisForLFunctions.HTGeometry.SymmetricCoefficientFractionModel
import GaloisForLFunctions.HTGeometry.VandermondeFixed
import GaloisForLFunctions.HTGeometry.GenericPolynomialSplitting

/-!
# The square-class input for the generic polynomial

The Vandermonde product of the generic roots is the Vandermonde polynomial read in the rational
function field, and the top elementary symmetric function is the constant coefficient up to sign.
So a square root in the symmetric part of the discriminant times that coefficient would be a square
root inside the coefficient field, which is excluded.

This is the square-class hypothesis of the base change step for the generic polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {d : ℕ}

theorem vandermondeProd_genericRoot :
    vandermondeProd (genericRoot K d) =
      algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) (vandermondePoly K d) := by
  rw [vandermondePoly, map_vandermondeProd_ringHom
    (algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)) _]
  rfl

/-- **The square-class hypothesis for the generic polynomial.**  Stated for any element of the
symmetric part representing the top elementary symmetric function. -/
theorem no_sqrt_generic_disc_mul_esymm (hd : 0 < d) (c : symmetricPart K d)
    (hc : (c : SymmetricRationalField K d) = esymmGen K d (topIndex d hd)) :
    ∀ e : symmetricPart K d,
      algebraMap (symmetricPart K d) (SymmetricRationalField K d) e =
        vandermondeProd (genericRoot K d) * vandermondeProd (genericRoot K d) →
      ¬ ∃ t : symmetricPart K d, e * c = t * t := by
  rintro e he ⟨t, ht⟩
  refine no_sqrt_disc_mul_esymmTop_of_mem_symmetricPartField (K := K) (d := d) hd ?_
  refine ⟨(t : SymmetricRationalField K d), t.2, ?_⟩
  have hcoeE : (e : SymmetricRationalField K d) =
      algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)
        (vandermondePoly K d * vandermondePoly K d) := by
    have h : (e : SymmetricRationalField K d) =
        vandermondeProd (genericRoot K d) * vandermondeProd (genericRoot K d) := he
    rw [h, vandermondeProd_genericRoot, map_mul]
  have hcoeT := congrArg
    (fun x : symmetricPart K d => (x : SymmetricRationalField K d)) ht
  push_cast at hcoeT
  rw [← hcoeE, ← hc]
  exact hcoeT

end GaloisForLFunctions.HTGeometry
