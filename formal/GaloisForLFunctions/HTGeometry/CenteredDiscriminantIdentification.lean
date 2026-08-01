import GaloisForLFunctions.HTGeometry.CenteredDiscriminantNonSquare
import GaloisForLFunctions.HTGeometry.VandermondeFixed
import GaloisForLFunctions.HTGeometry.CenteredPolynomialOverCoefficients

/-!
# The Vandermonde product of the centered roots is the discriminant square root

Translating a family does not change its Vandermonde product, so the product over the centered roots
is the product over the generic roots, which is the Vandermonde polynomial read in the rational
function field.

Hence the square-class statement proved for the generic roots is a statement about the discriminant
square root of the centered polynomial, which is what the base change step compares against the
constant coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- **The Vandermonde product of the centered roots, read in the rational function field.** -/
theorem coe_vandermondeProd_centeredRootIn :
    ((vandermondeProd (centeredRootIn K d) : centeredField K d) :
      SymmetricRationalField K d) =
      algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) (vandermondePoly K d) := by
  have h1 : ((vandermondeProd (centeredRootIn K d) : centeredField K d) :
      SymmetricRationalField K d) = vandermondeProd (centeredRoot K d) := by
    have h := map_vandermondeProd_ringHom
      ((centeredField K d).val.toRingHom) (centeredRootIn K d)
    exact h
  have h2 : vandermondeProd (centeredRoot K d) = vandermondeProd (genericRoot K d) := by
    have hshift : (fun i => genericRoot K d i - genericAverage K d) = centeredRoot K d := by
      funext i
      rw [centeredRoot]
    rw [← hshift, vandermondeProd_sub_const]
  have h3 : vandermondeProd (genericRoot K d) =
      algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) (vandermondePoly K d) := by
    rw [vandermondePoly, map_vandermondeProd_ringHom
      (algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)) _]
    rfl
  rw [h1, h2, h3]

/-- The constant coefficient of the centered polynomial, inside the coefficient field. -/
noncomputable def centeredConstant (K : Type*) [Field K] [CharZero K] (d : ℕ) (hd : 0 < d) :
    centeredCoeffField K d :=
  centeredCoeffIn K d ⟨0, hd⟩

theorem coe_centeredConstant (hd : 0 < d) :
    (((centeredConstant K d hd : centeredCoeffField K d) : centeredField K d) :
      SymmetricRationalField K d) = (centeredMonicF K d).coeff 0 := rfl

end GaloisForLFunctions.HTGeometry
