import GaloisForLFunctions.HTGeometry.CenteredDiscriminantIdentification

/-!
# The square-class input of the base change, for the centered polynomial

The discriminant square root of the centered polynomial is the Vandermonde product of its roots, and
its square, read in the rational function field, is the Vandermonde polynomial squared.  So a square
root in the coefficient field of the discriminant times the constant coefficient would be a square
root there, which is excluded.

This is the square-class hypothesis of the base change step, in the form that step consumes it.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- **The square-class hypothesis for the centered generic polynomial.** -/
theorem no_sqrt_centered_disc_mul_constant [IsAlgClosed K] (hd : 3 ≤ d) :
    ∀ e : centeredCoeffField K d,
      algebraMap (centeredCoeffField K d) (centeredField K d) e =
        vandermondeProd (centeredRootIn K d) * vandermondeProd (centeredRootIn K d) →
      ¬ ∃ t : centeredCoeffField K d, e * centeredConstant K d (by omega) = t * t := by
  rintro e he ⟨t, ht⟩
  refine not_exists_sq_disc_mul_centeredConstant (K := K) (d := d) hd ?_
  refine ⟨(((t : centeredField K d) : SymmetricRationalField K d)), ?_⟩
  have hcoeE : (((e : centeredField K d) : SymmetricRationalField K d)) =
      algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)
        (vandermondePoly K d * vandermondePoly K d) := by
    have h : (((e : centeredField K d) : SymmetricRationalField K d)) =
        ((vandermondeProd (centeredRootIn K d) * vandermondeProd (centeredRootIn K d) :
          centeredField K d) : SymmetricRationalField K d) :=
      congrArg (fun x : centeredField K d => (x : SymmetricRationalField K d)) he
    rw [h]
    push_cast
    rw [coe_vandermondeProd_centeredRootIn]
  have hcoeT := congrArg
    (fun x : centeredCoeffField K d =>
      (((x : centeredField K d) : SymmetricRationalField K d))) ht
  push_cast at hcoeT
  rw [← hcoeE, ← coe_centeredConstant (K := K) (d := d) (by omega)]
  exact hcoeT

end GaloisForLFunctions.HTGeometry
