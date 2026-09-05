import GaloisForLFunctions.HTGeometry.UniversalToGeneric
import GaloisForLFunctions.HTGeometry.GenericCoeffPred
import GaloisForLFunctions.HTGeometry.CenteredCoefficientIndependence
import GaloisForLFunctions.HTGeometry.CenteredIsTaylorShift
import GaloisForLFunctions.HTGeometry.GenericAverageSymmetric

/-!
# The centered coefficients of the generic polynomial are algebraically independent

Specialising the indeterminate coefficients to the generic ones carries the universal centering
shift to the average of the roots, hence the universal centered coefficients to the coefficients of
the centered generic polynomial.

Since that specialisation is injective — the elementary symmetric functions being algebraically
independent — the independence proved for the universal centered coefficients descends.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial


variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

omit [CharZero K] in
theorem coeffSub_centeringShift (hd : 0 < d) :
    coeffSub K d (centeringShift K d hd) = genericAverage K d := by
  rw [centeringShift, map_neg, map_smul, genericAverage_eq hd]
  congr 2
  have h : ((⟨d - 1, by omega⟩ : Fin d) : ℕ) = d - 1 := rfl
  rw [coeffSub_X, h]

omit [CharZero K] in
/-- **The specialisation carries the universal centered coefficients to the centered ones.** -/
theorem coeffSub_universalCenteredCoeff (hd : 0 < d) (k : ℕ) :
    coeffSub K d (universalCenteredCoeff K d hd k) = (centeredMonicF K d).coeff k := by
  have h : Polynomial.map (coeffSub K d).toRingHom
      (Polynomial.taylor (centeringShift K d hd) (universalMonic K d)) =
      centeredMonicF K d := by
    rw [map_taylor', map_coeffSub_universalMonic hd]
    have hshift : (coeffSub K d).toRingHom (centeringShift K d hd) = genericAverage K d :=
      coeffSub_centeringShift hd
    rw [hshift]
    exact taylor_genericMonicF
  calc coeffSub K d (universalCenteredCoeff K d hd k)
      = (Polynomial.map (coeffSub K d).toRingHom
          (Polynomial.taylor (centeringShift K d hd) (universalMonic K d))).coeff k :=
        (Polynomial.coeff_map _ _).symm
    _ = (centeredMonicF K d).coeff k := by rw [h]

end GaloisForLFunctions.HTGeometry
