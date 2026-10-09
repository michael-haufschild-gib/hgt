import GaloisForLFunctions.HTGeometry.AffineConstantVectorFieldTranslation
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.FactorialClosure

/-!
# Native constant vector fields satisfy the source termination condition

The existing parametrized-translation polynomial has only finitely many
coefficients. Its native Taylor-coefficient formula therefore proves local
nilpotence of every constant vector field, paying the source factorial-
closure and invariant-localization prerequisites for all root velocities.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial StableCoordinate

noncomputable section

variable {K ι : Type*} [Field K] [CharZero K]

/-- The native inverse-factorial coefficient is nonzero in the polynomial algebra. -/
theorem paperVectorField_invFactorial_ne_zero (m : ℕ) :
    invFactorialCast (MvPolynomial ι K) m ≠ 0 := by
  unfold invFactorialCast
  exact (map_ne_zero (algebraMap ℚ (MvPolynomial ι K))).mpr
    (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)))

/-- Every iterate above the native translation-polynomial degree vanishes. -/
theorem paperConstantVectorField_iterate_eq_zero
    (v : ι → K) (p : MvPolynomial ι K) (m : ℕ)
    (hm : (translationParameterized v p).natDegree < m) :
    ((constVectorField v : MvPolynomial ι K → MvPolynomial ι K)^[m]) p = 0 := by
  have h := Polynomial.coeff_eq_zero_of_natDegree_lt hm
  rw [coeff_translationParameterized] at h
  exact (mul_eq_zero.mp h).resolve_left (paperVectorField_invFactorial_ne_zero m)

/-- The source local-nilpotence premise is proved for every native constant vector field. -/
theorem paperConstantVectorField_locallyNilpotent (v : ι → K) :
    IsLocallyNilpotent (constVectorField v) := by
  intro p
  exact ⟨(translationParameterized v p).natDegree + 1,
    paperConstantVectorField_iterate_eq_zero v p _ (Nat.lt_succ_self _)⟩

end

end GaloisForLFunctions.HTGeometry
