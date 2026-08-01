import GaloisForLFunctions.HTGeometry.UniversalCenteredCoefficients
import GaloisForLFunctions.HTGeometry.GenericPolynomialSplitting

/-!
# Specialising the indeterminate coefficients to the generic ones

Sending each variable to the corresponding coefficient of the generic polynomial carries the monic
polynomial with indeterminate coefficients to the generic polynomial.

So every statement about the universal coefficients specialises to one about the generic ones, in
particular the effect of the centering shift.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] {d : ℕ}

/-- Sending each variable to the matching coefficient of the generic polynomial. -/
noncomputable def coeffSub (K : Type*) [Field K] (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] SymmetricRationalField K d :=
  MvPolynomial.aeval (fun j : Fin d => (genericMonicF K d).coeff (j : ℕ))

theorem coeffSub_X (j : Fin d) :
    coeffSub K d (MvPolynomial.X j) = (genericMonicF K d).coeff (j : ℕ) := by
  rw [coeffSub, MvPolynomial.aeval_X]

/-- **The specialisation carries the universal monic polynomial to the generic one.** -/
theorem map_coeffSub_universalMonic (hd : 0 < d) :
    Polynomial.map (coeffSub K d).toRingHom (universalMonic K d) = genericMonicF K d := by
  refine Polynomial.ext fun k => ?_
  rw [Polynomial.coeff_map]
  by_cases hk : k < d
  · rw [coeff_universalMonic_lt hk]
    exact coeffSub_X _
  · by_cases hkd : k = d
    · have h1 : (universalMonic K d).coeff k = 1 := by
        rw [hkd, ← natDegree_universalMonic (K := K) hd]
        exact (monic_universalMonic hd).coeff_natDegree
      have h2 : (genericMonicF K d).coeff k = 1 := by
        rw [hkd, ← natDegree_genericMonicF (K := K) (d := d)]
        exact (monic_genericMonicF (K := K) (d := d)).coeff_natDegree
      rw [h1, h2, map_one]
    · have h1 : (universalMonic K d).coeff k = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        rw [natDegree_universalMonic hd]
        omega
      have h2 : (genericMonicF K d).coeff k = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        rw [natDegree_genericMonicF]
        omega
      rw [h1, h2, map_zero]

end GaloisForLFunctions.HTGeometry
