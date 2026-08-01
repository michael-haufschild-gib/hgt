import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Parametrising the roots that sum to zero

The tuples whose entries sum to zero are parametrised by their first entries, the last being minus
their sum.  Substituting that parametrisation into a polynomial in all the entries is the algebra
map that reads it on the hyperplane.

The first elementary symmetric function becomes zero under this substitution, which is what makes
the remaining ones the coefficients of a centered polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [CommRing K] {m : ℕ}

/-- The parametrisation of the sum-zero hyperplane: the last coordinate is minus the sum of the
others. -/
noncomputable def sumZeroCoord (K : Type*) [CommRing K] (m : ℕ) (i : Fin (m + 1)) :
    MvPolynomial (Fin m) K :=
  if h : (i : ℕ) < m then MvPolynomial.X ⟨i, h⟩ else -∑ j : Fin m, MvPolynomial.X j

/-- Reading a polynomial in `m + 1` variables on the sum-zero hyperplane. -/
noncomputable def sumZeroRestrict (K : Type*) [CommRing K] (m : ℕ) :
    MvPolynomial (Fin (m + 1)) K →ₐ[K] MvPolynomial (Fin m) K :=
  MvPolynomial.aeval (sumZeroCoord K m)

theorem sumZeroRestrict_X (i : Fin (m + 1)) :
    sumZeroRestrict K m (MvPolynomial.X i) = sumZeroCoord K m i := by
  rw [sumZeroRestrict, MvPolynomial.aeval_X]

/-- **The parametrised coordinates sum to zero.** -/
theorem sum_sumZeroCoord : ∑ i : Fin (m + 1), sumZeroCoord K m i = 0 := by
  classical
  have hlast : sumZeroCoord K m (Fin.last m) = -∑ j : Fin m, MvPolynomial.X j := by
    rw [sumZeroCoord, dif_neg (by simp)]
  rw [Fin.sum_univ_castSucc, hlast]
  have hcast : ∀ j : Fin m, sumZeroCoord K m (Fin.castSucc j) = MvPolynomial.X j := by
    intro j
    rw [sumZeroCoord, dif_pos (by exact j.2)]
    congr 1
  rw [Finset.sum_congr rfl (fun j _ => hcast j)]
  ring

/-- **The first elementary symmetric function vanishes on the hyperplane.** -/
theorem sumZeroRestrict_esymm_one :
    sumZeroRestrict K m (MvPolynomial.esymm (Fin (m + 1)) K 1) = 0 := by
  rw [MvPolynomial.esymm_one, map_sum]
  simp only [sumZeroRestrict_X]
  exact sum_sumZeroCoord

end GaloisForLFunctions.HTGeometry
