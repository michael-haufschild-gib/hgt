import GaloisForLFunctions.HTGeometry.ScalarMonomial
import GaloisForLFunctions.HTGeometry.ExponentialTowerModel

/-!
# The tower monomial has monomial shape

`towerMonomial k = ∏_{1 ≤ i ≤ k} X i` is a scalar monomial, and finite products of scalar monomials
are scalar monomials.

These are the factors that appear in the determinant reduction of `ExponentialTowerUnitCost`: each
Bell step contributes `(−1)^a`, a tower monomial, and a power of a tower monomial.  Carrying
`IsScalarMonomial` through that reduction therefore only needs the reduction's own equation together
with these closure facts.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- A finite product of scalar monomials is a scalar monomial. -/
theorem IsScalarMonomial.prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial ℕ ℂ)
    (h : ∀ i ∈ s, IsScalarMonomial (f i)) : IsScalarMonomial (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isScalarMonomial_one
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **The tower monomial is a scalar monomial.** -/
theorem isScalarMonomial_towerMonomial (k : ℕ) :
    IsScalarMonomial (towerMonomial k : MvPolynomial ℕ ℂ) := by
  rw [towerMonomial]
  exact IsScalarMonomial.prod _ _ fun i _ => isScalarMonomial_X i

end GaloisForLFunctions.HTGeometry
