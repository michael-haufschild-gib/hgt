import GaloisForLFunctions.HTGeometry.SiegelSwap
import GaloisForLFunctions.HTGeometry.PotentialDescent

/-!
# The reduction potential

The potential driving lattice basis reduction is the product of the determinants of all the leading
minors.  Since those determinants are attached to the form and not to a chosen decomposition, so is
the potential — which is what makes "minimise the potential over the orbit" a well-posed
instruction.

In Jacobi coordinates it is a product of powers of the diagonal, each `dₘ` appearing once for every
leading minor that contains it.

* `potentialOf` : the product of the leading minors.
* `potentialOf_form` : **its value in Jacobi coordinates.**
* `potentialOf_pos` : **it is positive.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The product of the determinants of all leading minors. -/
noncomputable def potentialOf (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∏ k : Fin (n + 1), (leadingBlock (Fin.is_le k) A).det

/-- **The potential in Jacobi coordinates.** -/
theorem potentialOf_form (J : JacobiData n) :
    potentialOf J.form
      = ∏ k : Fin (n + 1), ∏ m : Fin (k : ℕ), J.d (Fin.castLE (Fin.is_le k) m) := by
  refine Finset.prod_congr rfl fun k _ => ?_
  exact det_leadingBlock_form (Fin.is_le k) J

/-- **The potential is positive.** -/
theorem potentialOf_pos (J : JacobiData n) : 0 < potentialOf J.form := by
  rw [potentialOf_form]
  exact Finset.prod_pos fun k _ => Finset.prod_pos fun m _ => J.pos _

/-- The potential is a function of the form alone: two Jacobi data for the same form give the same
potential.  (Immediate from the definition, which never mentions a decomposition.) -/
theorem potentialOf_congr {J J' : JacobiData n} (h : J.form = J'.form) :
    potentialOf J.form = potentialOf J'.form := by rw [h]

end GaloisForLFunctions.HTGeometry
