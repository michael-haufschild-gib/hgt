import GaloisForLFunctions.HTGeometry.IsolatedKoszulCocycle

/-!
# The linear part of an isolated Koszul boundary is antisymmetric

Reading the boundary axis-component formula `isolatedKoszulBoundary_val_apply` at the linear
(`coeff 1`) level shows that the `X`-linear part of a Koszul boundary is an antisymmetric matrix in
the position/axis indices `(i,k)`: it is `−(c i k)ₖ.coeff 0` above the diagonal and `+(c k i)ₖ.coeff 0`
below, and `0` on the diagonal.  This is the structural constraint that the reduced-`H⁰` detectors read
off, and the algebraic input for the `X`-linear graded piece of the first Koszul cohomology where the
Hochster classes live.
-/

namespace GaloisForLFunctions

noncomputable section

variable {F : Type*} [Field F] {n : ℕ}

/-- The linear (`coeff 1`) part of a Koszul boundary is antisymmetric in `(i,k)`. -/
theorem isolatedKoszulBoundary_coeff_one
    (c : Fin (n + 2) → Fin (n + 2) → isolatedBoundarySubring F n) (i k : Fin (n + 2)) :
    ((isolatedKoszulBoundary c i : Fin (n + 2) → Polynomial F) k).coeff 1
      = if i < k then -((c i k : Fin (n + 2) → Polynomial F) k).coeff 0
        else if k < i then ((c k i : Fin (n + 2) → Polynomial F) k).coeff 0 else 0 := by
  rw [isolatedKoszulBoundary_val_apply]
  split_ifs with h1 h2 <;> simp [Polynomial.coeff_mul_X, Polynomial.coeff_neg]

end

end GaloisForLFunctions
