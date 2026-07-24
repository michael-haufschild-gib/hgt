import GaloisForLFunctions.HTGeometry.IsolatedKoszulCocycle

/-!
# The linear part of an isolated Koszul cocycle has zero diagonal

Complementing `isolatedKoszulBoundary_coeff_one` (the linear part of a boundary is antisymmetric), this
records the linear-level constraint on cocycles: the diagonal-free cocycle condition
`isolatedKoszulRelation_eq_zero_iff` forces the `k`-th axis component of `a k` to vanish, so in
particular its `coeff 1` vanishes.  In the `coeff-1` matrix picture `M_{ik} = ((a i)_k).coeff 1`, the
cocycles have zero diagonal and the boundaries are antisymmetric — the structural data of the linear
first Koszul cohomology.
-/

namespace GaloisForLFunctions

noncomputable section

variable {F : Type*} [Field F] {n : ℕ}

/-- The linear (`coeff 1`) diagonal of a first Koszul cocycle vanishes. -/
theorem isolatedKoszulRelation_eq_zero_coeff_one_diag
    {a : Fin (n + 2) → isolatedBoundarySubring F n}
    (hcocycle : isolatedKoszulRelation a = 0) (k : Fin (n + 2)) :
    ((a k : Fin (n + 2) → Polynomial F) k).coeff 1 = 0 := by
  rw [(isolatedKoszulRelation_eq_zero_iff a).mp hcocycle k, Polynomial.coeff_zero]

end

end GaloisForLFunctions
