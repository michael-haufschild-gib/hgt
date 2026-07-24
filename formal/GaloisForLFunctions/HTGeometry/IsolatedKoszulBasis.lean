import GaloisForLFunctions.HTGeometry.IsolatedKoszulCocycle

/-!
# The base-to-component basis cycles are diagonal-free

The canonical Hochster representatives `isolatedDisconnectCycleBasis j` (the `j`-th base-to-component
connection, `x_{j+1}` at position `0`) have zero axis-diagonal — each `(basis j)ₖ` has vanishing
`k`-th component — hence are first Koszul cycles by the diagonal-free cocycle characterization
`isolatedKoszulRelation_eq_zero_iff`.  This checks the cocycle characterization against the concrete
Hochster basis.
-/

namespace GaloisForLFunctions

noncomputable section

variable {F : Type*} [Field F] {n : ℕ}

/-- The base-to-component basis cycles are diagonal-free. -/
theorem isolatedDisconnectCycleBasis_diagonal_free (j : Fin (n + 1)) (k : Fin (n + 2)) :
    ((isolatedDisconnectCycleBasis (F := F) j) k : Fin (n + 2) → Polynomial F) k = 0 := by
  by_cases hk : k = 0
  · subst hk
    show ((isolatedBoundaryX (F := F) j.succ : Fin (n + 2) → Polynomial F) 0) = 0
    rw [isolatedBoundaryX_apply, if_neg (Fin.succ_ne_zero j).symm]
  · show ((if k = 0 then isolatedBoundaryX (F := F) j.succ else 0 :
      isolatedBoundarySubring F n) : Fin (n + 2) → Polynomial F) k = 0
    rw [if_neg hk]
    rfl

/-- The base-to-component cycles are first Koszul cycles, via the diagonal-free characterization. -/
theorem isolatedKoszulRelation_disconnectCycleBasis_of_diagonal_free (j : Fin (n + 1)) :
    isolatedKoszulRelation (isolatedDisconnectCycleBasis (F := F) j) = 0 :=
  (isolatedKoszulRelation_eq_zero_iff _).mpr (isolatedDisconnectCycleBasis_diagonal_free j)

end

end GaloisForLFunctions
