import GaloisForLFunctions.HTGeometry.MultivariateRelationGrouping

/-!
# A nonvanishing grouped coefficient

The cascade separation criterion is driven by the existence of a point where one grouped coefficient
does not vanish.  The grouped coefficient at level `j` sums the monomial family over the fibre of
exponent `j` in the last variable, so a single monomial sitting in that fibre, with unit coefficient
evaluated at the all-ones point, contributes exactly one.

So the nonvanishing hypothesis is satisfiable at every level.
-/

namespace GaloisForLFunctions.HTGeometry

variable {k : ℕ}

/-- The exponent concentrated at the last variable. -/
def lastExponent (k N : ℕ) : Fin (k + 1) → ℕ :=
  fun i => if i = Fin.last k then N else 0

@[simp] theorem lastExponent_last (k N : ℕ) : lastExponent k N (Fin.last k) = N := by
  rw [lastExponent, if_pos rfl]

/-- **The grouped coefficient of a single unit monomial at the all-ones point is one.** -/
theorem groupedCoeff_lastExponent (N : ℕ) :
    groupedCoeff (k := k) {lastExponent k N} (fun _ => 1) (fun _ => 1) N = 1 := by
  classical
  rw [groupedCoeff, Finset.filter_singleton, if_pos (lastExponent_last k N),
    Finset.sum_singleton]
  simp

/-- Hence the cascade criterion's nonvanishing hypothesis is satisfiable at every level. -/
theorem groupedCoeff_lastExponent_ne_zero (N : ℕ) :
    groupedCoeff (k := k) {lastExponent k N} (fun _ => 1) (fun _ => 1) N ≠ 0 := by
  rw [groupedCoeff_lastExponent]
  exact one_ne_zero

/-- Existence form at the all-ones point. -/
theorem exists_groupedCoeff_ne_zero (N : ℕ) :
    ∃ (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → ℂ) (x : Fin (k + 1) → ℂ),
      groupedCoeff S A x N ≠ 0 :=
  ⟨_, _, _, groupedCoeff_lastExponent_ne_zero N⟩

end GaloisForLFunctions.HTGeometry
