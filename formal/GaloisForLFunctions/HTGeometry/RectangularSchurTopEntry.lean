import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic

/-!
# The top variable of a rectangular Jacobi--Trudi matrix occurs once

In the rectangular Toeplitz section the entry index `n + r - i` is largest at the bottom-left corner,
and it reaches its largest value only there.

So the determinant is a polynomial of degree one in that variable, with the complementary minor as
its coefficient — the reduction of irreducibility to a coprimality of that minor with the remainder.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Zero K]

/-- **The largest index of the rectangular Toeplitz section is attained only at the corner.** -/
theorem rectangularSchurToeplitz_index_eq_top {n m : ℕ} {r i : Fin m}
    (hle : (i : ℕ) ≤ n + (r : ℕ)) (htop : n + (r : ℕ) - (i : ℕ) = n + m - 1) :
    (r : ℕ) = m - 1 ∧ (i : ℕ) = 0 := by
  have hr := r.isLt
  have hi := i.isLt
  constructor <;> omega

/-- **Off the corner the entry index is strictly smaller.** -/
theorem rectangularSchurToeplitz_index_lt_top {n m : ℕ} {r i : Fin m}
    (hle : (i : ℕ) ≤ n + (r : ℕ)) (hne : ¬ ((r : ℕ) = m - 1 ∧ (i : ℕ) = 0)) :
    n + (r : ℕ) - (i : ℕ) < n + m - 1 := by
  have hr := r.isLt
  have hi := i.isLt
  rcases Classical.em ((r : ℕ) = m - 1) with hrm | hrm
  · have hi0 : (i : ℕ) ≠ 0 := fun h => hne ⟨hrm, h⟩
    omega
  · omega

/-- **The corner entry is the top variable.** -/
theorem rectangularSchurToeplitz_corner (h : ℕ → K) {n m : ℕ} (hm : 0 < m) :
    rectangularSchurToeplitz h n m ⟨m - 1, by omega⟩ ⟨0, by omega⟩ = h (n + m - 1) := by
  rw [rectangularSchurToeplitz, if_pos (by simp)]
  congr 1
  simp only []
  omega

/-! ## The determinant does not vanish identically -/

/-- **At the unit tail the Toeplitz section is the identity.**  Setting the `n`-th complete
homogeneous coefficient to one and all others to zero turns the rectangular Jacobi--Trudi matrix
into the identity matrix. -/
theorem rectangularSchurToeplitz_unit_tail {R : Type*} [CommRing R] [DecidableEq R] (n m : ℕ) :
    rectangularSchurToeplitz (fun k => if k = n then (1 : R) else 0) n m = 1 := by
  refine Matrix.ext fun r i => ?_
  rw [rectangularSchurToeplitz, Matrix.one_apply]
  have hr := r.isLt
  have hi := i.isLt
  by_cases hle : (i : ℕ) ≤ n + (r : ℕ)
  · rw [if_pos hle]
    by_cases hri : r = i
    · have hval : (r : ℕ) = (i : ℕ) := by rw [hri]
      rw [if_pos hri, if_pos (by omega : n + (r : ℕ) - (i : ℕ) = n)]
    · rw [if_neg hri, if_neg ?_]
      intro hcon
      exact hri (Fin.ext (by omega))
  · rw [if_neg hle, if_neg ?_]
    intro hcon
    exact hle (by rw [hcon]; omega)

end GaloisForLFunctions.HTGeometry
