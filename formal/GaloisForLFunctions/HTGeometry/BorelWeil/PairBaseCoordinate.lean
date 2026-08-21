import GaloisForLFunctions.HTGeometry.BorelWeil.FibreCoordinate

/-!
# The base coordinates of a `ℙ¹` fibration

The functions regular on both cells of a coset pair are the ones pulled back from the base of the
fibration `G/B → G/P_i`.  Two families of them are visible directly: the cell coordinates whose
denominator is a leading minor other than the `(i+1)`-st — those minors agree up to sign with the
ones of the reflected cell — and, for each row below the step, the ratio of the `(i+2)`-minor with
rows `(0,…,i−1,i+1,r)` to the `(i+2)`-nd leading minor.  On the big cell the latter is
`t · c_{r,i+1} − c_{r,i}`, so modulo the fibre coordinate it recovers the one coordinate that is not
already a base coordinate.

## Main results

* `det_of_almost_lowerTriangular` — a determinant that is lower triangular apart from one entry.
* `leadingMinorMat_pairUpdate_of_isLowerUni` — the `(i+2)`-minor of a lower unitriangular matrix
  with rows `(0,…,i−1,i+1,b)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- **A determinant that is lower triangular apart from one entry.**  If a matrix vanishes above the
diagonal except at the single position `(i, i')` with `i' = i + 1`, has `1` there, and has unit
diagonal away from `i` and `i'`, its determinant is the `2 × 2` determinant of the exceptional
block. -/
theorem det_of_almost_lowerTriangular {M : Matrix (Fin N) (Fin N) k} {i i' : Fin N}
    (hii' : (i' : ℕ) = (i : ℕ) + 1) (hone : M i i' = 1)
    (hzero : ∀ ρ c : Fin N, (ρ : ℕ) < (c : ℕ) → ¬ (ρ = i ∧ c = i') → M ρ c = 0)
    (hdiag : ∀ ρ : Fin N, ρ ≠ i → ρ ≠ i' → M ρ ρ = 1) :
    M.det = M i i * M i' i' - M i' i := by
  classical
  have hne : i ≠ i' := by
    intro hc
    rw [hc] at hii'
    omega
  have hswapi : (Equiv.swap i i') i = i' := Equiv.swap_apply_left i i'
  have hswapi' : (Equiv.swap i i') i' = i := Equiv.swap_apply_right i i'
  have hSdet : (M.submatrix id ⇑(Equiv.swap i i')).det = - M.det := by
    rw [Matrix.det_permute', Equiv.Perm.sign_swap hne]
    simp
  have hTdet : ((M.submatrix id ⇑(Equiv.swap i i')).updateCol i'
      (fun ρ => (M.submatrix id ⇑(Equiv.swap i i')) ρ i'
        + (-(M i i)) • (M.submatrix id ⇑(Equiv.swap i i')) ρ i)).det
      = (M.submatrix id ⇑(Equiv.swap i i')).det :=
    Matrix.det_updateCol_add_smul_self _ (Ne.symm hne) _
  have hTapply : ∀ ρ c : Fin N,
      ((M.submatrix id ⇑(Equiv.swap i i')).updateCol i'
        (fun ρ => (M.submatrix id ⇑(Equiv.swap i i')) ρ i'
          + (-(M i i)) • (M.submatrix id ⇑(Equiv.swap i i')) ρ i)) ρ c
        = if c = i' then M ρ i + (-(M i i)) * M ρ i' else M ρ ((Equiv.swap i i') c) := by
    intro ρ c
    rw [Matrix.updateCol_apply]
    by_cases hc : c = i'
    · rw [if_pos hc, if_pos hc]
      simp only [Matrix.submatrix_apply, id_eq, hswapi, hswapi', smul_eq_mul]
    · rw [if_neg hc, if_neg hc]
      simp only [Matrix.submatrix_apply, id_eq]
  have htri : ((M.submatrix id ⇑(Equiv.swap i i')).updateCol i'
      (fun ρ => (M.submatrix id ⇑(Equiv.swap i i')) ρ i'
        + (-(M i i)) • (M.submatrix id ⇑(Equiv.swap i i')) ρ i)).BlockTriangular
      (OrderDual.toDual : Fin N → (Fin N)ᵒᵈ) := by
    intro ρ c hrc
    have hlt : ρ < c := hrc
    rw [hTapply]
    by_cases hc : c = i'
    · rw [if_pos hc]
      have hrle : (ρ : ℕ) ≤ (i : ℕ) := by
        have : (ρ : ℕ) < (c : ℕ) := hlt
        rw [hc] at this
        omega
      by_cases hri : ρ = i
      · rw [hri, hone, mul_one]
        ring
      · have hrlt : (ρ : ℕ) < (i : ℕ) := by
          have : (ρ : ℕ) ≠ (i : ℕ) := fun hcon => hri (Fin.ext hcon)
          omega
        have h1 : M ρ i = 0 := hzero ρ i hrlt (fun hcon => hri hcon.1)
        have h2 : M ρ i' = 0 := hzero ρ i' (by omega) (fun hcon => hri hcon.1)
        rw [h1, h2, mul_zero, add_zero]
    · rw [if_neg hc]
      by_cases hci : c = i
      · rw [hci, hswapi]
        refine hzero ρ i' ?_ ?_
        · have : (ρ : ℕ) < (c : ℕ) := hlt
          rw [hci] at this
          omega
        · rintro ⟨hcon, -⟩
          exact hci (by rw [← hcon] at hlt; exact absurd hlt (lt_irrefl _) )
      · rw [Equiv.swap_apply_of_ne_of_ne hci hc]
        exact hzero ρ c hlt (fun hcon => hc hcon.2)
  have hdiagT : ∀ ρ : Fin N,
      ((M.submatrix id ⇑(Equiv.swap i i')).updateCol i'
        (fun ρ => (M.submatrix id ⇑(Equiv.swap i i')) ρ i'
          + (-(M i i)) • (M.submatrix id ⇑(Equiv.swap i i')) ρ i)) ρ ρ
        = if ρ = i' then M i' i + (-(M i i)) * M i' i' else 1 := by
    intro ρ
    rw [hTapply]
    by_cases hri' : ρ = i'
    · rw [if_pos hri', if_pos hri', hri']
    · rw [if_neg hri', if_neg hri']
      by_cases hri : ρ = i
      · rw [hri, hswapi, hone]
      · rw [Equiv.swap_apply_of_ne_of_ne hri hri']
        exact hdiag ρ hri hri'
  have hprod : ((M.submatrix id ⇑(Equiv.swap i i')).updateCol i'
      (fun ρ => (M.submatrix id ⇑(Equiv.swap i i')) ρ i'
        + (-(M i i)) • (M.submatrix id ⇑(Equiv.swap i i')) ρ i)).det
      = M i' i + (-(M i i)) * M i' i' := by
    rw [Matrix.det_of_lowerTriangular _ htri,
      Finset.prod_congr rfl fun ρ (_ : ρ ∈ Finset.univ) => hdiagT ρ,
      Finset.prod_eq_single i' (fun ρ _ hρ => by rw [if_neg hρ]) (fun h => absurd
        (Finset.mem_univ i') h), if_pos rfl]
  rw [hTdet, hSdet] at hprod
  have : -M.det = M i' i + (-(M i i)) * M i' i' := hprod
  linarith [this]

end GaloisForLFunctions.HTGeometry.BorelWeil
