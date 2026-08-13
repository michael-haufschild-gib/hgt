import GaloisForLFunctions.RHTower.DeningerHazewinkelLowTailCoordinates

namespace RHTower
noncomputable section

def deningerHazewinkelPenultimateRow (k : ℕ) : Fin (k + 2) :=
  ⟨k, by omega⟩

theorem deningerHazewinkelPenultimateCofactor (k s : ℕ) :
    ((deningerHazewinkelSpecialMatrix (k + 1) s).submatrix
      (deningerHazewinkelPenultimateRow k).succAbove
      (Fin.last (k + 1)).succAbove).det =
      deningerHazewinkelNextCofactor k := by
  rw [deningerHazewinkelNextCofactor]
  congr 1
  ext i j
  rw [Matrix.submatrix_apply, Fin.succAbove_last_apply]
  by_cases hi : i = Fin.last k
  · subst i
    have hpen : deningerHazewinkelPenultimateRow k ≠ Fin.last (k + 1) := by
      intro h
      have := congrArg Fin.val h
      simp [deningerHazewinkelPenultimateRow] at this
    rw [Fin.succAbove_ne_last_last hpen]
    simp [deningerHazewinkelSpecialMatrix,
      deningerHazewinkelNextCofactorMatrix]
  · have hilt : i.val < k := by
      have hile : i.val ≤ k := Nat.le_of_lt_succ i.isLt
      exact lt_of_le_of_ne hile (fun h => hi (Fin.ext h))
    rw [Fin.succAbove_of_castSucc_lt]
    · simp [deningerHazewinkelSpecialMatrix,
        deningerHazewinkelNextCofactorMatrix, hi]
    · exact hilt

/-- Terms strictly below the second pivot in the special-minor Laplace expansion. -/
def deningerHazewinkelSecondLaplaceRemainder (k s : ℕ) :
    MvPolynomial ℕ ℤ :=
  ∑ i ∈ ((Finset.univ.erase (Fin.last (k + 1))).erase
      (deningerHazewinkelPenultimateRow k)),
    (-1) ^ (i.val + (k + 1)) *
      deningerHazewinkelUniversalCoeff (i.val + s) *
      ((deningerHazewinkelSpecialMatrix (k + 1) s).submatrix
        i.succAbove (Fin.last (k + 1)).succAbove).det

/-- Exact two-pivot identity.  Past the boundary minor, the next surviving coefficient is the
negative adjacent cofactor `-E_(k+1)`. -/
theorem deningerHazewinkelSpecialMinor_second_pivot
    {k s : ℕ} (hks : k + 2 ≤ s) :
    deningerHazewinkelSpecialMinor (k + 1) s =
      deningerHazewinkelLeadingDeterminant (k + 1) *
          MvPolynomial.X (k + s) -
        deningerHazewinkelNextCofactor k *
          MvPolynomial.X (k + s - 1) +
        deningerHazewinkelSecondLaplaceRemainder k s := by
  rw [deningerHazewinkelSpecialMinor_pivot_laplace,
    deningerHazewinkelUniversalCoeff_pivot (by omega : 1 ≤ k + 1)]
  have hpen : deningerHazewinkelPenultimateRow k ∈
      (Finset.univ.erase (Fin.last (k + 1))) := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    have := congrArg Fin.val h
    simp [deningerHazewinkelPenultimateRow] at this
  rw [deningerHazewinkelSpecialLaplaceRemainder,
    ← Finset.add_sum_erase
      (Finset.univ.erase (Fin.last (k + 1)))
      (fun i : Fin (k + 2) =>
        (-1) ^ (i.val + (k + 1)) *
          deningerHazewinkelUniversalCoeff (i.val + s) *
          ((deningerHazewinkelSpecialMatrix (k + 1) s).submatrix
            i.succAbove (Fin.last (k + 1)).succAbove).det)
      hpen]
  rw [deningerHazewinkelPenultimateCofactor,
    show deningerHazewinkelUniversalCoeff
      ((deningerHazewinkelPenultimateRow k).val + s) =
        MvPolynomial.X (k + s - 1) by
      rw [show (deningerHazewinkelPenultimateRow k).val + s =
        (k + s - 1) + 1 by
          simp [deningerHazewinkelPenultimateRow]
          omega]
      rfl]
  simp only [deningerHazewinkelPenultimateRow,
    show (-1 : MvPolynomial ℕ ℤ) ^ (k + (k + 1)) = -1 by
      rw [show k + (k + 1) = 2 * k + 1 by omega, pow_succ, pow_mul]
      simp]
  have hindex : k + 1 + s - 1 = k + s := by omega
  rw [hindex]
  rw [deningerHazewinkelSecondLaplaceRemainder]
  simp only [deningerHazewinkelPenultimateRow]
  ring

/-- Every variable in the two-pivot remainder precedes the second pivot. -/
theorem deningerHazewinkelSecondLaplaceRemainder_vars_lt
    {k s v : ℕ} (hks : k + 2 ≤ s)
    (hv : v ∈ (deningerHazewinkelSecondLaplaceRemainder k s).vars) :
    v < k + s - 1 := by
  rw [deningerHazewinkelSecondLaplaceRemainder] at hv
  have hvsum := MvPolynomial.vars_sum_subset
    ((Finset.univ.erase (Fin.last (k + 1))).erase
      (deningerHazewinkelPenultimateRow k))
    (fun i : Fin (k + 2) =>
      (-1) ^ (i.val + (k + 1)) *
        deningerHazewinkelUniversalCoeff (i.val + s) *
        ((deningerHazewinkelSpecialMatrix (k + 1) s).submatrix
          i.succAbove (Fin.last (k + 1)).succAbove).det) hv
  simp only [Finset.mem_biUnion] at hvsum
  obtain ⟨i, hi, hvterm⟩ := hvsum
  have hi' := Finset.mem_erase.mp hi
  have hilast := Finset.mem_erase.mp hi'.2
  have hilt : i.val < k := by
    have hile : i.val ≤ k + 1 := Nat.le_of_lt_succ i.isLt
    have hneLast : i.val ≠ k + 1 := by
      intro h
      exact hilast.1 (Fin.ext h)
    have hnePen : i.val ≠ k := by
      intro h
      exact hi'.1 (Fin.ext (by simpa [deningerHazewinkelPenultimateRow] using h))
    omega
  have hvouter := MvPolynomial.vars_mul
    ((-1) ^ (i.val + (k + 1)) *
      deningerHazewinkelUniversalCoeff (i.val + s))
    (((deningerHazewinkelSpecialMatrix (k + 1) s).submatrix
      i.succAbove (Fin.last (k + 1)).succAbove).det) hvterm
  rcases Finset.mem_union.mp hvouter with hvleft | hvdet
  · have hvinner := MvPolynomial.vars_mul
      ((-1) ^ (i.val + (k + 1)) : MvPolynomial ℕ ℤ)
      (deningerHazewinkelUniversalCoeff (i.val + s)) hvleft
    rcases Finset.mem_union.mp hvinner with hvsign | hvcoeff
    · have hvbase := MvPolynomial.vars_pow
        ((-1 : MvPolynomial ℕ ℤ)) (i.val + (k + 1)) hvsign
      simp at hvbase
    · rw [deningerHazewinkelUniversalCoeff_mem_vars_iff] at hvcoeff
      omega
  · have hvlt := deningerHazewinkelSpecialCofactor_vars_lt (k + 1) s i hvdet
    omega

end
end RHTower

