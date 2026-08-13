import GaloisForLFunctions.RHTower.DeningerHazewinkelLeadingPrime
import GaloisForLFunctions.HTGeometry.DifferentialCharacteristicPseudoReduction
import GaloisForLFunctions.HTGeometry.PseudoDivisionCommRing

/-!
# Triangular pivots for Hazewinkel's special Hankel minors

Expansion down the last column writes every special minor as the leading Hankel determinant times
one new coefficient variable plus a polynomial in strictly earlier variables.  This is the
division-free pivot used in Hazewinkel's integral saturation argument.
-/

namespace RHTower

noncomputable section

open scoped BigOperators

/-- Matrix with leading columns `0,…,n-1` and final column `s`. -/
def deningerHazewinkelSpecialMatrix (n s : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial ℕ ℤ) :=
  fun i j => if j = Fin.last n then
    deningerHazewinkelUniversalCoeff (i.val + s)
  else deningerHazewinkelUniversalCoeff (i.val + j.val)

/-- Hazewinkel's special minor `m_s`. -/
def deningerHazewinkelSpecialMinor (n s : ℕ) : MvPolynomial ℕ ℤ :=
  (deningerHazewinkelSpecialMatrix n s).det

theorem deningerHazewinkelSpecialMinor_eq_updateCol (n s : ℕ) :
    deningerHazewinkelSpecialMinor n s =
      ((deningerHazewinkelBorderedLeading n).updateCol (Fin.last n)
        (fun i => deningerHazewinkelUniversalCoeff (i.val + s))).det := by
  apply congrArg Matrix.det
  ext i j
  by_cases hj : j = Fin.last n
  · subst j
    simp [deningerHazewinkelSpecialMatrix]
  · rw [Matrix.updateCol_ne hj, deningerHazewinkelBorderedLeading_apply]
    have hjlt : j.val < n := by
      have hjle : j.val ≤ n := Nat.le_of_lt_succ j.isLt
      exact lt_of_le_of_ne hjle (fun h => hj (Fin.ext h))
    simp [deningerHazewinkelSpecialMatrix, hj, hjlt]

theorem deningerHazewinkelSpecialMinor_mem_specialIdeal (n s : ℕ) :
    deningerHazewinkelSpecialMinor n s ∈ deningerHazewinkelSpecialMinorIdeal n := by
  rw [deningerHazewinkelSpecialMinor_eq_updateCol]
  apply Ideal.subset_span
  exact ⟨s, rfl⟩

/-- Variables in a determinant occur in matrix entries. -/
theorem mvPolynomial_vars_det_subset_entries
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial ℕ R)) :
    M.det.vars ⊆ Finset.univ.biUnion fun i =>
      Finset.univ.biUnion fun j => (M i j).vars := by
  classical
  rw [Matrix.det_apply]
  intro v hv
  have hvsum := MvPolynomial.vars_sum_subset Finset.univ
    (fun σ : Equiv.Perm ι => (Equiv.Perm.sign σ : ℤ) • ∏ i, M (σ i) i) hv
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hvsum ⊢
  obtain ⟨σ, hvσ⟩ := hvsum
  have hvprod : v ∈ (∏ i, M (σ i) i).vars := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
    · simpa [hσ] using hvσ
    · simpa [hσ] using hvσ
  have hventry := MvPolynomial.vars_prod
    (s := (Finset.univ : Finset ι)) (fun i => M (σ i) i) hvprod
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hventry
  obtain ⟨j, hvj⟩ := hventry
  exact ⟨σ j, j, hvj⟩

/-- All non-pivot terms in last-column Laplace expansion. -/
def deningerHazewinkelSpecialLaplaceRemainder (n s : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ i ∈ (Finset.univ.erase (Fin.last n)),
    (-1) ^ (i.val + n) *
      deningerHazewinkelUniversalCoeff (i.val + s) *
      ((deningerHazewinkelSpecialMatrix n s).submatrix
        i.succAbove (Fin.last n).succAbove).det

/-- Exact last-column pivot identity `m_s = D_n a_(n+s) + lower`. -/
theorem deningerHazewinkelSpecialMinor_pivot_laplace (n s : ℕ) :
    deningerHazewinkelSpecialMinor n s =
      deningerHazewinkelLeadingDeterminant n *
        deningerHazewinkelUniversalCoeff (n + s) +
      deningerHazewinkelSpecialLaplaceRemainder n s := by
  rw [deningerHazewinkelSpecialMinor, Matrix.det_succ_column _ (Fin.last n)]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin (n + 1)))
    (fun i => (-1) ^ (i.val + (Fin.last n).val) *
      deningerHazewinkelSpecialMatrix n s i (Fin.last n) *
      ((deningerHazewinkelSpecialMatrix n s).submatrix
        i.succAbove (Fin.last n).succAbove).det)
    (Finset.mem_univ (Fin.last n))]
  have hcofactor :
      ((deningerHazewinkelSpecialMatrix n s).submatrix
        (Fin.last n).succAbove (Fin.last n).succAbove).det =
      deningerHazewinkelLeadingDeterminant n := by
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [Fin.succAbove_last_apply, Fin.succAbove_last_apply]
    simp [deningerHazewinkelSpecialMatrix]
  rw [hcofactor]
  simp only [Fin.val_last, deningerHazewinkelSpecialMatrix, if_pos,
    show (-1 : MvPolynomial ℕ ℤ) ^ (n + n) = 1 by rw [← two_mul]; simp,
    one_mul]
  rw [mul_comm]
  rfl

theorem deningerHazewinkelUniversalCoeff_mem_vars_iff {r v : ℕ} :
    v ∈ (deningerHazewinkelUniversalCoeff r).vars ↔ r = v + 1 := by
  cases r with
  | zero => simp [deningerHazewinkelUniversalCoeff]
  | succ r => simp [deningerHazewinkelUniversalCoeff, eq_comm]

theorem deningerHazewinkelSpecialCofactor_vars_lt
    (n s : ℕ) (i : Fin (n + 1)) {v : ℕ}
    (hv : v ∈ ((deningerHazewinkelSpecialMatrix n s).submatrix
      i.succAbove (Fin.last n).succAbove).det.vars) :
    v < 2 * n - 1 := by
  have hentries := mvPolynomial_vars_det_subset_entries
    ((deningerHazewinkelSpecialMatrix n s).submatrix
      i.succAbove (Fin.last n).succAbove) hv
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hentries
  obtain ⟨r, c, hentry⟩ := hentries
  simp only [Matrix.submatrix_apply] at hentry
  rw [Fin.succAbove_last_apply] at hentry
  have hc : c.castSucc ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at this
    exact (Nat.ne_of_lt c.isLt) this
  simp only [deningerHazewinkelSpecialMatrix, hc, if_false] at hentry
  rw [deningerHazewinkelUniversalCoeff_mem_vars_iff] at hentry
  simp only [Fin.val_castSucc] at hentry
  have hr : (i.succAbove r).val ≤ n := Nat.le_of_lt_succ (i.succAbove r).isLt
  have hcval : c.val < n := c.isLt
  omega

/-- Every variable in the Laplace remainder precedes the pivot variable. -/
theorem deningerHazewinkelSpecialLaplaceRemainder_vars_lt
    {n s v : ℕ} (hn : 1 ≤ n) (hns : n ≤ s)
    (hv : v ∈ (deningerHazewinkelSpecialLaplaceRemainder n s).vars) :
    v < n + s - 1 := by
  rw [deningerHazewinkelSpecialLaplaceRemainder] at hv
  have hvsum := MvPolynomial.vars_sum_subset
    (Finset.univ.erase (Fin.last n))
    (fun i : Fin (n + 1) =>
      (-1) ^ (i.val + n) * deningerHazewinkelUniversalCoeff (i.val + s) *
        ((deningerHazewinkelSpecialMatrix n s).submatrix
          i.succAbove (Fin.last n).succAbove).det) hv
  simp only [Finset.mem_biUnion] at hvsum
  obtain ⟨i, hi, hvterm⟩ := hvsum
  have hvouter := MvPolynomial.vars_mul
    ((-1) ^ (i.val + n) * deningerHazewinkelUniversalCoeff (i.val + s))
    (((deningerHazewinkelSpecialMatrix n s).submatrix
      i.succAbove (Fin.last n).succAbove).det) hvterm
  rcases Finset.mem_union.mp hvouter with hvleft | hvdet
  · have hvinner := MvPolynomial.vars_mul
      ((-1) ^ (i.val + n) : MvPolynomial ℕ ℤ)
      (deningerHazewinkelUniversalCoeff (i.val + s)) hvleft
    rcases Finset.mem_union.mp hvinner with hvsign | hvcoeff
    · have hvbase := MvPolynomial.vars_pow
        ((-1 : MvPolynomial ℕ ℤ)) (i.val + n) hvsign
      simp at hvbase
    · rw [deningerHazewinkelUniversalCoeff_mem_vars_iff] at hvcoeff
      have hilt : i.val < n := by
        have hine : i ≠ Fin.last n := Finset.ne_of_mem_erase hi
        have hile : i.val ≤ n := Nat.le_of_lt_succ i.isLt
        exact lt_of_le_of_ne hile (fun h => hine (Fin.ext h))
      omega
  · have hvlt := deningerHazewinkelSpecialCofactor_vars_lt n s i hvdet
    omega

/-- Variables of `D_n` precede every special pivot at index `s ≥ n`. -/
theorem deningerHazewinkelLeadingDeterminant_vars_lt_pivot
    {n s v : ℕ} (_hn : 1 ≤ n) (hns : n ≤ s)
    (hv : v ∈ (deningerHazewinkelLeadingDeterminant n).vars) :
    v < n + s - 1 := by
  have hentries := mvPolynomial_vars_det_subset_entries
    (fun i j : Fin n => deningerHazewinkelUniversalCoeff (i.val + j.val)) hv
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hentries
  obtain ⟨i, j, hentry⟩ := hentries
  rw [deningerHazewinkelUniversalCoeff_mem_vars_iff] at hentry
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem deningerHazewinkelUniversalCoeff_pivot
    {n s : ℕ} (hn : 1 ≤ n) :
    deningerHazewinkelUniversalCoeff (n + s) =
      MvPolynomial.X (n + s - 1) := by
  rw [show n + s = (n + s - 1) + 1 by omega]
  rfl

theorem deningerHazewinkelLeadingDeterminant_ne_zero (n : ℕ) :
    deningerHazewinkelLeadingDeterminant n ≠ 0 := by
  rcases deningerHazewinkelLeadingDeterminant_prime_or_isUnit n with hp | hu
  · exact hp.ne_zero
  · exact hu.ne_zero

theorem deningerHazewinkelLeadingDeterminant_degreeOf_pivot
    {n s : ℕ} (hn : 1 ≤ n) (hns : n ≤ s) :
    MvPolynomial.degreeOf (n + s - 1)
      (deningerHazewinkelLeadingDeterminant n) = 0 := by
  by_contra hne
  have hmem := MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hne
  have hlt := deningerHazewinkelLeadingDeterminant_vars_lt_pivot hn hns hmem
  omega

theorem deningerHazewinkelSpecialLaplaceRemainder_degreeOf_pivot
    {n s : ℕ} (hn : 1 ≤ n) (hns : n ≤ s) :
    MvPolynomial.degreeOf (n + s - 1)
      (deningerHazewinkelSpecialLaplaceRemainder n s) = 0 := by
  by_contra hne
  have hmem := MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hne
  have hlt := deningerHazewinkelSpecialLaplaceRemainder_vars_lt hn hns hmem
  omega

/-- The special minor is linear in its new pivot variable. -/
theorem deningerHazewinkelSpecialMinor_degreeOf_pivot
    {n s : ℕ} (hn : 1 ≤ n) (hns : n ≤ s) :
    MvPolynomial.degreeOf (n + s - 1)
      (deningerHazewinkelSpecialMinor n s) = 1 := by
  rw [deningerHazewinkelSpecialMinor_pivot_laplace,
    deningerHazewinkelUniversalCoeff_pivot hn]
  have hD0 := deningerHazewinkelLeadingDeterminant_degreeOf_pivot hn hns
  have hR0 := deningerHazewinkelSpecialLaplaceRemainder_degreeOf_pivot hn hns
  have hDX : MvPolynomial.degreeOf (n + s - 1)
      (deningerHazewinkelLeadingDeterminant n * MvPolynomial.X (n + s - 1)) = 1 := by
    rw [MvPolynomial.degreeOf_mul_eq
      (deningerHazewinkelLeadingDeterminant_ne_zero n) (MvPolynomial.X_ne_zero _),
      hD0]
    simp
  rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (by omega :
    MvPolynomial.degreeOf (n + s - 1)
      (deningerHazewinkelSpecialLaplaceRemainder n s) <
    MvPolynomial.degreeOf (n + s - 1)
      (deningerHazewinkelLeadingDeterminant n * MvPolynomial.X (n + s - 1)))]
  exact hDX

/-- The initial of the special minor at its pivot is exactly `D_n`. -/
theorem deningerHazewinkelSpecialMinor_initialAt_pivot
    {n s : ℕ} (hn : 1 ≤ n) (hns : n ≤ s) :
    GaloisForLFunctions.mvPolynomialInitialAt (n + s - 1)
      (deningerHazewinkelSpecialMinor n s) =
      deningerHazewinkelLeadingDeterminant n := by
  rw [GaloisForLFunctions.initialAt_eq_pderiv_of_degreeOf_eq_one
    (deningerHazewinkelSpecialMinor_degreeOf_pivot hn hns)]
  rw [deningerHazewinkelSpecialMinor_pivot_laplace,
    deningerHazewinkelUniversalCoeff_pivot hn, map_add,
    MvPolynomial.pderiv_mul]
  have hDnot : n + s - 1 ∉ (deningerHazewinkelLeadingDeterminant n).vars := by
    intro hmem
    have := deningerHazewinkelLeadingDeterminant_vars_lt_pivot hn hns hmem
    omega
  have hRnot : n + s - 1 ∉
      (deningerHazewinkelSpecialLaplaceRemainder n s).vars := by
    intro hmem
    have := deningerHazewinkelSpecialLaplaceRemainder_vars_lt hn hns hmem
    omega
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hDnot,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hRnot]
  simp

/-- No variable after the pivot occurs in a special minor. -/
theorem deningerHazewinkelSpecialMinor_vars_le_pivot
    {n s v : ℕ} (hn : 1 ≤ n) (hns : n ≤ s)
    (hv : v ∈ (deningerHazewinkelSpecialMinor n s).vars) :
    v ≤ n + s - 1 := by
  rw [deningerHazewinkelSpecialMinor_pivot_laplace,
    deningerHazewinkelUniversalCoeff_pivot hn] at hv
  have hvadd := MvPolynomial.vars_add_subset
    (deningerHazewinkelLeadingDeterminant n * MvPolynomial.X (n + s - 1))
    (deningerHazewinkelSpecialLaplaceRemainder n s) hv
  rcases Finset.mem_union.mp hvadd with hvmul | hvrem
  · have hvparts := MvPolynomial.vars_mul
      (deningerHazewinkelLeadingDeterminant n) (MvPolynomial.X (n + s - 1)) hvmul
    rcases Finset.mem_union.mp hvparts with hvD | hvX
    · exact (deningerHazewinkelLeadingDeterminant_vars_lt_pivot hn hns hvD).le
    · exact (by simpa using hvX : v = n + s - 1).le
  · exact (deningerHazewinkelSpecialLaplaceRemainder_vars_lt hn hns hvrem).le

end

end RHTower
