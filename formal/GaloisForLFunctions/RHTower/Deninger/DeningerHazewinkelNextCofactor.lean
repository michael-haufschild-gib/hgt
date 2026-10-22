import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelSpecialPivot

/-!
# The second Hazewinkel cofactor

The cofactor immediately below `D_n` is itself the next special minor at stage `n-1`.  This
identification makes its nondivisibility by `D_n` a consequence of two symbolic pivot degrees.
-/

namespace RHTower

noncomputable section

/-- Leading Hankel matrix with its last row shifted once.  Index `k` represents stage `k+1`. -/
def deningerHazewinkelNextCofactorMatrix (k : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) (MvPolynomial ℕ ℤ) :=
  fun i j => if i = Fin.last k then
    deningerHazewinkelUniversalCoeff (k + 1 + j.val)
  else deningerHazewinkelUniversalCoeff (i.val + j.val)

/-- The shifted-last-row cofactor `E_(k+1)`. -/
def deningerHazewinkelNextCofactor (k : ℕ) : MvPolynomial ℕ ℤ :=
  (deningerHazewinkelNextCofactorMatrix k).det

/-- `D_(k+1)` is the boundary special minor at stage `k`. -/
theorem deningerHazewinkelLeadingDeterminant_succ_eq_special (k : ℕ) :
    deningerHazewinkelLeadingDeterminant (k + 1) =
      deningerHazewinkelSpecialMinor k k := by
  apply congrArg Matrix.det
  ext i j
  by_cases hj : j = Fin.last k
  · subst j
    simp [deningerHazewinkelSpecialMatrix]
  · simp [deningerHazewinkelSpecialMatrix, hj]

/-- By transposition, `E_(k+1)` is the next special minor `m_(k+1)` at stage `k`. -/
theorem deningerHazewinkelNextCofactor_eq_special (k : ℕ) :
    deningerHazewinkelNextCofactor k =
      deningerHazewinkelSpecialMinor k (k + 1) := by
  rw [deningerHazewinkelNextCofactor, deningerHazewinkelSpecialMinor,
    ← Matrix.det_transpose]
  apply congrArg Matrix.det
  ext i j
  by_cases hj : j = Fin.last k
  · subst j
    simp only [Matrix.transpose_apply, deningerHazewinkelNextCofactorMatrix,
      deningerHazewinkelSpecialMatrix, if_pos]
    rw [Nat.add_comm (k + 1) i.val]
  · simp only [Matrix.transpose_apply, deningerHazewinkelNextCofactorMatrix,
      deningerHazewinkelSpecialMatrix, hj, if_false]
    rw [Nat.add_comm j.val i.val]

theorem deningerHazewinkelLeading_succ_not_dvd_previous
    {k : ℕ} (hk : 1 ≤ k) :
    ¬ deningerHazewinkelLeadingDeterminant (k + 1) ∣
      deningerHazewinkelLeadingDeterminant k := by
  intro hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hDprev0 : MvPolynomial.degreeOf (k + k - 1)
      (deningerHazewinkelLeadingDeterminant k) = 0 :=
    deningerHazewinkelLeadingDeterminant_degreeOf_pivot hk le_rfl
  have hDdegree : MvPolynomial.degreeOf (k + k - 1)
      (deningerHazewinkelLeadingDeterminant (k + 1)) = 1 := by
    rw [deningerHazewinkelLeadingDeterminant_succ_eq_special]
    exact deningerHazewinkelSpecialMinor_degreeOf_pivot hk le_rfl
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hq
    exact deningerHazewinkelLeadingDeterminant_ne_zero k hq
  have hdegree := MvPolynomial.degreeOf_mul_eq
    (deningerHazewinkelLeadingDeterminant_ne_zero (k + 1)) hq0
    (n := k + k - 1)
  have heqdegree := congrArg (MvPolynomial.degreeOf (k + k - 1)) hq
  rw [hDprev0, hdegree, hDdegree] at heqdegree
  omega

/-- The second cofactor is nonzero on the irreducible divisor `D_(k+1)=0`. -/
theorem deningerHazewinkelLeading_succ_not_dvd_nextCofactor
    {k : ℕ} (hk : 1 ≤ k) :
    ¬ deningerHazewinkelLeadingDeterminant (k + 1) ∣
      deningerHazewinkelNextCofactor k := by
  intro hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hDnot : k + (k + 1) - 1 ∉
      (deningerHazewinkelLeadingDeterminant (k + 1)).vars := by
    rw [deningerHazewinkelLeadingDeterminant_succ_eq_special]
    intro hmem
    have hle := deningerHazewinkelSpecialMinor_vars_le_pivot hk le_rfl hmem
    omega
  have hpderivD := MvPolynomial.pderiv_eq_zero_of_notMem_vars hDnot
  have hEderiv : MvPolynomial.pderiv (k + (k + 1) - 1)
      (deningerHazewinkelNextCofactor k) =
      deningerHazewinkelLeadingDeterminant k := by
    rw [deningerHazewinkelNextCofactor_eq_special]
    exact (GaloisForLFunctions.initialAt_eq_pderiv_of_degreeOf_eq_one
      (deningerHazewinkelSpecialMinor_degreeOf_pivot hk
        (by omega : k ≤ k + 1))).symm.trans
      (deningerHazewinkelSpecialMinor_initialAt_pivot hk (by omega : k ≤ k + 1))
  have hdivprev : deningerHazewinkelLeadingDeterminant (k + 1) ∣
      deningerHazewinkelLeadingDeterminant k := by
    refine ⟨MvPolynomial.pderiv (k + (k + 1) - 1) q, ?_⟩
    rw [← hEderiv, hq, MvPolynomial.pderiv_mul, hpderivD]
    simp
  exact deningerHazewinkelLeading_succ_not_dvd_previous hk hdivprev

end

end RHTower
