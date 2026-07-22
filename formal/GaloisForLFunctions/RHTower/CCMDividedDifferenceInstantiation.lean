/-
# CCM divided-difference instantiation

This module verifies that every finite divided-difference matrix with an odd source and even
diagonal has the exact displacement and reflection data consumed by the boundary-channel
completion trichotomy.  Scalar spectral shifts preserve all those identities.
-/
import GaloisForLFunctions.RHTower.CCMBoundaryChannelCompletion

noncomputable section

namespace RHTower

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Finite CCM divided-difference matrix with freely specified diagonal. -/
def ccmDividedDifferenceMatrix
    (clock source diagonal : n → ℝ) : Matrix n n ℝ :=
  fun i j => if i = j then diagonal i
    else (source i - source j) / (clock i - clock j)

/-- Diagonal clock attached to a finite set of clock coordinates. -/
def ccmDiagonalClock (clock : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal clock

/-- Constant boundary vector in the divided-difference displacement law. -/
def ccmConstantBoundary : n → ℝ := fun _ => 1

omit [Fintype n] in
/-- Divided-difference matrices are symmetric, including at coincident clock values. -/
theorem ccmDividedDifferenceMatrix_transpose
    (clock source diagonal : n → ℝ) :
    (ccmDividedDifferenceMatrix clock source diagonal).transpose =
      ccmDividedDifferenceMatrix clock source diagonal := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ccmDividedDifferenceMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp only [Matrix.transpose_apply, ccmDividedDifferenceMatrix, hij, hji, if_false]
    rw [show source j - source i = -(source i - source j) by ring,
      show clock j - clock i = -(clock i - clock j) by ring, div_neg, neg_div]
    simp

omit [Fintype n] in
/-- A real diagonal clock is symmetric. -/
theorem ccmDiagonalClock_transpose (clock : n → ℝ) :
    (ccmDiagonalClock clock).transpose = ccmDiagonalClock clock := by
  simp [ccmDiagonalClock]

/-- **Finite divided-difference displacement law.** -/
theorem ccmDividedDifference_displacement
    (clock source diagonal : n → ℝ) (hclock : Function.Injective clock) :
    ccmDiagonalClock clock * ccmDividedDifferenceMatrix clock source diagonal -
        ccmDividedDifferenceMatrix clock source diagonal * ccmDiagonalClock clock =
      Matrix.vecMulVec source ccmConstantBoundary -
        Matrix.vecMulVec ccmConstantBoundary source := by
  ext i j
  simp only [ccmDiagonalClock, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.sub_apply]
  by_cases hij : i = j
  · subst j
    simp [ccmDividedDifferenceMatrix, Matrix.vecMulVec_apply, ccmConstantBoundary]
    ring
  · have hclockij : clock i - clock j ≠ 0 := sub_ne_zero.mpr (hclock.ne hij)
    simp only [ccmDividedDifferenceMatrix, hij, if_false,
      Matrix.vecMulVec_apply, ccmConstantBoundary]
    field_simp

/-- Permutation matrix acting by a finite reflection. -/
def ccmReflectionMatrix (rho : n ≃ n) : Matrix n n ℝ :=
  fun i j => if j = rho i then 1 else 0

/-- The reflection matrix acts by precomposition with the reflection. -/
theorem ccmReflectionMatrix_mulVec (rho : n ≃ n) (v : n → ℝ) :
    ccmReflectionMatrix rho *ᵥ v = fun i => v (rho i) := by
  funext i
  simp only [ccmReflectionMatrix, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (rho i)]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

omit [Fintype n] [DecidableEq n] in
lemma ccm_eq_reflection_iff
    (rho : n ≃ n) (hrho : ∀ i, rho (rho i) = i) (i j : n) :
    i = rho j ↔ j = rho i := by
  constructor
  · intro h
    have h' := congrArg rho h
    simpa [hrho] using h'.symm
  · intro h
    have h' := congrArg rho h
    simpa [hrho] using h'.symm

omit [Fintype n] in
/-- An involutive reflection matrix is symmetric. -/
theorem ccmReflectionMatrix_transpose
    (rho : n ≃ n) (hrho : ∀ i, rho (rho i) = i) :
    (ccmReflectionMatrix rho).transpose = ccmReflectionMatrix rho := by
  ext i j
  simp only [Matrix.transpose_apply, ccmReflectionMatrix]
  by_cases h : i = rho j
  · have h' : j = rho i := (ccm_eq_reflection_iff rho hrho i j).1 h
    rw [if_pos h, if_pos h']
  · have h' : j ≠ rho i := fun h' => h ((ccm_eq_reflection_iff rho hrho i j).2 h')
    rw [if_neg h, if_neg h']

/-- An involutive reflection matrix squares to the identity. -/
theorem ccmReflectionMatrix_sq
    (rho : n ≃ n) (hrho : ∀ i, rho (rho i) = i) :
    ccmReflectionMatrix rho * ccmReflectionMatrix rho = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (rho i)]
  · by_cases hij : i = j
    · subst j
      simp [ccmReflectionMatrix, hrho]
    · have hji : j ≠ i := Ne.symm hij
      simp [ccmReflectionMatrix, hrho, hij, hji]
  · intro b hb hne
    simp [ccmReflectionMatrix, hne]
  · simp

omit [Fintype n] in
/-- Odd clock/source data and an even diagonal make the divided-difference matrix reflection
invariant entrywise. -/
theorem ccmDividedDifference_reflection_entry
    (rho : n ≃ n) (clock source diagonal : n → ℝ)
    (hclock : ∀ i, clock (rho i) = -clock i)
    (hsource : ∀ i, source (rho i) = -source i)
    (hdiagonal : ∀ i, diagonal (rho i) = diagonal i) :
    ccmDividedDifferenceMatrix clock source diagonal (rho i) (rho j) =
      ccmDividedDifferenceMatrix clock source diagonal i j := by
  by_cases hij : i = j
  · subst j
    simp [ccmDividedDifferenceMatrix, hdiagonal]
  · have hrhoij : rho i ≠ rho j := fun h => hij (rho.injective h)
    simp only [ccmDividedDifferenceMatrix, hij, hrhoij, if_false, hclock, hsource]
    rw [show -source i - -source j = -(source i - source j) by ring,
      show -clock i - -clock j = -(clock i - clock j) by ring, div_neg, neg_div]
    simp

lemma ccm_mul_reflectionMatrix_apply
    (rho : n ≃ n) (hrho : ∀ i, rho (rho i) = i)
    (Q : Matrix n n ℝ) (i j : n) :
    (Q * ccmReflectionMatrix rho) i j = Q i (rho j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (rho j)]
  · simp [ccmReflectionMatrix, hrho]
  · intro b hb hne
    have hne' : j ≠ rho b := by
      intro h
      have : b = rho j := (ccm_eq_reflection_iff rho hrho b j).2 h
      exact hne this
    simp [ccmReflectionMatrix, hne']
  · simp

lemma ccm_reflectionMatrix_mul_apply
    (rho : n ≃ n) (Q : Matrix n n ℝ) (i j : n) :
    (ccmReflectionMatrix rho * Q) i j = Q (rho i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (rho i)]
  · simp [ccmReflectionMatrix]
  · intro b hb hne
    simp [ccmReflectionMatrix, hne]
  · simp

/-- Reflection-invariant divided-difference matrices commute with reflection. -/
theorem ccmReflectionMatrix_commutes_dividedDifference
    (rho : n ≃ n) (hrho : ∀ i, rho (rho i) = i)
    (clock source diagonal : n → ℝ)
    (hclock : ∀ i, clock (rho i) = -clock i)
    (hsource : ∀ i, source (rho i) = -source i)
    (hdiagonal : ∀ i, diagonal (rho i) = diagonal i) :
    ccmDividedDifferenceMatrix clock source diagonal * ccmReflectionMatrix rho =
      ccmReflectionMatrix rho * ccmDividedDifferenceMatrix clock source diagonal := by
  ext i j
  rw [ccm_mul_reflectionMatrix_apply rho hrho,
    ccm_reflectionMatrix_mul_apply rho]
  have h := ccmDividedDifference_reflection_entry rho clock source diagonal
    hclock hsource hdiagonal (i := rho i) (j := j)
  simpa [hrho] using h

/-- The constant boundary is reflection-even. -/
theorem ccmReflectionMatrix_constantBoundary_even
    (rho : n ≃ n) :
    ccmReflectionMatrix rho *ᵥ ccmConstantBoundary = ccmConstantBoundary := by
  rw [ccmReflectionMatrix_mulVec]
  rfl

/-- An odd source vector is a `-1` eigenvector of reflection. -/
theorem ccmReflectionMatrix_source_odd
    (rho : n ≃ n) (source : n → ℝ)
    (hsource : ∀ i, source (rho i) = -source i) :
    ccmReflectionMatrix rho *ᵥ source = -source := by
  rw [ccmReflectionMatrix_mulVec]
  funext i
  exact hsource i

/-- Scalar spectral-floor shift. -/
def ccmScalarShift (Q : Matrix n n ℝ) (mu : ℝ) : Matrix n n ℝ :=
  Q - mu • (1 : Matrix n n ℝ)

omit [Fintype n] in
/-- Scalar shifts preserve symmetry. -/
theorem ccmScalarShift_transpose (Q : Matrix n n ℝ) (mu : ℝ)
    (hQ : Q.transpose = Q) :
    (ccmScalarShift Q mu).transpose = ccmScalarShift Q mu := by
  simp [ccmScalarShift, Matrix.transpose_sub, hQ]

/-- Scalar shifts preserve commutation with every matrix. -/
theorem ccmScalarShift_commutes (Q Gamma : Matrix n n ℝ) (mu : ℝ)
    (hQG : Q * Gamma = Gamma * Q) :
    ccmScalarShift Q mu * Gamma = Gamma * ccmScalarShift Q mu := by
  simp [ccmScalarShift, Matrix.sub_mul, Matrix.mul_sub, hQG]

/-- Scalar shifts preserve a clock displacement identity. -/
theorem ccmScalarShift_displacement (Q D R : Matrix n n ℝ) (mu : ℝ)
    (hdisp : D * Q - Q * D = R) :
    D * ccmScalarShift Q mu - ccmScalarShift Q mu * D = R := by
  simp [ccmScalarShift, Matrix.mul_sub, Matrix.sub_mul]
  simpa using hdisp

/-- **Unconditional finite CCM completion.**  Every injective reflection-graded divided-difference
matrix, after any scalar shift (in particular its spectral-floor shift), admits a rank-one clock
completion which is metric-adjoint and preserves the full radical.  No kernel dimension or kernel
parity premise occurs. -/
theorem ccmDividedDifferenceShift_boundaryCompletion_exists
    (rho : n ≃ n) (hrho : ∀ i, rho (rho i) = i)
    (clock source diagonal : n → ℝ) (mu : ℝ)
    (hclockInjective : Function.Injective clock)
    (hclockOdd : ∀ i, clock (rho i) = -clock i)
    (hsourceOdd : ∀ i, source (rho i) = -source i)
    (hdiagonalEven : ∀ i, diagonal (rho i) = diagonal i) :
    let Q := ccmDividedDifferenceMatrix clock source diagonal
    let T := ccmScalarShift Q mu
    ∃ A : Matrix n n ℝ,
      T * A = A.transpose * T ∧
      ∀ k : n → ℝ, T *ᵥ k = 0 → T *ᵥ (A *ᵥ k) = 0 := by
  dsimp only
  apply ccmBoundaryChannelCompletion_exists
    (T := ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu)
    (D := ccmDiagonalClock clock) (Gamma := ccmReflectionMatrix rho)
    (eta := ccmConstantBoundary) (beta := source)
  · exact ccmScalarShift_transpose _ _
      (ccmDividedDifferenceMatrix_transpose clock source diagonal)
  · exact ccmDiagonalClock_transpose clock
  · exact ccmReflectionMatrix_transpose rho hrho
  · exact ccmScalarShift_commutes _ _ _
      (ccmReflectionMatrix_commutes_dividedDifference rho hrho clock source diagonal
        hclockOdd hsourceOdd hdiagonalEven)
  · exact ccmReflectionMatrix_constantBoundary_even rho
  · exact ccmReflectionMatrix_source_odd rho source hsourceOdd
  · apply ccmScalarShift_displacement
    exact ccmDividedDifference_displacement clock source diagonal hclockInjective

end RHTower
