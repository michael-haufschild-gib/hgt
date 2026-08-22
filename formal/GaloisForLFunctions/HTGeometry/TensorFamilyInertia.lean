import GaloisForLFunctions.HTGeometry.HaynsworthInertia

/-!
# Iterated Kronecker products of matrix families and their inertia

For a finite family of rectangular matrices `M i : Matrix (α i) (β i) ℂ` the *tensor family*

`tensorFamily M x y = ∏ i, M i (x i) (y i)`

is the iterated Kronecker product on the product index types.  It is multiplicative, commutes with
the conjugate transpose, sends diagonal families to diagonal matrices, and therefore has inertia
determined by the products of the local eigenvalues.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

section Basic

variable {ι : Type*} [Fintype ι] {α β γ : ι → Type*}
  [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]

/-- The iterated Kronecker product of a family of matrices. -/
def tensorFamily (M : ∀ i, Matrix (α i) (β i) ℂ) : Matrix (∀ i, α i) (∀ i, β i) ℂ :=
  Matrix.of fun x y => ∏ i, M i (x i) (y i)

omit [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] in
@[simp] theorem tensorFamily_apply (M : ∀ i, Matrix (α i) (β i) ℂ) (x : ∀ i, α i) (y : ∀ i, β i) :
    tensorFamily M x y = ∏ i, M i (x i) (y i) := rfl

omit [∀ i, Fintype (α i)] [∀ i, Fintype (γ i)] in
theorem tensorFamily_mul [DecidableEq ι] (M : ∀ i, Matrix (α i) (β i) ℂ)
    (N : ∀ i, Matrix (β i) (γ i) ℂ) :
    tensorFamily M * tensorFamily N = tensorFamily fun i => M i * N i := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  simp only [tensorFamily_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (β i)))
    (fun i b => M i (x i) b * N i b (y i)), Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun z _ => (Finset.prod_mul_distrib).symm

omit [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] in
theorem tensorFamily_conjTranspose (M : ∀ i, Matrix (α i) (β i) ℂ) :
    (tensorFamily M)ᴴ = tensorFamily fun i => (M i)ᴴ := by
  ext x y
  simp [Matrix.conjTranspose_apply]

omit [∀ i, Fintype (α i)] in
theorem tensorFamily_one [DecidableEq ι] [∀ i, DecidableEq (α i)] :
    tensorFamily (fun i => (1 : Matrix (α i) (α i) ℂ)) = 1 := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [Matrix.one_apply_eq]
  · have : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    obtain ⟨i, hi⟩ := this
    rw [Matrix.one_apply_ne hxy]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [Matrix.one_apply_ne hi]

omit [∀ i, Fintype (α i)] in
theorem tensorFamily_diagonal [∀ i, DecidableEq (α i)] [DecidableEq ι] (μ : ∀ i, α i → ℂ) :
    tensorFamily (fun i => diagonal (μ i)) = diagonal fun x => ∏ i, μ i (x i) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [Matrix.diagonal_apply_eq]
  · have : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    obtain ⟨i, hi⟩ := this
    rw [Matrix.diagonal_apply_ne _ hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

theorem isUnit_tensorFamily [DecidableEq ι] [∀ i, DecidableEq (α i)]
    {M : ∀ i, Matrix (α i) (α i) ℂ} (h : ∀ i, IsUnit (M i)) : IsUnit (tensorFamily M) := by
  classical
  choose N hMN using fun i => (h i).exists_right_inv
  have hleft : ∀ i, N i * M i = 1 := fun i => mul_eq_one_comm.mp (hMN i)
  refine ⟨⟨tensorFamily M, tensorFamily N, ?_, ?_⟩, rfl⟩
  · rw [tensorFamily_mul,
      show (fun i => M i * N i) = (fun i => (1 : Matrix (α i) (α i) ℂ)) from funext hMN,
      tensorFamily_one]
  · rw [tensorFamily_mul,
      show (fun i => N i * M i) = (fun i => (1 : Matrix (α i) (α i) ℂ)) from funext hleft,
      tensorFamily_one]

omit [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)] in
theorem isHermitian_tensorFamily {M : ∀ i, Matrix (α i) (α i) ℂ} (h : ∀ i, (M i).IsHermitian) :
    (tensorFamily M).IsHermitian := by
  rw [Matrix.IsHermitian, tensorFamily_conjTranspose]
  congr 1
  exact funext fun i => (h i).eq

variable [DecidableEq ι] [∀ i, DecidableEq (α i)]

/-- **Inertia of an iterated Kronecker product.**  The positive index counts the product index
points at which the product of the local eigenvalues is positive. -/
theorem posIndex_tensorFamily {M : ∀ i, Matrix (α i) (α i) ℂ} (h : ∀ i, (M i).IsHermitian) :
    hermPosIndex (tensorFamily M)
      = ({x : ∀ i, α i | 0 < ∏ i, (h i).eigenvalues (x i)} : Finset (∀ i, α i)).card := by
  classical
  choose S hS hcongr using fun i => exists_congr_diagonal (h i)
  have hdec : tensorFamily M
      = (tensorFamily S)ᴴ *
        (diagonal fun x : ∀ i, α i => ((∏ i, (h i).eigenvalues (x i) : ℝ) : ℂ)) *
        tensorFamily S := by
    have hdiag : (diagonal fun x : ∀ i, α i => ((∏ i, (h i).eigenvalues (x i) : ℝ) : ℂ))
        = tensorFamily fun i => diagonal (fun a => (((h i).eigenvalues a : ℝ) : ℂ)) := by
      rw [tensorFamily_diagonal]
      congr 1
      funext x
      push_cast
      rfl
    rw [hdiag, tensorFamily_conjTranspose, tensorFamily_mul, tensorFamily_mul]
    congr 1
    funext i
    exact (hcongr i).symm
  rw [hdec, posIndex_conjugate _ (isUnit_tensorFamily hS), posIndex_diagonal]

/-- **Negative index of an iterated Kronecker product.** -/
theorem negIndex_tensorFamily {M : ∀ i, Matrix (α i) (α i) ℂ} (h : ∀ i, (M i).IsHermitian) :
    hermNegIndex (tensorFamily M)
      = ({x : ∀ i, α i | ∏ i, (h i).eigenvalues (x i) < 0} : Finset (∀ i, α i)).card := by
  classical
  choose S hS hcongr using fun i => exists_congr_diagonal (h i)
  have hdec : tensorFamily M
      = (tensorFamily S)ᴴ *
        (diagonal fun x : ∀ i, α i => ((∏ i, (h i).eigenvalues (x i) : ℝ) : ℂ)) *
        tensorFamily S := by
    have hdiag : (diagonal fun x : ∀ i, α i => ((∏ i, (h i).eigenvalues (x i) : ℝ) : ℂ))
        = tensorFamily fun i => diagonal (fun a => (((h i).eigenvalues a : ℝ) : ℂ)) := by
      rw [tensorFamily_diagonal]
      congr 1
      funext x
      push_cast
      rfl
    rw [hdiag, tensorFamily_conjTranspose, tensorFamily_mul, tensorFamily_mul]
    congr 1
    funext i
    exact (hcongr i).symm
  rw [hdec, negIndex_conjugate _ (isUnit_tensorFamily hS), negIndex_diagonal]

end Basic

end GaloisForLFunctions.HTGeometry
