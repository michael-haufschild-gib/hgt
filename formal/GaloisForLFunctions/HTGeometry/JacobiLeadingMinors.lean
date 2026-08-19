import GaloisForLFunctions.HTGeometry.SiegelSizeReduction

/-!
# Leading minors of a Jacobi decomposition

The leading `k × k` block of `Uᵀ D U` is again of that shape, because an upper triangular `U` has
no entries below the diagonal to couple the block to the rest.  Its determinant is therefore the
product of the first `k` diagonal entries, which identifies the Jacobi diagonal intrinsically:

`dₖ = det Aₖ₊₁ / det Aₖ`.

In particular the diagonal of a Jacobi decomposition is unique, and the potential `∏ det Aₖ` used to
run reduction theory is a function of the form alone.

* `leadingBlock` : the leading `k × k` block.
* `det_leadingBlock_form` : **its determinant is the product of the first `k` diagonal entries.**
* `JacobiData.d_unique` : **the Jacobi diagonal is determined by the form.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The leading `k × k` block. -/
def leadingBlock {k n : ℕ} (h : k ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)

@[simp]
theorem leadingBlock_apply {k n : ℕ} (h : k ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin k) :
    leadingBlock h A i j = A (Fin.castLE h i) (Fin.castLE h j) := rfl

theorem leadingBlock_upper {k n : ℕ} (h : k ≤ n) {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : ∀ i j : Fin n, j < i → U i j = 0) (i j : Fin k) (hji : j < i) :
    leadingBlock h U i j = 0 :=
  hU _ _ (by simpa using hji)

theorem leadingBlock_unit {k n : ℕ} (h : k ≤ n) {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : ∀ i, U i i = 1) (i : Fin k) : leadingBlock h U i i = 1 := hU _

/-- **The leading block of `Uᵀ D U` is `Uₖᵀ Dₖ Uₖ`.** -/
theorem leadingBlock_congr {k n : ℕ} (h : k ≤ n) {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : ∀ i j : Fin n, j < i → U i j = 0) (d : Fin n → ℝ) :
    leadingBlock h (Uᵀ * Matrix.diagonal d * U)
      = (leadingBlock h U)ᵀ * Matrix.diagonal (fun m : Fin k => d (Fin.castLE h m))
        * leadingBlock h U := by
  classical
  ext i j
  have hmul : ∀ a b : Fin n, (Uᵀ * Matrix.diagonal d) a b = U b a * d b := by
    intro a b
    rw [Matrix.mul_apply,
      Finset.sum_eq_single b (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
        (fun hcon => absurd (Finset.mem_univ b) hcon),
      Matrix.transpose_apply, Matrix.diagonal_apply_eq]
  have hmul' : ∀ a b : Fin k,
      ((leadingBlock h U)ᵀ * Matrix.diagonal (fun m : Fin k => d (Fin.castLE h m))) a b
        = U (Fin.castLE h b) (Fin.castLE h a) * d (Fin.castLE h b) := by
    intro a b
    rw [Matrix.mul_apply,
      Finset.sum_eq_single b (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
        (fun hcon => absurd (Finset.mem_univ b) hcon),
      Matrix.transpose_apply, Matrix.diagonal_apply_eq]
    rfl
  have hLHS : leadingBlock h (Uᵀ * Matrix.diagonal d * U) i j
      = ∑ m : Fin n, U m (Fin.castLE h i) * d m * U m (Fin.castLE h j) := by
    show (Uᵀ * Matrix.diagonal d * U) (Fin.castLE h i) (Fin.castLE h j) = _
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [hmul]
  have hRHS : ((leadingBlock h U)ᵀ * Matrix.diagonal (fun m : Fin k => d (Fin.castLE h m))
        * leadingBlock h U) i j
      = ∑ m : Fin k, U (Fin.castLE h m) (Fin.castLE h i) * d (Fin.castLE h m)
          * U (Fin.castLE h m) (Fin.castLE h j) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [hmul']; rfl
  rw [hLHS, hRHS]
  have hinj : Set.InjOn (Fin.castLE h) ((Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
    intro a _ b _ hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)
  rw [← Finset.sum_image (f := fun m : Fin n => U m (Fin.castLE h i) * d m * U m (Fin.castLE h j))
    hinj]
  refine (Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_).symm
  have hmk : k ≤ (m : ℕ) := by
    by_contra hcon
    exact hm (Finset.mem_image.2 ⟨⟨(m : ℕ), by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hlt : Fin.castLE h i < m := by
    refine Fin.lt_def.2 ?_
    have hi := i.isLt
    simp only [Fin.val_castLE]
    omega
  rw [hU m (Fin.castLE h i) hlt, zero_mul, zero_mul]

/-- **The determinant of the leading block is the product of the first `k` diagonal entries.** -/
theorem det_leadingBlock_form {k : ℕ} (h : k ≤ n) (J : JacobiData n) :
    (leadingBlock h J.form).det = ∏ m : Fin k, J.d (Fin.castLE h m) := by
  have hform : J.form = J.Uᵀ * Matrix.diagonal J.d * J.U := rfl
  rw [hform, leadingBlock_congr h J.upper J.d, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal]
  have hdet : (leadingBlock h J.U).det = 1 :=
    det_eq_one_of_unipotent (leadingBlock_upper h J.upper) (leadingBlock_unit h J.unit)
  rw [hdet, one_mul, mul_one]

/-- **The Jacobi diagonal is determined by the form.** -/
theorem JacobiData.d_unique {J J' : JacobiData n} (hform : J.form = J'.form) : J.d = J'.d := by
  have hprod : ∀ k : ℕ, ∀ h : k ≤ n,
      (∏ m : Fin k, J.d (Fin.castLE h m)) = ∏ m : Fin k, J'.d (Fin.castLE h m) := by
    intro k h
    rw [← det_leadingBlock_form h J, ← det_leadingBlock_form h J', hform]
  funext i
  have hi1 : (i : ℕ) + 1 ≤ n := i.isLt
  have hi0 : (i : ℕ) ≤ n := le_of_lt i.isLt
  have hstep : ∀ (k : ℕ) (hk : k + 1 ≤ n),
      (∏ m : Fin (k + 1), J.d (Fin.castLE hk m))
        = (∏ m : Fin k, J.d (Fin.castLE (le_of_lt hk) m)) * J.d ⟨k, hk⟩ := by
    intro k hk
    rw [Fin.prod_univ_castSucc]
    congr 1
  have hstep' : ∀ (k : ℕ) (hk : k + 1 ≤ n),
      (∏ m : Fin (k + 1), J'.d (Fin.castLE hk m))
        = (∏ m : Fin k, J'.d (Fin.castLE (le_of_lt hk) m)) * J'.d ⟨k, hk⟩ := by
    intro k hk
    rw [Fin.prod_univ_castSucc]
    congr 1
  have hpos : ∀ (k : ℕ) (hk : k ≤ n), (0 : ℝ) < ∏ m : Fin k, J.d (Fin.castLE hk m) :=
    fun k hk => Finset.prod_pos fun m _ => J.pos _
  have key := hprod ((i : ℕ) + 1) hi1
  rw [hstep (i : ℕ) hi1, hstep' (i : ℕ) hi1, hprod (i : ℕ) hi0] at key
  have hne : (∏ m : Fin (i : ℕ), J'.d (Fin.castLE hi0 m)) ≠ 0 := by
    have := hpos (i : ℕ) hi0
    rw [hprod (i : ℕ) hi0] at this
    exact ne_of_gt this
  have := mul_left_cancel₀ hne key
  have hii : (⟨(i : ℕ), hi1⟩ : Fin n) = i := Fin.ext rfl
  rwa [hii] at this

end GaloisForLFunctions.HTGeometry
