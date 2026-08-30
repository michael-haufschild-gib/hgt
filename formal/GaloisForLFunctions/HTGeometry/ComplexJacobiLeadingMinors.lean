import GaloisForLFunctions.HTGeometry.ComplexSiegelIsometryVanishing

/-!
# Leading minors of complex Jacobi forms

The leading block of `Uᴴ diag(d) U` is the same construction on the leading block of the complex
upper-unipotent factor.  Its determinant is therefore the product of the corresponding real Jacobi
weights.  Leading truncations inherit the complete complex Siegel structure.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- Leading square block of a complex matrix. -/
def complexLeadingBlock {k n : ℕ} (h : k ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)

@[simp] theorem complexLeadingBlock_apply {k n : ℕ} (h : k ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) :
    complexLeadingBlock h A i j = A (Fin.castLE h i) (Fin.castLE h j) := rfl

theorem complexLeadingBlock_upper {k n : ℕ} (h : k ≤ n)
    {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : ∀ i j : Fin n, j < i → U i j = 0) (i j : Fin k) (hji : j < i) :
    complexLeadingBlock h U i j = 0 := hU _ _ (by simpa using hji)

theorem complexLeadingBlock_unit {k n : ℕ} (h : k ≤ n)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : ∀ i, U i i = 1) (i : Fin k) :
    complexLeadingBlock h U i i = 1 := hU _

/-- Leading blocks commute with a complex upper-triangular Jacobi congruence. -/
theorem complexLeadingBlock_congr {k n : ℕ} (h : k ≤ n)
    {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : ∀ i j : Fin n, j < i → U i j = 0) (d : Fin n → ℝ) :
    complexLeadingBlock h
        (Matrix.conjTranspose U * Matrix.diagonal (fun i => (d i : ℂ)) * U) =
      Matrix.conjTranspose (complexLeadingBlock h U) *
        Matrix.diagonal (fun m : Fin k => (d (Fin.castLE h m) : ℂ)) *
          complexLeadingBlock h U := by
  classical
  ext i j
  have hmul : ∀ a b : Fin n,
      (Matrix.conjTranspose U * Matrix.diagonal (fun i => (d i : ℂ))) a b =
        star (U b a) * (d b : ℂ) := by
    intro a b
    rw [Matrix.mul_apply,
      Finset.sum_eq_single b
        (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
        (fun hcon => absurd (Finset.mem_univ b) hcon),
      Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
  have hmul' : ∀ a b : Fin k,
      (Matrix.conjTranspose (complexLeadingBlock h U) *
        Matrix.diagonal (fun m : Fin k => (d (Fin.castLE h m) : ℂ))) a b =
          star (U (Fin.castLE h b) (Fin.castLE h a)) * (d (Fin.castLE h b) : ℂ) := by
    intro a b
    rw [Matrix.mul_apply,
      Finset.sum_eq_single b
        (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
        (fun hcon => absurd (Finset.mem_univ b) hcon),
      Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
    rfl
  have hLHS : complexLeadingBlock h
      (Matrix.conjTranspose U * Matrix.diagonal (fun i => (d i : ℂ)) * U) i j =
      ∑ m : Fin n,
        star (U m (Fin.castLE h i)) * (d m : ℂ) * U m (Fin.castLE h j) := by
    show (Matrix.conjTranspose U * Matrix.diagonal (fun i => (d i : ℂ)) * U)
      (Fin.castLE h i) (Fin.castLE h j) = _
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [hmul]
  have hRHS :
      (Matrix.conjTranspose (complexLeadingBlock h U) *
        Matrix.diagonal (fun m : Fin k => (d (Fin.castLE h m) : ℂ)) *
          complexLeadingBlock h U) i j =
      ∑ m : Fin k,
        star (U (Fin.castLE h m) (Fin.castLE h i)) *
          (d (Fin.castLE h m) : ℂ) * U (Fin.castLE h m) (Fin.castLE h j) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [hmul']; rfl
  rw [hLHS, hRHS]
  have hinj : Set.InjOn (Fin.castLE h)
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
    intro a _ b _ hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)
  rw [← Finset.sum_image
    (f := fun m : Fin n =>
      star (U m (Fin.castLE h i)) * (d m : ℂ) * U m (Fin.castLE h j)) hinj]
  refine (Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_).symm
  have hmk : k ≤ (m : ℕ) := by
    by_contra hcon
    exact hm (Finset.mem_image.2
      ⟨⟨(m : ℕ), by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hlt : Fin.castLE h i < m := by
    refine Fin.lt_def.2 ?_
    have hi := i.isLt
    simp only [Fin.val_castLE]
    omega
  rw [hU m (Fin.castLE h i) hlt, star_zero, zero_mul, zero_mul]

/-- Determinant of a complex Jacobi form is its real diagonal product. -/
theorem ComplexJacobiData.det_form (J : ComplexJacobiData n) :
    J.form.det = ((∏ m, J.d m : ℝ) : ℂ) := by
  rw [ComplexJacobiData.form, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.det_diagonal, J.det_eq_one]
  simp

/-- Determinant of a leading complex Jacobi block is the corresponding weight product. -/
theorem complexDetLeadingBlock_form {k : ℕ} (h : k ≤ n) (J : ComplexJacobiData n) :
    (complexLeadingBlock h J.form).det =
      ((∏ m : Fin k, J.d (Fin.castLE h m) : ℝ) : ℂ) := by
  rw [ComplexJacobiData.form, complexLeadingBlock_congr h J.upper J.d,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal]
  have hdet : (complexLeadingBlock h J.U).det = 1 :=
    complex_det_eq_one_of_unipotent
      (complexLeadingBlock_upper h J.upper) (complexLeadingBlock_unit h J.unit)
  rw [hdet]
  simp

/-- Leading truncation of complex Jacobi data. -/
def ComplexJacobiData.trunc (J : ComplexJacobiData n) {k : ℕ} (hk : k ≤ n) :
    ComplexJacobiData k where
  U := complexLeadingBlock hk J.U
  d := fun m => J.d (Fin.castLE hk m)
  pos := fun _ => J.pos _
  upper := fun i j hji => complexLeadingBlock_upper hk J.upper i j hji
  unit := fun i => complexLeadingBlock_unit hk J.unit i

/-- Form of a complex Jacobi truncation is the leading block. -/
theorem ComplexJacobiData.trunc_form (J : ComplexJacobiData n)
    {k : ℕ} (hk : k ≤ n) :
    (J.trunc hk).form = complexLeadingBlock hk J.form := by
  exact (complexLeadingBlock_congr hk J.upper J.d).symm

/-- Complex Siegel bounds are inherited by leading truncations. -/
theorem ComplexJacobiData.trunc_isSiegel (J : ComplexJacobiData n)
    {k : ℕ} (hk : k ≤ n) {t u : ℝ} (hS : J.IsSiegel t u) :
    (J.trunc hk).IsSiegel t u := by
  refine ⟨fun i j hij => ?_, fun i j => hS.2 _ _⟩
  exact hS.1 (Fin.castLE hk i) (Fin.castLE hk j) (by simpa using hij)

end GaloisForLFunctions.HTGeometry
