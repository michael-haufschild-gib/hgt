import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity

/-!
# Rank-one Schur--Gaussian determinant curvature

This module proves the arbitrary-background rank-one law.  If `C` is a real positive-definite
matrix and `a` is a real label vector, Schur multiplication by

`exp (t * a i * a j)`

has an exact negative-square logarithmic determinant curvature.  Equivalently, Schur
multiplication by the one-dimensional Gaussian semigroup

`exp (-t * (a i - a j)^(2 : ℕ))`

has a globally concave log determinant on the nonnegative half-line.  The background matrix is
arbitrary; it need not itself be a one-dimensional Gaussian Gram matrix.
-/

open Filter
open scoped BigOperators Matrix MatrixOrder

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-! ### Positive square-root similarity parent algebra -/

/-- Similarity by the positive square root of a positive-definite matrix. -/
def matrixSqrtSimilarity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M D : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  CFC.sqrt M * D * (CFC.sqrt M)⁻¹

theorem matrixSqrt_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef) :
    CFC.sqrt M * CFC.sqrt M = M := by
  exact CFC.sqrt_mul_sqrt_self _ hM.posSemidef.nonneg

theorem matrixSqrt_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) :
    (CFC.sqrt M).transpose = CFC.sqrt M := by
  have hstar := (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
  rw [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at hstar
  exact hstar

theorem matrix_inv_eq_sqrt_inv_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef) :
    M⁻¹ = (CFC.sqrt M)⁻¹ * (CFC.sqrt M)⁻¹ := by
  let R := CFC.sqrt M
  letI : Invertible M :=
    Matrix.invertibleOfIsUnitDet M (M.isUnit_iff_isUnit_det.mp hM.isUnit)
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  letI : Invertible R := hRunit.nonempty_invertible.some
  have hR2 : R * R = M := matrixSqrt_mul_self M hM
  apply Matrix.mul_left_injective_of_invertible (A := M)
  change M⁻¹ * M = (R⁻¹ * R⁻¹) * M
  rw [Matrix.inv_mul_of_invertible, ← hR2]
  have hcancel : R⁻¹ * R = 1 :=
    Matrix.inv_mul_of_invertible _
  symm
  calc
    (R⁻¹ * R⁻¹) * (R * R) = R⁻¹ * (R⁻¹ * R) * R := by noncomm_ring
    _ = R⁻¹ * R := by rw [hcancel]; simp
    _ = 1 := hcancel

theorem matrixSqrtSimilarity_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M D : Matrix ι ι ℝ) (hD : D.transpose = D) :
    (matrixSqrtSimilarity M D).transpose =
      (CFC.sqrt M)⁻¹ * D * CFC.sqrt M := by
  unfold matrixSqrtSimilarity
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv, matrixSqrt_transpose, hD]
  noncomm_ring

/-- Hilbert--Schmidt energy of a positive-square-root similarity, expressed in the original
nonorthonormal Gram coordinates. -/
theorem matrixHilbertSchmidtEnergy_sqrtSimilarity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef)
    (D : Matrix ι ι ℝ) (hD : D.transpose = D) :
    matrixHilbertSchmidtEnergy (matrixSqrtSimilarity M D) =
      Matrix.trace (M⁻¹ * D * M * D) := by
  let R := CFC.sqrt M
  let Ri := (CFC.sqrt M)⁻¹
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  letI : Invertible R := hRunit.nonempty_invertible.some
  have hR2 : R * R = M := matrixSqrt_mul_self M hM
  have hRi2 : Ri * Ri = M⁻¹ := (matrix_inv_eq_sqrt_inv_mul M hM).symm
  have htrans : (R * D * Ri).transpose = Ri * D * R := by
    dsimp [Ri, R]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      matrixSqrt_transpose, hD]
    noncomm_ring
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul]
  change Matrix.trace ((R * D * Ri).transpose * (R * D * Ri)) =
    Matrix.trace (M⁻¹ * D * M * D)
  rw [htrans, ← hRi2, ← hR2]
  calc
    Matrix.trace ((Ri * D * R) * (R * D * Ri)) =
        Matrix.trace ((Ri * D * (R * R) * D) * Ri) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (Ri * (Ri * D * (R * R) * D)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Ri * Ri) * D * (R * R) * D) := by
      congr 1
      noncomm_ring

theorem matrixSqrtSimilarity_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef) (D E : Matrix ι ι ℝ) :
    matrixSqrtSimilarity M D * matrixSqrtSimilarity M E =
      matrixSqrtSimilarity M (D * E) := by
  have hRunit : IsUnit (CFC.sqrt M) :=
    (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  letI : Invertible (CFC.sqrt M) := hRunit.nonempty_invertible.some
  have hcancel : (CFC.sqrt M)⁻¹ * CFC.sqrt M = 1 :=
    Matrix.inv_mul_of_invertible _
  unfold matrixSqrtSimilarity
  calc
    (CFC.sqrt M * D * (CFC.sqrt M)⁻¹) *
        (CFC.sqrt M * E * (CFC.sqrt M)⁻¹) =
      CFC.sqrt M * D * ((CFC.sqrt M)⁻¹ * CFC.sqrt M) * E *
        (CFC.sqrt M)⁻¹ := by noncomm_ring
    _ = CFC.sqrt M * (D * E) * (CFC.sqrt M)⁻¹ := by
      rw [hcancel]
      noncomm_ring

/-- A real eigenvector of a real normal matrix is also an eigenvector of its transpose. -/
theorem matrix_transpose_mulVec_eq_smul_of_normal_real_eigenvector
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (lam : ℝ)
    (hnormal : matrixSelfCommutator A = 0)
    (hv : A *ᵥ v = lam • v) :
    A.transpose *ᵥ v = lam • v := by
  have hcomm : A * A.transpose = A.transpose * A := by
    unfold matrixSelfCommutator at hnormal
    exact sub_eq_zero.mp hnormal
  have henergy0 :
      (A.transpose *ᵥ v) ⬝ᵥ (A.transpose *ᵥ v) =
        (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
    calc
      (A.transpose *ᵥ v) ⬝ᵥ (A.transpose *ᵥ v) =
          v ⬝ᵥ A *ᵥ (A.transpose *ᵥ v) :=
        Matrix.dotProduct_transpose_mulVec A (A.transpose *ᵥ v) v
      _ = v ⬝ᵥ (A * A.transpose) *ᵥ v := by
        rw [Matrix.mulVec_mulVec]
      _ = v ⬝ᵥ (A.transpose * A) *ᵥ v := by rw [hcomm]
      _ = v ⬝ᵥ A.transpose *ᵥ (A *ᵥ v) := by
        rw [Matrix.mulVec_mulVec]
      _ = (A *ᵥ v) ⬝ᵥ (A *ᵥ v) :=
        Matrix.dotProduct_transpose_mulVec A v (A *ᵥ v)
  have henergy :
      (A.transpose *ᵥ v) ⬝ᵥ (A.transpose *ᵥ v) =
        lam ^ 2 * (v ⬝ᵥ v) := by
    rw [henergy0, hv]
    simp [pow_two]
    ring
  have hcross : v ⬝ᵥ (A.transpose *ᵥ v) = lam * (v ⬝ᵥ v) := by
    calc
      v ⬝ᵥ (A.transpose *ᵥ v) = v ⬝ᵥ (A *ᵥ v) :=
        Matrix.dotProduct_transpose_mulVec A v v
      _ = v ⬝ᵥ (lam • v) := by rw [hv]
      _ = lam * (v ⬝ᵥ v) := by simp
  have hcross' : (A.transpose *ᵥ v) ⬝ᵥ v = lam * (v ⬝ᵥ v) := by
    rw [dotProduct_comm]
    exact hcross
  apply sub_eq_zero.mp
  apply dotProduct_self_eq_zero.mp
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul]
  rw [henergy, hcross, hcross']
  simp only [smul_eq_mul]
  ring

/-- Real eigenvectors of a real normal matrix belonging to distinct eigenvalues are orthogonal. -/
theorem matrix_dotProduct_eq_zero_of_normal_distinct_real_eigenvectors
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (v w : ι → ℝ) (lam mu : ℝ)
    (hnormal : matrixSelfCommutator A = 0)
    (hv : A *ᵥ v = lam • v) (hw : A *ᵥ w = mu • w)
    (hne : lam ≠ mu) :
    v ⬝ᵥ w = 0 := by
  have hwT : A.transpose *ᵥ w = mu • w :=
    matrix_transpose_mulVec_eq_smul_of_normal_real_eigenvector A w mu hnormal hw
  have hscalar : lam * (v ⬝ᵥ w) = mu * (v ⬝ᵥ w) := by
    calc
      lam * (v ⬝ᵥ w) = (lam • v) ⬝ᵥ w := by simp
      _ = (A *ᵥ v) ⬝ᵥ w := by rw [hv]
      _ = w ⬝ᵥ (A *ᵥ v) := dotProduct_comm _ _
      _ = v ⬝ᵥ (A.transpose *ᵥ w) :=
        (Matrix.dotProduct_transpose_mulVec A v w).symm
      _ = v ⬝ᵥ (mu • w) := by rw [hwT]
      _ = mu * (v ⬝ᵥ w) := by simp
  have hprod : (lam - mu) * (v ⬝ᵥ w) = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

/-- If the original Gram matrix commutes with the symmetric generator, then its square-root
similarity is exactly the generator and hence has zero self-commutator. -/
theorem matrixSelfCommutator_sqrtSimilarity_eq_zero_of_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef)
    (D : Matrix ι ι ℝ) (hD : D.transpose = D)
    (hcomm : M * D = D * M) :
    matrixSelfCommutator (matrixSqrtSimilarity M D) = 0 := by
  let R := CFC.sqrt M
  let Ri := (CFC.sqrt M)⁻¹
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  letI : Invertible R := hRunit.nonempty_invertible.some
  have hRcomm : R * D = D * R := by
    have hMD : Commute M D := hcomm
    have h := hMD.cfcₙ_nnreal NNReal.sqrt
    simpa [R, CFC.sqrt] using h.eq
  have hcancel : R * Ri = 1 := Matrix.mul_inv_of_invertible _
  have hsimilarity : matrixSqrtSimilarity M D = D := by
    change R * D * Ri = D
    calc
      R * D * Ri = D * R * Ri := by rw [hRcomm]
      _ = D * (R * Ri) := by noncomm_ring
      _ = D := by rw [hcancel]; simp
  rw [hsimilarity]
  unfold matrixSelfCommutator
  rw [hD]
  simp

/-- **Positive-Gram normality rigidity.**  If square-root similarity turns a real diagonal
observable into a normal matrix, then Gram vectors carrying distinct observable values are
orthogonal. -/
theorem matrixSqrtSimilarity_selfCommutator_eq_zero_implies_diagonal_blocks
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef) (a : ι → ℝ)
    (hnormal : matrixSelfCommutator
      (matrixSqrtSimilarity M (Matrix.diagonal a)) = 0) :
    ∀ i j, a i ≠ a j → M i j = 0 := by
  let R := CFC.sqrt M
  let Ri := (CFC.sqrt M)⁻¹
  let D := Matrix.diagonal a
  let A := R * D * Ri
  have hnormalA : matrixSelfCommutator A = 0 := by
    simpa [A, R, Ri, D, matrixSqrtSimilarity] using hnormal
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  letI : Invertible R := hRunit.nonempty_invertible.some
  have hcancel : Ri * R = 1 := by
    dsimp [Ri]
    exact Matrix.inv_mul_of_invertible _
  have hR2 : R * R = M := matrixSqrt_mul_self M hM
  have hRsymm : R.transpose = R := by
    dsimp [R]
    exact matrixSqrt_transpose M
  have hAR : A * R = R * D := by
    dsimp [A]
    calc
      (R * D * Ri) * R = R * D * (Ri * R) := by noncomm_ring
      _ = R * D := by rw [hcancel]; simp
  have heigen (i : ι) : A *ᵥ R.col i = a i • R.col i := by
    change (A * R).col i = a i • R.col i
    rw [hAR]
    ext k
    simp [D, Matrix.mul_diagonal]
    ring
  intro i j hij
  have horth : R.col i ⬝ᵥ R.col j = 0 :=
    matrix_dotProduct_eq_zero_of_normal_distinct_real_eigenvectors
      A (R.col i) (R.col j) (a i) (a j) hnormalA
      (heigen i) (heigen j) hij
  calc
    M i j = (R.col i ⬝ᵥ R.col j) := by
      rw [← hR2]
      simp only [Matrix.mul_apply, dotProduct]
      apply Finset.sum_congr rfl
      intro k _
      have hk := congrFun (congrFun hRsymm k) i
      simp only [Matrix.transpose_apply] at hk
      change R i k * R k j = R k i * R k j
      rw [hk]
    _ = 0 := horth

/-- A diagonal observable commutes with a matrix exactly when the matrix has no entries between
distinct observable-value blocks. -/
theorem diagonal_commutes_matrix_iff_zero_off_label_blocks
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (a : ι → ℝ) :
    Matrix.diagonal a * M = M * Matrix.diagonal a ↔
      ∀ i j, a i ≠ a j → M i j = 0 := by
  constructor
  · intro h i j hij
    have hentry := congrFun (congrFun h i) j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
    have hprod : M i j * (a i - a j) = 0 := by
      calc
        M i j * (a i - a j) = a i * M i j - M i j * a j := by ring
        _ = 0 := sub_eq_zero.mpr hentry
    exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hij)
  · intro hblock
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : a i = a j
    · rw [hij]
      ring
    · rw [hblock i j hij]
      simp

/-- Exact equality classification for positive-Gram square-root similarity by a diagonal
observable. -/
theorem matrixSqrtSimilarity_selfCommutator_eq_zero_iff_diagonal_blocks
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef) (a : ι → ℝ) :
    matrixSelfCommutator (matrixSqrtSimilarity M (Matrix.diagonal a)) = 0 ↔
      ∀ i j, a i ≠ a j → M i j = 0 := by
  constructor
  · exact matrixSqrtSimilarity_selfCommutator_eq_zero_implies_diagonal_blocks M hM a
  · intro hblock
    apply matrixSelfCommutator_sqrtSimilarity_eq_zero_of_commute
      M hM (Matrix.diagonal a)
    · ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij, Ne.symm hij]
    · exact ((diagonal_commutes_matrix_iff_zero_off_label_blocks M a).2 hblock).symm

/-- Algebraic core of the rank-one law: the determinant-curvature jet generated by
`M' = D M D` and `M'' = D^(2 : ℕ) M D^(2 : ℕ)` is exactly minus one half of a self-commutator square. -/
theorem gramLogCurvatureJet_diagonalCongruence_eq_neg_selfCommutator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosDef)
    (D : Matrix ι ι ℝ) (hD : D.transpose = D) :
    gramLogCurvatureJet M (D * M * D) ((D * D) * M * (D * D)) =
      -matrixHilbertSchmidtEnergy
        (matrixSelfCommutator (matrixSqrtSimilarity M D)) / 2 := by
  let R := CFC.sqrt M
  let Ri := (CFC.sqrt M)⁻¹
  let A := matrixSqrtSimilarity M D
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  letI : Invertible R := hRunit.nonempty_invertible.some
  have hR2 : R * R = M := matrixSqrt_mul_self M hM
  have hRi2 : Ri * Ri = M⁻¹ := (matrix_inv_eq_sqrt_inv_mul M hM).symm
  have hD2 : (D * D).transpose = D * D := by
    rw [Matrix.transpose_mul, hD]
  have hAsq : A * A = matrixSqrtSimilarity M (D * D) := by
    exact matrixSqrtSimilarity_mul M hM D D
  have hfirst :
      Matrix.trace (M⁻¹ * ((D * D) * M * (D * D))) =
        matrixHilbertSchmidtEnergy (A * A) := by
    calc
      Matrix.trace (M⁻¹ * ((D * D) * M * (D * D))) =
          Matrix.trace (M⁻¹ * (D * D) * M * (D * D)) := by
        congr 1
        noncomm_ring
      _ = matrixHilbertSchmidtEnergy (matrixSqrtSimilarity M (D * D)) :=
        (matrixHilbertSchmidtEnergy_sqrtSimilarity M hM (D * D) hD2).symm
      _ = matrixHilbertSchmidtEnergy (A * A) := by rw [hAsq]
  have hsecond :
      Matrix.trace (((M⁻¹ * (D * M * D)) * M⁻¹) * (D * M * D)) =
        Matrix.trace ((A.transpose * A) * (A.transpose * A)) := by
    rw [show A.transpose = Ri * D * R by
      dsimp [A, Ri, R]
      exact matrixSqrtSimilarity_transpose M D hD]
    change Matrix.trace (((M⁻¹ * (D * M * D)) * M⁻¹) * (D * M * D)) =
      Matrix.trace (((Ri * D * R) * (R * D * Ri)) *
        ((Ri * D * R) * (R * D * Ri)))
    rw [← hRi2, ← hR2]
    symm
    calc
      Matrix.trace (((Ri * D * R) * (R * D * Ri)) *
          ((Ri * D * R) * (R * D * Ri))) =
        Matrix.trace ((Ri * D * (R * R) * D * (Ri * Ri) * D *
          (R * R) * D) * Ri) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace (Ri * (Ri * D * (R * R) * D * (Ri * Ri) * D *
          (R * R) * D)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((((Ri * Ri) * (D * (R * R) * D)) * (Ri * Ri)) *
          (D * (R * R) * D)) := by
            congr 1
            noncomm_ring
  unfold gramLogCurvatureJet
  rw [Matrix.trace_sub, hfirst, hsecond]
  rw [selfCommutator_energy_eq_two_mul_defect]
  ring

/-! ### The arbitrary-background Schur exponential path -/

/-- Schur multiplication of a background matrix by a rank-one exponential semigroup. -/
def rankOneSchurExponentialPath {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => C i j * Real.exp (t * a i * a j)

/-- First entrywise jet of the rank-one Schur exponential path. -/
def rankOneSchurExponentialFirst {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => C i j * (a i * a j) * Real.exp (t * a i * a j)

/-- Second entrywise jet of the rank-one Schur exponential path. -/
def rankOneSchurExponentialSecond {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => C i j * (a i * a j) ^ 2 * Real.exp (t * a i * a j)

/-- Diagonal matrix of the rank-one labels. -/
def rankOneLabelDiagonal {n : ℕ} (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal a

theorem rankOneLabelDiagonal_transpose {n : ℕ} (a : Fin n → ℝ) :
    (rankOneLabelDiagonal a).transpose = rankOneLabelDiagonal a := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [rankOneLabelDiagonal]
  · simp [rankOneLabelDiagonal, hij, Ne.symm hij]

theorem rankOneSchurExponentialFirst_eq_diagonal_mul {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) :
    rankOneSchurExponentialFirst C a t =
      rankOneLabelDiagonal a * rankOneSchurExponentialPath C a t *
        rankOneLabelDiagonal a := by
  ext i j
  simp [rankOneSchurExponentialFirst, rankOneSchurExponentialPath,
    rankOneLabelDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem rankOneSchurExponentialSecond_eq_diagonal_mul {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) :
    rankOneSchurExponentialSecond C a t =
      (rankOneLabelDiagonal a * rankOneLabelDiagonal a) *
        rankOneSchurExponentialPath C a t *
          (rankOneLabelDiagonal a * rankOneLabelDiagonal a) := by
  ext i j
  simp [rankOneSchurExponentialSecond, rankOneSchurExponentialPath,
    rankOneLabelDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  ring

/-- Exact block classification for commutation with the label diagonal. -/
theorem rankOneLabelDiagonal_commutes_rankOneSchurExponentialPath_iff {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) :
    rankOneLabelDiagonal a * rankOneSchurExponentialPath C a t =
        rankOneSchurExponentialPath C a t * rankOneLabelDiagonal a ↔
      ∀ i j, a i ≠ a j → C i j = 0 := by
  constructor
  · intro h i j hij
    have hentry := congrFun (congrFun h i) j
    simp [rankOneLabelDiagonal, rankOneSchurExponentialPath,
      Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
    have hprod :
        (C i j * Real.exp (t * a i * a j)) * (a i - a j) = 0 := by
      calc
        (C i j * Real.exp (t * a i * a j)) * (a i - a j) =
            a i * (C i j * Real.exp (t * a i * a j)) -
              C i j * Real.exp (t * a i * a j) * a j := by ring
        _ = 0 := sub_eq_zero.mpr hentry
    have hce : C i j * Real.exp (t * a i * a j) = 0 :=
      (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hij)
    exact (mul_eq_zero.mp hce).resolve_right (Real.exp_ne_zero _)
  · intro hblock
    ext i j
    simp [rankOneLabelDiagonal, rankOneSchurExponentialPath,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : a i = a j
    · rw [hij]
      ring
    · rw [hblock i j hij]
      simp

theorem hasDerivAt_rankOneSchurExponentialPath {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s => rankOneSchurExponentialPath C a s i j)
      (rankOneSchurExponentialFirst C a t i j) t := by
  have harg0 := (hasDerivAt_id (x := t)).mul_const (a i * a j)
  have harg : HasDerivAt (fun s : ℝ => s * a i * a j) (a i * a j) t := by
    convert! harg0 using 1
    · funext s
      simp only [id_eq]
      ring
    · ring
  convert! harg.exp.const_mul (C i j) using 1
  simp [rankOneSchurExponentialFirst]
  ring

theorem hasDerivAt_rankOneSchurExponentialFirst {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s => rankOneSchurExponentialFirst C a s i j)
      (rankOneSchurExponentialSecond C a t i j) t := by
  have harg0 := (hasDerivAt_id (x := t)).mul_const (a i * a j)
  have harg : HasDerivAt (fun s : ℝ => s * a i * a j) (a i * a j) t := by
    convert! harg0 using 1
    · funext s
      simp only [id_eq]
      ring
    · ring
  convert! harg.exp.const_mul (C i j * (a i * a j)) using 1
  simp [rankOneSchurExponentialSecond]
  ring

/-- The exponential tail beyond degree zero is positive semidefinite at every nonnegative
scale. -/
theorem rankOneExponentialTail_posSemidef {n : ℕ}
    (a : Fin n → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    Matrix.PosSemidef ((fun i j => Real.exp (t * a i * a j) - 1) :
      Matrix (Fin n) (Fin n) ℝ) := by
  let y : Fin n → Fin 1 → ℝ := fun i _ => Real.sqrt t * a i
  have htail := gaussianCoherentGram_sub_truncation_posSemidef y 0
  convert! htail using 1
  ext i j
  simp [gaussianCoherentGram, truncatedExponentialInnerMatrix,
    truncatedExpSeries, coordinateDot, y]
  calc
    t * a i * a j = (Real.sqrt t * Real.sqrt t) * a i * a j := by
      rw [Real.mul_self_sqrt ht]
    _ = Real.sqrt t * a i * (Real.sqrt t * a j) := by ring

/-- An arbitrary positive-definite background remains positive definite after Schur
multiplication by the rank-one exponential semigroup. -/
theorem rankOneSchurExponentialPath_posDef {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    (rankOneSchurExponentialPath C a t).PosDef := by
  let P : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => Real.exp (t * a i * a j) - 1
  have hP : P.PosSemidef := rankOneExponentialTail_posSemidef a t ht
  have hCP : (C ⊙ P).PosSemidef := hC.posSemidef.hadamard hP
  have hadd := hC.add_posSemidef hCP
  convert! hadd using 1
  ext i j
  simp [rankOneSchurExponentialPath, P, Matrix.hadamard]
  ring

/-- The block condition from the paper theorem is sufficient for equality in the exact
self-commutator curvature identity. -/
theorem rankOneSchurExponential_selfCommutator_eq_zero_of_block {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t)
    (hblock : ∀ i j, a i ≠ a j → C i j = 0) :
    matrixSelfCommutator
      (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
        (rankOneLabelDiagonal a)) = 0 := by
  apply matrixSelfCommutator_sqrtSimilarity_eq_zero_of_commute
    (rankOneSchurExponentialPath C a t)
    (rankOneSchurExponentialPath_posDef C a hC t ht)
    (rankOneLabelDiagonal a) (rankOneLabelDiagonal_transpose a)
  exact ((rankOneLabelDiagonal_commutes_rankOneSchurExponentialPath_iff C a t).2 hblock).symm

/-- **Sharp equality classification for the rank-one Schur path.**  Curvature vanishes exactly
when the background has no coupling between distinct label blocks. -/
theorem rankOneSchurExponential_selfCommutator_eq_zero_iff_block {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    matrixSelfCommutator
        (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
          (rankOneLabelDiagonal a)) = 0 ↔
      ∀ i j, a i ≠ a j → C i j = 0 := by
  constructor
  · intro hnormal
    have hHblock :
        ∀ i j, a i ≠ a j → rankOneSchurExponentialPath C a t i j = 0 :=
      (matrixSqrtSimilarity_selfCommutator_eq_zero_iff_diagonal_blocks
        (rankOneSchurExponentialPath C a t)
        (rankOneSchurExponentialPath_posDef C a hC t ht) a).1 (by
          simpa [rankOneLabelDiagonal] using hnormal)
    intro i j hij
    have hzero := hHblock i j hij
    simp only [rankOneSchurExponentialPath] at hzero
    exact (mul_eq_zero.mp hzero).resolve_right (Real.exp_ne_zero _)
  · exact rankOneSchurExponential_selfCommutator_eq_zero_of_block C a hC t ht

/-- The normality equality condition is equivalently commutation of the evolving Gram matrix
with the label observable. -/
theorem rankOneSchurExponential_selfCommutator_eq_zero_iff_commutes {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    matrixSelfCommutator
        (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
          (rankOneLabelDiagonal a)) = 0 ↔
      rankOneLabelDiagonal a * rankOneSchurExponentialPath C a t =
        rankOneSchurExponentialPath C a t * rankOneLabelDiagonal a := by
  rw [rankOneSchurExponential_selfCommutator_eq_zero_iff_block C a hC t ht,
    rankOneLabelDiagonal_commutes_rankOneSchurExponentialPath_iff C a t]

/-- **Exact rank-one Schur curvature identity.** -/
theorem gramLogCurvatureJet_rankOneSchurExponential_eq_neg_selfCommutator {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    gramLogCurvatureJet (rankOneSchurExponentialPath C a t)
        (rankOneSchurExponentialFirst C a t)
        (rankOneSchurExponentialSecond C a t) =
      -matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
            (rankOneLabelDiagonal a))) / 2 := by
  rw [rankOneSchurExponentialFirst_eq_diagonal_mul,
    rankOneSchurExponentialSecond_eq_diagonal_mul]
  exact gramLogCurvatureJet_diagonalCongruence_eq_neg_selfCommutator
    (rankOneSchurExponentialPath C a t)
    (rankOneSchurExponentialPath_posDef C a hC t ht)
    (rankOneLabelDiagonal a) (rankOneLabelDiagonal_transpose a)

theorem hasDerivAt_rankOneSchurExponential_logDet {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => Real.log (rankOneSchurExponentialPath C a s).det)
      (deriv (fun s => Real.log (rankOneSchurExponentialPath C a s).det) t) t := by
  apply DifferentiableAt.hasDerivAt
  have hdet := (rankOneSchurExponentialPath_posDef C a hC t ht).det_pos.ne'
  exact ((hasDerivAt_matrixDet (rankOneSchurExponentialPath C a)
    (rankOneSchurExponentialFirst C a t) t
    (hasDerivAt_rankOneSchurExponentialPath C a t)).log hdet).differentiableAt

theorem hasDerivAt_rankOneSchurExponential_logDetDerivative {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt
      (deriv (fun s => Real.log (rankOneSchurExponentialPath C a s).det))
      (-matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
            (rankOneLabelDiagonal a))) / 2) t := by
  have hpos := rankOneSchurExponentialPath_posDef C a hC t ht
  have hdetDeriv := hasDerivAt_matrixDet (rankOneSchurExponentialPath C a)
    (rankOneSchurExponentialFirst C a t) t
    (hasDerivAt_rankOneSchurExponentialPath C a t)
  have hdet : ∀ᶠ s in nhds t, (rankOneSchurExponentialPath C a s).det ≠ 0 :=
    hdetDeriv.continuousAt.eventually_ne hpos.det_pos.ne'
  have h := hasDerivAt_logDetDerivative_eq_gramLogCurvatureJet
    (rankOneSchurExponentialPath C a)
    (rankOneSchurExponentialFirst C a)
    (rankOneSchurExponentialSecond C a) t
    (hasDerivAt_rankOneSchurExponentialPath C a)
    (hasDerivAt_rankOneSchurExponentialFirst C a) hdet
  rw [gramLogCurvatureJet_rankOneSchurExponential_eq_neg_selfCommutator
    C a hC t ht] at h
  exact h

/-- The literal second derivative of the rank-one Schur log determinant is the exact negative
self-commutator square. -/
theorem rankOneSchurExponential_logDet_secondDerivative_eq {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s => Real.log (rankOneSchurExponentialPath C a s).det)) t =
      -matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
            (rankOneLabelDiagonal a))) / 2 := by
  exact (hasDerivAt_rankOneSchurExponential_logDetDerivative C a hC t ht).deriv

/-- The Schur-exponential log-determinant curvature vanishes exactly on the label-block
decomposition of the background. -/
theorem rankOneSchurExponential_logDet_secondDerivative_eq_zero_iff_block {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s => Real.log (rankOneSchurExponentialPath C a s).det)) t = 0 ↔
      ∀ i j, a i ≠ a j → C i j = 0 := by
  rw [rankOneSchurExponential_logDet_secondDerivative_eq C a hC t ht]
  let S := matrixSelfCommutator
    (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
      (rankOneLabelDiagonal a))
  constructor
  · intro hzero
    have henergy : matrixHilbertSchmidtEnergy S = 0 := by
      dsimp [S] at hzero ⊢
      linarith
    exact (rankOneSchurExponential_selfCommutator_eq_zero_iff_block C a hC t ht).1
      ((matrixHilbertSchmidtEnergy_eq_zero_iff S).1 henergy)
  · intro hblock
    have hS : S = 0 :=
      (rankOneSchurExponential_selfCommutator_eq_zero_iff_block C a hC t ht).2 hblock
    have henergy : matrixHilbertSchmidtEnergy S = 0 :=
      (matrixHilbertSchmidtEnergy_eq_zero_iff S).2 hS
    dsimp [S] at henergy ⊢
    rw [henergy]
    norm_num

/-- Nontrivial label coupling makes the Schur-exponential log-determinant curvature strictly
negative at every nonnegative scale. -/
theorem rankOneSchurExponential_logDet_secondDerivative_lt_zero {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t)
    (hentries : ∀ i j, C i j ≠ 0)
    (hlabels : ∃ i j, a i ≠ a j) :
    deriv (deriv (fun s => Real.log (rankOneSchurExponentialPath C a s).det)) t < 0 := by
  let S := matrixSelfCommutator
    (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
      (rankOneLabelDiagonal a))
  have hS : S ≠ 0 := by
    intro hzero
    have hblock :=
      (rankOneSchurExponential_selfCommutator_eq_zero_iff_block C a hC t ht).1 hzero
    obtain ⟨i, j, hij⟩ := hlabels
    exact hentries i j (hblock i j hij)
  have henergy_ne : matrixHilbertSchmidtEnergy S ≠ 0 := by
    intro hzero
    exact hS ((matrixHilbertSchmidtEnergy_eq_zero_iff S).1 hzero)
  have henergy_pos : 0 < matrixHilbertSchmidtEnergy S :=
    lt_of_le_of_ne (matrixHilbertSchmidtEnergy_nonneg S) henergy_ne.symm
  rw [rankOneSchurExponential_logDet_secondDerivative_eq C a hC t ht]
  dsimp [S] at henergy_pos ⊢
  linarith

/-- The arbitrary-background rank-one Schur exponential log determinant is globally concave on
the closed nonnegative half-line. -/
theorem rankOneSchurExponential_logDet_concaveOn {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hC : C.PosDef) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun t => Real.log (rankOneSchurExponentialPath C a t).det) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 0)
    (f' := deriv (fun t => Real.log (rankOneSchurExponentialPath C a t).det))
    (f'' := fun t =>
      -matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
            (rankOneLabelDiagonal a))) / 2)
  · intro t ht
    exact (hasDerivAt_rankOneSchurExponential_logDet C a hC t ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      have : 0 < t := by simpa using ht
      exact this.le
    exact (hasDerivAt_rankOneSchurExponential_logDet C a hC t ht0).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      have : 0 < t := by simpa using ht
      exact this.le
    exact (hasDerivAt_rankOneSchurExponential_logDetDerivative C a hC t ht0).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      have : 0 < t := by simpa using ht
      exact this.le
    have henergy := matrixHilbertSchmidtEnergy_nonneg
      (matrixSelfCommutator
        (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
          (rankOneLabelDiagonal a)))
    linarith

/-! ### One-dimensional Gaussian semigroup form -/

/-- Schur multiplication by the one-dimensional Gaussian distance semigroup. -/
def rankOneSchurGaussianPath {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => C i j * Real.exp (-t * (a i - a j) ^ 2)

/-- Diagonal gauge converting the Gaussian distance path to the exponential-inner-product
path. -/
def rankOneSchurGaussianGauge {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => Real.exp (-t * a i ^ 2)

theorem rankOneSchurGaussianPath_factorization {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) :
    rankOneSchurGaussianPath C a t =
      rankOneSchurGaussianGauge a t *
        rankOneSchurExponentialPath C a (2 * t) *
          rankOneSchurGaussianGauge a t := by
  ext i j
  simp [rankOneSchurGaussianPath, rankOneSchurGaussianGauge,
    rankOneSchurExponentialPath, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [show -(t * (a i - a j) ^ 2) =
      (-(t * a i ^ 2) + 2 * t * a i * a j) + (-(t * a j ^ 2)) by ring]
  rw [Real.exp_add, Real.exp_add]
  ring

theorem rankOneSchurGaussianGauge_det {n : ℕ}
    (a : Fin n → ℝ) (t : ℝ) :
    (rankOneSchurGaussianGauge a t).det =
      Real.exp (-t * ∑ i, a i ^ 2) := by
  rw [rankOneSchurGaussianGauge, Matrix.det_diagonal, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

theorem rankOneSchurGaussianPath_det {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (t : ℝ) :
    (rankOneSchurGaussianPath C a t).det =
      Real.exp (-2 * t * ∑ i, a i ^ 2) *
        (rankOneSchurExponentialPath C a (2 * t)).det := by
  rw [rankOneSchurGaussianPath_factorization, Matrix.det_mul, Matrix.det_mul,
    rankOneSchurGaussianGauge_det]
  calc
    Real.exp (-t * ∑ i, a i ^ 2) *
          (rankOneSchurExponentialPath C a (2 * t)).det *
            Real.exp (-t * ∑ i, a i ^ 2) =
        (Real.exp (-t * ∑ i, a i ^ 2) *
          Real.exp (-t * ∑ i, a i ^ 2)) *
            (rankOneSchurExponentialPath C a (2 * t)).det := by ring
    _ = Real.exp ((-t * ∑ i, a i ^ 2) + (-t * ∑ i, a i ^ 2)) *
          (rankOneSchurExponentialPath C a (2 * t)).det := by
            rw [Real.exp_add]
    _ = Real.exp (-2 * t * ∑ i, a i ^ 2) *
          (rankOneSchurExponentialPath C a (2 * t)).det := by
            congr 2
            ring

theorem rankOneSchurGaussian_logDet_eq_affine_add {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    Real.log (rankOneSchurGaussianPath C a t).det =
      -2 * t * ∑ i, a i ^ 2 +
        Real.log (rankOneSchurExponentialPath C a (2 * t)).det := by
  rw [rankOneSchurGaussianPath_det,
    Real.log_mul (Real.exp_ne_zero _)
      (rankOneSchurExponentialPath_posDef C a hC (2 * t) (by linarith)).det_pos.ne',
    Real.log_exp]

/-- The Gaussian distance parametrization has the literal curvature
`-2 * ‖[A_{2t}, A_{2t}ᵀ]‖²`.  This is the exact differential form behind the global
concavity theorem below. -/
theorem rankOneSchurGaussian_logDet_secondDerivative_eq {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s => Real.log (rankOneSchurGaussianPath C a s).det)) t =
      -2 * matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (matrixSqrtSimilarity (rankOneSchurExponentialPath C a (2 * t))
            (rankOneLabelDiagonal a))) := by
  let H : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    rankOneSchurExponentialPath C a
  let H₁ : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    rankOneSchurExponentialFirst C a
  let f : ℝ → ℝ := fun u => Real.log (H u).det
  let g : ℝ → ℝ := fun s => f (2 * s)
  let k : ℝ → ℝ := fun s => Real.log (rankOneSchurGaussianPath C a s).det
  let S : ℝ := ∑ i, a i ^ 2
  let E : ℝ := matrixHilbertSchmidtEnergy
    (matrixSelfCommutator
      (matrixSqrtSimilarity (H (2 * t)) (rankOneLabelDiagonal a)))
  have hscale (s : ℝ) : HasDerivAt (fun u : ℝ => 2 * u) 2 s := by
    convert! (hasDerivAt_id (x := s)).const_mul 2 using 1
    simp
  have hpos : (H (2 * t)).PosDef := by
    exact rankOneSchurExponentialPath_posDef C a hC (2 * t) (by linarith)
  have hdetAt := hasDerivAt_matrixDet H (H₁ (2 * t)) (2 * t)
    (hasDerivAt_rankOneSchurExponentialPath C a (2 * t))
  have hdet : ∀ᶠ s in nhds t, (H (2 * s)).det ≠ 0 :=
    (hdetAt.comp t (hscale t)).continuousAt.eventually_ne hpos.det_pos.ne'
  have hfdiff : ∀ᶠ s in nhds t, DifferentiableAt ℝ f (2 * s) := by
    filter_upwards [hdet] with s hs
    exact ((hasDerivAt_matrixDet H (H₁ (2 * s)) (2 * s)
      (hasDerivAt_rankOneSchurExponentialPath C a (2 * s))).log hs).differentiableAt
  have hgdiff : ∀ᶠ s in nhds t, DifferentiableAt ℝ g s := by
    filter_upwards [hfdiff] with s hs
    exact hs.comp s (hscale s).differentiableAt
  have hfirst :
      deriv g =ᶠ[nhds t] fun s => 2 * deriv f (2 * s) := by
    filter_upwards [hfdiff] with s hs
    have hcomp := hs.hasDerivAt.comp s (hscale s)
    change deriv (fun u => f (2 * u)) s = 2 * deriv f (2 * s)
    rw [show (fun u => f (2 * u)) = f ∘ (fun u : ℝ => 2 * u) by rfl]
    rw [hcomp.deriv]
    ring
  have hfsecond : HasDerivAt (deriv f) (-E / 2) (2 * t) := by
    simpa [f, H, E] using
      hasDerivAt_rankOneSchurExponential_logDetDerivative C a hC (2 * t) (by linarith)
  have hmodel : HasDerivAt (fun s => 2 * deriv f (2 * s)) (-2 * E) t := by
    have hcomp := hfsecond.comp t (hscale t)
    convert! hcomp.const_mul 2 using 1
    ring
  have hgsecond : HasDerivAt (deriv g) (-2 * E) t :=
    hmodel.congr_of_eventuallyEq hfirst
  have hlog : k =ᶠ[nhds t] fun s => -2 * s * S + g s := by
    filter_upwards [hdet] with s hs
    dsimp [k, g, f, H, S]
    rw [rankOneSchurGaussianPath_det,
      Real.log_mul (Real.exp_ne_zero _) hs, Real.log_exp]
  have hrhsFirst :
      deriv (fun s => -2 * s * S + g s) =ᶠ[nhds t]
        fun s => deriv g s - 2 * S := by
    filter_upwards [hgdiff] with s hs
    have haffine : HasDerivAt (fun u : ℝ => -2 * u * S) (-2 * S) s := by
      have hbase := (hasDerivAt_id (x := s)).const_mul (-2 * S)
      convert! hbase using 1
      · funext u
        simp only [id_eq]
        ring
      · ring
    have hadd := haffine.add hs.hasDerivAt
    convert! hadd.deriv using 1
    ring
  have hkFirst : deriv k =ᶠ[nhds t] fun s => deriv g s - 2 * S :=
    hlog.deriv.trans hrhsFirst
  have hkSecond : HasDerivAt (deriv k) (-2 * E) t :=
    (hgsecond.sub_const (2 * S)).congr_of_eventuallyEq hkFirst
  simpa [k, E, H] using hkSecond.deriv

/-- Gaussian rank-one metric curvature vanishes exactly when the background splits along the
equal-label blocks. -/
theorem rankOneSchurGaussian_logDet_secondDerivative_eq_zero_iff_block {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s => Real.log (rankOneSchurGaussianPath C a s).det)) t = 0 ↔
      ∀ i j, a i ≠ a j → C i j = 0 := by
  rw [rankOneSchurGaussian_logDet_secondDerivative_eq C a hC t ht]
  let S := matrixSelfCommutator
    (matrixSqrtSimilarity (rankOneSchurExponentialPath C a (2 * t))
      (rankOneLabelDiagonal a))
  constructor
  · intro hzero
    have henergy : matrixHilbertSchmidtEnergy S = 0 := by
      dsimp [S] at hzero ⊢
      linarith
    exact (rankOneSchurExponential_selfCommutator_eq_zero_iff_block
      C a hC (2 * t) (by linarith)).1
        ((matrixHilbertSchmidtEnergy_eq_zero_iff S).1 henergy)
  · intro hblock
    have hS : S = 0 :=
      (rankOneSchurExponential_selfCommutator_eq_zero_iff_block
        C a hC (2 * t) (by linarith)).2 hblock
    have henergy : matrixHilbertSchmidtEnergy S = 0 :=
      (matrixHilbertSchmidtEnergy_eq_zero_iff S).2 hS
    dsimp [S] at henergy ⊢
    rw [henergy]
    norm_num

/-- If the background couples every pair and the rank-one labels are nonconstant, Gaussian
rank-one metric log-volume has strictly negative curvature at every nonnegative scale. -/
theorem rankOneSchurGaussian_logDet_secondDerivative_lt_zero {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t)
    (hentries : ∀ i j, C i j ≠ 0)
    (hlabels : ∃ i j, a i ≠ a j) :
    deriv (deriv (fun s => Real.log (rankOneSchurGaussianPath C a s).det)) t < 0 := by
  rw [rankOneSchurGaussian_logDet_secondDerivative_eq C a hC t ht]
  let S := matrixSelfCommutator
    (matrixSqrtSimilarity (rankOneSchurExponentialPath C a (2 * t))
      (rankOneLabelDiagonal a))
  have hS : S ≠ 0 := by
    intro hzero
    have hblock :=
      (rankOneSchurExponential_selfCommutator_eq_zero_iff_block
        C a hC (2 * t) (by linarith)).1 hzero
    obtain ⟨i, j, hij⟩ := hlabels
    exact hentries i j (hblock i j hij)
  have henergy_ne : matrixHilbertSchmidtEnergy S ≠ 0 := by
    intro hzero
    exact hS ((matrixHilbertSchmidtEnergy_eq_zero_iff S).1 hzero)
  have henergy_pos : 0 < matrixHilbertSchmidtEnergy S :=
    lt_of_le_of_ne (matrixHilbertSchmidtEnergy_nonneg S) henergy_ne.symm
  dsimp [S] at henergy_pos ⊢
  linarith

/-- Coordinate-wise global concavity of Gaussian-kernel log volume under every rank-one
positive-semidefinite metric update, for an arbitrary positive-definite background. -/
theorem rankOneSchurGaussian_logDet_concaveOn {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hC : C.PosDef) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun t => Real.log (rankOneSchurGaussianPath C a t).det) := by
  let S : ℝ := ∑ i, a i ^ 2
  let f : ℝ → ℝ := fun t =>
    Real.log (rankOneSchurExponentialPath C a t).det
  have hf : ConcaveOn ℝ (Set.Ici 0) f :=
    rankOneSchurExponential_logDet_concaveOn C a hC
  have hcomp : ConcaveOn ℝ (Set.Ici 0) (fun t => f (2 * t)) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy p q hp hq hpq
    have h := hf.2 (show 2 * x ∈ Set.Ici (0 : ℝ) by
        simpa only [Set.mem_Ici] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx)
      (show 2 * y ∈ Set.Ici (0 : ℝ) by
        simpa only [Set.mem_Ici] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hy)
      hp hq hpq
    convert! h using 1
    simp only [smul_eq_mul]
    ring
  have haffine : ConcaveOn ℝ (Set.Ici 0) (fun t => -2 * t * S) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy p q hp hq hpq
    simp only [smul_eq_mul]
    rw [show -2 * (p * x + q * y) * S =
        p * (-2 * x * S) + q * (-2 * y * S) by ring]
  have hsum : ConcaveOn ℝ (Set.Ici 0) (fun t => -2 * t * S + f (2 * t)) := by
    simpa only [Pi.add_apply] using! haffine.add hcomp
  apply hsum.congr
  intro t ht
  exact (rankOneSchurGaussian_logDet_eq_affine_add C a hC t ht).symm

/-- Packaged universal law: exact exponential-path curvature together with global Gaussian-path
concavity. -/
theorem rankOneSchurGaussian_universalLaw {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (rankOneSchurExponentialPath C a s).det)) t =
        -matrixHilbertSchmidtEnergy
          (matrixSelfCommutator
            (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
              (rankOneLabelDiagonal a))) / 2 ∧
      ConcaveOn ℝ (Set.Ici 0)
        (fun s => Real.log (rankOneSchurGaussianPath C a s).det) := by
  exact ⟨rankOneSchurExponential_logDet_secondDerivative_eq C a hC t ht,
    rankOneSchurGaussian_logDet_concaveOn C a hC⟩

/-- Packaged sharp law: both exact curvature identities, global Gaussian concavity, and the
complete equality classification. -/
theorem rankOneSchurGaussian_sharpUniversalLaw {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hC : C.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (rankOneSchurExponentialPath C a s).det)) t =
        -matrixHilbertSchmidtEnergy
          (matrixSelfCommutator
            (matrixSqrtSimilarity (rankOneSchurExponentialPath C a t)
              (rankOneLabelDiagonal a))) / 2 ∧
      deriv (deriv (fun s =>
        Real.log (rankOneSchurGaussianPath C a s).det)) t =
          -2 * matrixHilbertSchmidtEnergy
            (matrixSelfCommutator
              (matrixSqrtSimilarity (rankOneSchurExponentialPath C a (2 * t))
                (rankOneLabelDiagonal a))) ∧
      ConcaveOn ℝ (Set.Ici 0)
        (fun s => Real.log (rankOneSchurGaussianPath C a s).det) ∧
      (deriv (deriv (fun s =>
        Real.log (rankOneSchurGaussianPath C a s).det)) t = 0 ↔
          ∀ i j, a i ≠ a j → C i j = 0) := by
  exact ⟨rankOneSchurExponential_logDet_secondDerivative_eq C a hC t ht,
    rankOneSchurGaussian_logDet_secondDerivative_eq C a hC t ht,
    rankOneSchurGaussian_logDet_concaveOn C a hC,
    rankOneSchurGaussian_logDet_secondDerivative_eq_zero_iff_block C a hC t ht⟩

end

end GaloisForLFunctions.HilbertMetric
