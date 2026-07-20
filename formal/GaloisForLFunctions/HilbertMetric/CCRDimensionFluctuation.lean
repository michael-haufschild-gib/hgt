import GaloisForLFunctions.HilbertMetric.FanoCommutator

/-!
# CCR dimension--fluctuation law

For a finite commuting family `Aᵢ` with a rectangular CCR completion `Bᵢ`, the total leakage
variance has an exact dimension-sensitive sum-of-squares decomposition.  If `d` is the number
of modes, `E` is the compressed annihilation energy, `V` is the squared energy of the contracted
leakage, `C` is the mixed nonnormality energy, and `K` is the traceless leakage-tensor energy,
then

`d * (d + 1) * (d * E - V) = d ^ 2 * C + K`.

The right side is a literal sum of squares.  Thus `V ≤ d * E`; equality is equivalent to joint
normality of every mixed compression and pure-trace leakage.  At one mode the traceless tensor
vanishes and the identity reduces to the self-commutator Fano law.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {I n m : Type*} [Fintype I] [DecidableEq I]
  [Fintype n] [DecidableEq n] [Fintype m]

/-- Squared coordinate Hilbert--Schmidt energy of a rectangular real matrix. -/
def rectangularMatrixHilbertSchmidtEnergy (A : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

omit [DecidableEq n] in
/-- Rectangular coordinate energy is the transpose-product trace. -/
theorem rectangularMatrixHilbertSchmidtEnergy_eq_trace_transpose_mul
    (A : Matrix m n ℝ) :
    rectangularMatrixHilbertSchmidtEnergy A = Matrix.trace (A.transpose * A) := by
  simp only [rectangularMatrixHilbertSchmidtEnergy, Matrix.trace]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change A j i ^ 2 = A j i * A j i
  ring

omit [DecidableEq n] in
theorem rectangularMatrixHilbertSchmidtEnergy_nonneg (A : Matrix m n ℝ) :
    0 ≤ rectangularMatrixHilbertSchmidtEnergy A := by
  unfold rectangularMatrixHilbertSchmidtEnergy
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _

omit [DecidableEq n] in
theorem rectangularMatrixHilbertSchmidtEnergy_eq_zero_iff (A : Matrix m n ℝ) :
    rectangularMatrixHilbertSchmidtEnergy A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have hi : (∑ j, A i j ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg (A i j)).mp h i (Finset.mem_univ i)
    have hij : A i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (A i j)).mp
        hi j (Finset.mem_univ j)
    simpa using (sq_eq_zero_iff.mp hij)
  · rintro rfl
    simp [rectangularMatrixHilbertSchmidtEnergy]

omit [DecidableEq n] in
theorem rectangularMatrixHilbertSchmidtEnergy_square (A : Matrix n n ℝ) :
    rectangularMatrixHilbertSchmidtEnergy A = matrixHilbertSchmidtEnergy A := rfl

/-- Column energy of the compressed annihilation tuple. -/
def ccrColumnEnergyMatrix (A : I → Matrix n n ℝ) : Matrix n n ℝ :=
  ∑ i, (A i).transpose * A i

/-- Row energy of the compressed annihilation tuple. -/
def ccrRowEnergyMatrix (A : I → Matrix n n ℝ) : Matrix n n ℝ :=
  ∑ i, A i * (A i).transpose

/-- Total compressed annihilation energy, interpreted as mean number in the Fock application. -/
def ccrMeanEnergy (A : I → Matrix n n ℝ) : ℝ :=
  ∑ i, matrixHilbertSchmidtEnergy (A i)

/-- Pair-product energy of a commuting annihilation tuple. -/
def ccrProductEnergy (A : I → Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, matrixHilbertSchmidtEnergy (A i * A j)

/-- Contraction of the completion leakage tensor. -/
def ccrLeakageTrace (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) :
    Matrix m n ℝ :=
  ∑ i, (B i).transpose * A i

/-- Squared leakage contraction, interpreted as total number variance in the Fock application. -/
def ccrNumberVariance (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) : ℝ :=
  rectangularMatrixHilbertSchmidtEnergy (ccrLeakageTrace A B)

/-- Collective mixed nonnormality.  For a commuting tuple this equals the sum of the squared
energies of all mixed commutators `Aᵢ Aⱼᵀ - Aⱼᵀ Aᵢ`. -/
def ccrMixedCommutatorEnergy (A : I → Matrix n n ℝ) : ℝ :=
  matrixHilbertSchmidtEnergy (ccrColumnEnergyMatrix A - ccrRowEnergyMatrix A)

/-- One mixed nonnormality commutator. -/
def ccrMixedCommutator (A : I → Matrix n n ℝ) (i j : I) : Matrix n n ℝ :=
  A i * (A j).transpose - (A j).transpose * A i

/-- Literal sum of the Hilbert--Schmidt energies of every mixed commutator. -/
def ccrPairwiseMixedCommutatorEnergy (A : I → Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, matrixHilbertSchmidtEnergy (ccrMixedCommutator A i j)

/-- Full (uncontracted) completion leakage energy. -/
def ccrFullLeakageEnergy (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) : ℝ :=
  ∑ i, ∑ j, rectangularMatrixHilbertSchmidtEnergy ((B i).transpose * A j)

/-- The scaled traceless part of the matrix-valued leakage tensor `Bᵢᵀ Aⱼ`. -/
def ccrScaledTracelessLeakage (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (i j : I) : Matrix m n ℝ :=
  (Fintype.card I : ℝ) • ((B i).transpose * A j) -
    if i = j then ccrLeakageTrace A B else 0

/-- Squared Hilbert--Schmidt energy of the scaled traceless leakage tensor. -/
def ccrScaledTracelessLeakageEnergy
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) : ℝ :=
  ∑ i, ∑ j, rectangularMatrixHilbertSchmidtEnergy
    (ccrScaledTracelessLeakage A B i j)

/-- The compressed annihilators commute. -/
def IsCommutingCCRCompression (A : I → Matrix n n ℝ) : Prop :=
  ∀ i j, A i * A j = A j * A i

/-- Exact upper-left block of the canonical commutation relations. -/
def IsCCRCompletion (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) : Prop :=
  ∀ i j,
    B i * (B j).transpose =
      (if i = j then 1 else 0) + (A j).transpose * A i - A i * (A j).transpose

omit [DecidableEq I] [DecidableEq n] in
theorem ccrColumnEnergyMatrix_transpose (A : I → Matrix n n ℝ) :
    (ccrColumnEnergyMatrix A).transpose = ccrColumnEnergyMatrix A := by
  classical
  simp [ccrColumnEnergyMatrix, Matrix.transpose_sum, Matrix.transpose_mul]

omit [DecidableEq I] [DecidableEq n] in
theorem ccrRowEnergyMatrix_transpose (A : I → Matrix n n ℝ) :
    (ccrRowEnergyMatrix A).transpose = ccrRowEnergyMatrix A := by
  classical
  simp [ccrRowEnergyMatrix, Matrix.transpose_sum, Matrix.transpose_mul]

omit [Fintype I] in
private theorem trace_ccr_variance_term
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B)
    (i j : I) :
    Matrix.trace ((A i).transpose * (B i * (B j).transpose) * A j) =
      (if i = j then matrixHilbertSchmidtEnergy (A i) else 0) +
        matrixHilbertSchmidtEnergy (A i * A j) -
          Matrix.trace (((A i).transpose * A i) * ((A j).transpose * A j)) := by
  rw [hccr i j]
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul,
    matrixHilbertSchmidtEnergy_eq_trace_transpose_mul]
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    have hm :
        (A i).transpose *
            (1 + (A i).transpose * A i - A i * (A i).transpose) * A i =
          (A i).transpose * A i +
              (A i * A i).transpose * (A i * A i) -
            ((A i).transpose * A i) * ((A i).transpose * A i) := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    rw [hm, Matrix.trace_sub, Matrix.trace_add]
  · simp only [if_neg hij, zero_add]
    have ht : (A i).transpose * (A j).transpose =
        (A j).transpose * (A i).transpose := by
      simpa only [Matrix.transpose_mul] using
        congrArg Matrix.transpose (hcomm i j).symm
    have hm :
        (A i).transpose *
            ((A j).transpose * A i - A i * (A j).transpose) * A j =
          (A i * A j).transpose * (A i * A j) -
            ((A i).transpose * A i) * ((A j).transpose * A j) := by
      rw [Matrix.transpose_mul]
      calc
        (A i).transpose *
            ((A j).transpose * A i - A i * (A j).transpose) * A j =
            ((A i).transpose * (A j).transpose) * (A i * A j) -
              ((A i).transpose * A i) * ((A j).transpose * A j) := by
                noncomm_ring
        _ = (A j).transpose * (A i).transpose * (A i * A j) -
              ((A i).transpose * A i) * ((A j).transpose * A j) := by rw [ht]
    rw [hm, Matrix.trace_sub]

omit [DecidableEq I] [Fintype n] [DecidableEq n] in
private theorem sum_matrix_mul
    (X : I → Matrix n m ℝ) (Y : Matrix m n ℝ) :
    (∑ i, X i) * Y = ∑ i, X i * Y := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.sum_apply]
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

omit [DecidableEq I] [Fintype n] [DecidableEq n] in
private theorem matrix_mul_sum
    (X : Matrix n m ℝ) (Y : I → Matrix m n ℝ) :
    X * (∑ i, Y i) = ∑ i, X * Y i := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.sum_apply]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- The CCR contraction reproduces the additive Slater variance formula. -/
theorem ccrNumberVariance_eq_mean_add_product_sub_columnSq
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B) :
    ccrNumberVariance A B =
      ccrMeanEnergy A + ccrProductEnergy A -
        Matrix.trace (ccrColumnEnergyMatrix A * ccrColumnEnergyMatrix A) := by
  classical
  rw [ccrNumberVariance, rectangularMatrixHilbertSchmidtEnergy_eq_trace_transpose_mul]
  have hmul :
      (∑ i, (A i).transpose * B i) * (∑ j, (B j).transpose * A j) =
        ∑ i, ∑ j, (A i).transpose * (B i * (B j).transpose) * A j := by
    rw [sum_matrix_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [matrix_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.mul_assoc]
  calc
    Matrix.trace ((ccrLeakageTrace A B).transpose * ccrLeakageTrace A B) =
        ∑ i, ∑ j,
          Matrix.trace ((A i).transpose * (B i * (B j).transpose) * A j) := by
            simp only [ccrLeakageTrace, Matrix.transpose_sum, Matrix.transpose_mul,
              Matrix.transpose_transpose]
            rw [hmul]
            simp only [Matrix.trace_sum]
    _ = ∑ i, ∑ j,
        ((if i = j then matrixHilbertSchmidtEnergy (A i) else 0) +
          matrixHilbertSchmidtEnergy (A i * A j) -
            Matrix.trace (((A i).transpose * A i) * ((A j).transpose * A j))) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact trace_ccr_variance_term A B hcomm hccr i j
    _ = ccrMeanEnergy A + ccrProductEnergy A -
        Matrix.trace (ccrColumnEnergyMatrix A * ccrColumnEnergyMatrix A) := by
          unfold ccrMeanEnergy ccrProductEnergy ccrColumnEnergyMatrix
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
          simp
          rw [Finset.sum_comm]

omit [Fintype I] [DecidableEq I] [DecidableEq n] in
private theorem productEnergy_term_eq_column_row_term
    (A : I → Matrix n n ℝ) (i j : I) :
    matrixHilbertSchmidtEnergy (A i * A j) =
      Matrix.trace (((A i).transpose * A i) * (A j * (A j).transpose)) := by
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul, Matrix.transpose_mul]
  calc
    Matrix.trace ((A j).transpose * (A i).transpose * (A i * A j)) =
        Matrix.trace ((A i * A j) * ((A j).transpose * (A i).transpose)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((A i * (A j * (A j).transpose)) * (A i).transpose) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace ((A i).transpose * (A i * (A j * (A j).transpose))) :=
      (Matrix.trace_mul_comm _ _).symm
    _ = Matrix.trace (((A i).transpose * A i) * (A j * (A j).transpose)) := by
      congr 1
      noncomm_ring

omit [DecidableEq I] [DecidableEq n] in
theorem ccrProductEnergy_eq_trace_column_mul_row (A : I → Matrix n n ℝ)
    (hcomm : IsCommutingCCRCompression A) :
    ccrProductEnergy A =
      Matrix.trace (ccrColumnEnergyMatrix A * ccrRowEnergyMatrix A) := by
  classical
  unfold ccrProductEnergy ccrColumnEnergyMatrix ccrRowEnergyMatrix
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    matrixHilbertSchmidtEnergy (A i * A j) =
        matrixHilbertSchmidtEnergy (A j * A i) := by rw [hcomm i j]
    _ = Matrix.trace (((A j).transpose * A j) * (A i * (A i).transpose)) :=
      productEnergy_term_eq_column_row_term A j i

omit [Fintype I] [DecidableEq I] [DecidableEq n] in
private theorem mixedLeftEnergy_term (A : I → Matrix n n ℝ) (i j : I) :
    matrixHilbertSchmidtEnergy (A i * (A j).transpose) =
      Matrix.trace (((A j).transpose * A j) * ((A i).transpose * A i)) := by
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  calc
    Matrix.trace ((A j * (A i).transpose) * (A i * (A j).transpose)) =
        Matrix.trace (A j * ((A i).transpose * A i) * (A j).transpose) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace ((A j).transpose * A j * ((A i).transpose * A i)) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (((A j).transpose * A j) * ((A i).transpose * A i)) := by
      congr 1

omit [Fintype I] [DecidableEq I] [DecidableEq n] in
private theorem mixedRightEnergy_term (A : I → Matrix n n ℝ) (i j : I) :
    matrixHilbertSchmidtEnergy ((A j).transpose * A i) =
      Matrix.trace ((A j * (A j).transpose) * (A i * (A i).transpose)) := by
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  calc
    Matrix.trace (((A i).transpose * A j) * ((A j).transpose * A i)) =
        Matrix.trace ((A i).transpose * (A j * (A j).transpose) * A i) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (A i * (A i).transpose * (A j * (A j).transpose)) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace ((A j * (A j).transpose) * (A i * (A i).transpose)) :=
      Matrix.trace_mul_comm _ _

private def ccrMixedCrossTrace (A : I → Matrix n n ℝ) (i j : I) : ℝ :=
  Matrix.trace ((A j * (A i).transpose) * ((A j).transpose * A i))

omit [Fintype I] [DecidableEq I] [DecidableEq n] in
private theorem mixedReverseCrossTrace_eq (A : I → Matrix n n ℝ) (i j : I) :
    Matrix.trace (((A i).transpose * A j) * (A i * (A j).transpose)) =
      ccrMixedCrossTrace A i j := by
  unfold ccrMixedCrossTrace
  rw [← Matrix.trace_transpose
    ((A j * (A i).transpose) * ((A j).transpose * A i))]
  congr 1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

omit [Fintype I] [DecidableEq I] [DecidableEq n] in
private theorem mixedCrossTrace_swap_eq_product
    (A : I → Matrix n n ℝ) (hcomm : IsCommutingCCRCompression A) (i j : I) :
    ccrMixedCrossTrace A j i = matrixHilbertSchmidtEnergy (A i * A j) := by
  unfold ccrMixedCrossTrace
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul, Matrix.transpose_mul]
  calc
    Matrix.trace ((A i * (A j).transpose) * ((A i).transpose * A j)) =
        Matrix.trace (A i * ((A j).transpose * (A i).transpose) * A j) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (A j * A i * ((A j).transpose * (A i).transpose)) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace ((A i * A j) * ((A j).transpose * (A i).transpose)) := by
      rw [hcomm j i]
    _ = Matrix.trace (((A j).transpose * (A i).transpose) * (A i * A j)) :=
      (Matrix.trace_mul_comm _ _).symm

omit [Fintype I] [DecidableEq I] [DecidableEq n] in
private theorem mixedCommutatorEnergy_term
    (A : I → Matrix n n ℝ) (i j : I) :
    matrixHilbertSchmidtEnergy (ccrMixedCommutator A i j) =
      matrixHilbertSchmidtEnergy (A i * (A j).transpose) +
        matrixHilbertSchmidtEnergy ((A j).transpose * A i) -
          2 * ccrMixedCrossTrace A i j := by
  unfold ccrMixedCommutator ccrMixedCrossTrace
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul, Matrix.transpose_sub,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.trace_sub]
  rw [← matrixHilbertSchmidtEnergy_eq_trace_transpose_mul,
    ← matrixHilbertSchmidtEnergy_eq_trace_transpose_mul]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [mixedReverseCrossTrace_eq]
  unfold ccrMixedCrossTrace
  ring

omit [DecidableEq I] [DecidableEq n] in
/-- For a commuting compression, collective row--column nonnormality is literally the sum of all
mixed commutator squares. -/
theorem ccrPairwiseMixedCommutatorEnergy_eq
    (A : I → Matrix n n ℝ) (hcomm : IsCommutingCCRCompression A) :
    ccrPairwiseMixedCommutatorEnergy A = ccrMixedCommutatorEnergy A := by
  classical
  have hleft :
      (∑ i, ∑ j, matrixHilbertSchmidtEnergy (A i * (A j).transpose)) =
        Matrix.trace (ccrColumnEnergyMatrix A * ccrColumnEnergyMatrix A) := by
    unfold ccrColumnEnergyMatrix
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    calc
      matrixHilbertSchmidtEnergy (A j * (A i).transpose) =
          Matrix.trace (((A i).transpose * A i) * ((A j).transpose * A j)) :=
        mixedLeftEnergy_term A j i
      _ = Matrix.trace (((A j).transpose * A j) * ((A i).transpose * A i)) :=
        Matrix.trace_mul_comm _ _
  have hright :
      (∑ i, ∑ j, matrixHilbertSchmidtEnergy ((A j).transpose * A i)) =
        Matrix.trace (ccrRowEnergyMatrix A * ccrRowEnergyMatrix A) := by
    unfold ccrRowEnergyMatrix
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    calc
      matrixHilbertSchmidtEnergy ((A i).transpose * A j) =
          Matrix.trace ((A i * (A i).transpose) * (A j * (A j).transpose)) :=
        mixedRightEnergy_term A j i
      _ = Matrix.trace ((A j * (A j).transpose) * (A i * (A i).transpose)) :=
        Matrix.trace_mul_comm _ _
  have hcross :
      (∑ i, ∑ j, ccrMixedCrossTrace A i j) = ccrProductEnergy A := by
    calc
      (∑ i, ∑ j, ccrMixedCrossTrace A i j) =
          ∑ i, ∑ j, ccrMixedCrossTrace A j i := by rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, matrixHilbertSchmidtEnergy (A i * A j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact mixedCrossTrace_swap_eq_product A hcomm i j
      _ = ccrProductEnergy A := rfl
  have hcross2 :
      (∑ i, ∑ j, 2 * ccrMixedCrossTrace A i j) = 2 * ccrProductEnergy A := by
    simp_rw [← Finset.mul_sum]
    rw [hcross]
  unfold ccrPairwiseMixedCommutatorEnergy
  simp_rw [mixedCommutatorEnergy_term]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hleft, hright, hcross2]
  rw [ccrProductEnergy_eq_trace_column_mul_row A hcomm]
  unfold ccrMixedCommutatorEnergy
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul, Matrix.transpose_sub,
    ccrColumnEnergyMatrix_transpose, ccrRowEnergyMatrix_transpose]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.trace_sub]
  rw [Matrix.trace_mul_comm (ccrRowEnergyMatrix A) (ccrColumnEnergyMatrix A)]
  ring

omit [DecidableEq I] [DecidableEq n] in
/-- Collective mixed nonnormality expands into the row/column trace polynomial. -/
theorem ccrMixedCommutatorEnergy_eq_trace_polynomial (A : I → Matrix n n ℝ) :
    ccrMixedCommutatorEnergy A =
      Matrix.trace (ccrColumnEnergyMatrix A * ccrColumnEnergyMatrix A) +
        Matrix.trace (ccrRowEnergyMatrix A * ccrRowEnergyMatrix A) -
          2 * Matrix.trace (ccrColumnEnergyMatrix A * ccrRowEnergyMatrix A) := by
  unfold ccrMixedCommutatorEnergy
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul, Matrix.transpose_sub,
    ccrColumnEnergyMatrix_transpose, ccrRowEnergyMatrix_transpose]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.trace_sub]
  rw [Matrix.trace_mul_comm (ccrRowEnergyMatrix A) (ccrColumnEnergyMatrix A)]
  ring

omit [Fintype I] in
private theorem fullLeakage_term
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hccr : IsCCRCompletion A B) (i j : I) :
    rectangularMatrixHilbertSchmidtEnergy ((B i).transpose * A j) =
      matrixHilbertSchmidtEnergy (A j) + matrixHilbertSchmidtEnergy (A i * A j) -
        Matrix.trace ((A i * (A i).transpose) * (A j * (A j).transpose)) := by
  rw [rectangularMatrixHilbertSchmidtEnergy_eq_trace_transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  have hregroup :
      ((A j).transpose * B i) * ((B i).transpose * A j) =
        (A j).transpose * (B i * (B i).transpose) * A j := by
    simp only [Matrix.mul_assoc]
  rw [hregroup, hccr i i]
  simp only [if_pos, matrixHilbertSchmidtEnergy_eq_trace_transpose_mul]
  have hm :
      (A j).transpose *
          (1 + (A i).transpose * A i - A i * (A i).transpose) * A j =
        (A j).transpose * A j +
            (A i * A j).transpose * (A i * A j) -
          (A j).transpose * (A i * (A i).transpose) * A j := by
    rw [Matrix.transpose_mul]
    noncomm_ring
  rw [hm, Matrix.trace_sub, Matrix.trace_add]
  congr 1
  calc
    Matrix.trace ((A j).transpose * (A i * (A i).transpose) * A j) =
        Matrix.trace (A j * (A j).transpose * (A i * (A i).transpose)) := by
      rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace ((A i * (A i).transpose) * (A j * (A j).transpose)) :=
      Matrix.trace_mul_comm _ _

/-- Full leakage energy is determined by mean, product, and row energy. -/
theorem ccrFullLeakageEnergy_eq
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hccr : IsCCRCompletion A B) :
    ccrFullLeakageEnergy A B =
      (Fintype.card I : ℝ) * ccrMeanEnergy A + ccrProductEnergy A -
        Matrix.trace (ccrRowEnergyMatrix A * ccrRowEnergyMatrix A) := by
  classical
  unfold ccrFullLeakageEnergy
  simp_rw [fullLeakage_term A B hccr]
  unfold ccrMeanEnergy ccrProductEnergy ccrRowEnergyMatrix
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
  simp
  rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  rw [Finset.sum_comm]

/-- The full leakage tensor equals `(d+1)E-V-C`. -/
theorem ccrFullLeakageEnergy_eq_mean_variance_commutator
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B) :
    ccrFullLeakageEnergy A B =
      ((Fintype.card I : ℝ) + 1) * ccrMeanEnergy A -
        ccrNumberVariance A B - ccrMixedCommutatorEnergy A := by
  rw [ccrFullLeakageEnergy_eq A B hccr,
    ccrNumberVariance_eq_mean_add_product_sub_columnSq A B hcomm hccr,
    ccrMixedCommutatorEnergy_eq_trace_polynomial]
  rw [ccrProductEnergy_eq_trace_column_mul_row A hcomm]
  ring

private theorem scalar_scaled_traceless
    (z : I → I → ℝ) :
    (∑ i, ∑ j,
      ((Fintype.card I : ℝ) * z i j -
        if i = j then (∑ k, z k k) else 0) ^ 2) =
      (Fintype.card I : ℝ) ^ 2 * (∑ i, ∑ j, (z i j) ^ 2) -
        (Fintype.card I : ℝ) * (∑ k, z k k) ^ 2 := by
  have hcross :
      (∑ i, 2 * (Fintype.card I : ℝ) * z i i * (∑ k, z k k)) =
        2 * (Fintype.card I : ℝ) * (∑ k, z k k) ^ 2 := by
    calc
      (∑ i, 2 * (Fintype.card I : ℝ) * z i i * (∑ k, z k k)) =
          (∑ i, 2 * (Fintype.card I : ℝ) * z i i) * (∑ k, z k k) := by
            rw [Finset.sum_mul]
      _ = (2 * (Fintype.card I : ℝ) * (∑ i, z i i)) * (∑ k, z k k) := by
            rw [← Finset.mul_sum]
      _ = 2 * (Fintype.card I : ℝ) * (∑ k, z k k) ^ 2 := by ring
  have hquad :
      (∑ i, ∑ j, (Fintype.card I : ℝ) ^ 2 * (z i j) ^ 2) =
        (Fintype.card I : ℝ) ^ 2 * (∑ i, ∑ j, (z i j) ^ 2) := by
    calc
      (∑ i, ∑ j, (Fintype.card I : ℝ) ^ 2 * (z i j) ^ 2) =
          ∑ i, (Fintype.card I : ℝ) ^ 2 * (∑ j, (z i j) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = (Fintype.card I : ℝ) ^ 2 * (∑ i, ∑ j, (z i j) ^ 2) := by
            rw [Finset.mul_sum]
  calc
    (∑ i, ∑ j,
      ((Fintype.card I : ℝ) * z i j -
        if i = j then (∑ k, z k k) else 0) ^ 2) =
        ∑ i, ∑ j,
          ((Fintype.card I : ℝ) ^ 2 * (z i j) ^ 2 -
            2 * (Fintype.card I : ℝ) * z i j *
              (if i = j then (∑ k, z k k) else 0) +
            (if i = j then (∑ k, z k k) else 0) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
    _ = (Fintype.card I : ℝ) ^ 2 * (∑ i, ∑ j, (z i j) ^ 2) -
        2 * (Fintype.card I : ℝ) * (∑ k, z k k) ^ 2 +
        (Fintype.card I : ℝ) * (∑ k, z k k) ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          simp
          rw [hcross, hquad]
    _ = (Fintype.card I : ℝ) ^ 2 * (∑ i, ∑ j, (z i j) ^ 2) -
        (Fintype.card I : ℝ) * (∑ k, z k k) ^ 2 := by ring

omit [DecidableEq I] [DecidableEq n] in
private theorem sum_four_comm (f : I → I → m → n → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) =
      ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  calc
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) =
        ∑ i, ∑ a, ∑ j, ∑ b, f i j a b := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, f i j a b := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, f i j a b := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm

omit [DecidableEq n] in
/-- Orthogonal trace/traceless decomposition of the completion leakage tensor. -/
theorem ccrScaledTracelessLeakageEnergy_eq
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) :
    ccrScaledTracelessLeakageEnergy A B =
      (Fintype.card I : ℝ) ^ 2 * ccrFullLeakageEnergy A B -
        (Fintype.card I : ℝ) * ccrNumberVariance A B := by
  classical
  unfold ccrScaledTracelessLeakageEnergy ccrScaledTracelessLeakage
    ccrFullLeakageEnergy ccrNumberVariance ccrLeakageTrace
    rectangularMatrixHilbertSchmidtEnergy
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [sum_four_comm]
  calc
    (∑ a, ∑ b, ∑ i, ∑ j,
      ((Fintype.card I : ℝ) * (((B i).transpose * A j) a b) -
        (if i = j then (∑ k, (B k).transpose * A k) else 0) a b) ^ 2) =
      ∑ a, ∑ b, ∑ i, ∑ j,
        ((Fintype.card I : ℝ) * (((B i).transpose * A j) a b) -
          if i = j then (∑ k, ((B k).transpose * A k) a b) else 0) ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            by_cases hij : i = j
            · subst j
              simp only [if_pos]
              rw [Matrix.sum_apply a b Finset.univ
                (fun k => (B k).transpose * A k)]
            · simp [hij]
    _ = ∑ a, ∑ b,
        ((Fintype.card I : ℝ) ^ 2 *
            (∑ i, ∑ j, (((B i).transpose * A j) a b) ^ 2) -
          (Fintype.card I : ℝ) *
            (∑ k, ((B k).transpose * A k) a b) ^ 2) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          exact scalar_scaled_traceless
            (z := fun i j => ((B i).transpose * A j) a b)
    _ = (Fintype.card I : ℝ) ^ 2 *
          (∑ a, ∑ b, ∑ i, ∑ j, (((B i).transpose * A j) a b) ^ 2) -
        (Fintype.card I : ℝ) *
          (∑ a, ∑ b, (∑ k, ((B k).transpose * A k) a b) ^ 2) := by
            simp only [Finset.sum_sub_distrib]
            simp_rw [← Finset.mul_sum]
    _ = (Fintype.card I : ℝ) ^ 2 *
          (∑ i, ∑ j, ∑ a, ∑ b, (((B i).transpose * A j) a b) ^ 2) -
        (Fintype.card I : ℝ) *
          (∑ a, ∑ b, (∑ k, ((B k).transpose * A k) a b) ^ 2) := by
            rw [sum_four_comm]

omit [DecidableEq I] [DecidableEq n] in
theorem ccrMixedCommutatorEnergy_nonneg (A : I → Matrix n n ℝ) :
    0 ≤ ccrMixedCommutatorEnergy A :=
  matrixHilbertSchmidtEnergy_nonneg _

omit [DecidableEq n] in
theorem ccrScaledTracelessLeakageEnergy_nonneg
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) :
    0 ≤ ccrScaledTracelessLeakageEnergy A B := by
  unfold ccrScaledTracelessLeakageEnergy
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    rectangularMatrixHilbertSchmidtEnergy_nonneg _

/-- **CCR dimension--fluctuation identity.**  The dimension-scaled gap between total compressed
energy and contracted leakage variance is exactly mixed nonnormality plus traceless leakage. -/
theorem ccr_dimension_fluctuation_identity
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B) :
    (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) + 1) *
        ((Fintype.card I : ℝ) * ccrMeanEnergy A - ccrNumberVariance A B) =
      (Fintype.card I : ℝ) ^ 2 * ccrMixedCommutatorEnergy A +
        ccrScaledTracelessLeakageEnergy A B := by
  rw [ccrScaledTracelessLeakageEnergy_eq,
    ccrFullLeakageEnergy_eq_mean_variance_commutator A B hcomm hccr]
  ring

/-- Literal mixed-commutator form of the dimension--fluctuation identity. -/
theorem ccr_dimension_fluctuation_pairwise_identity
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B) :
    (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) + 1) *
        ((Fintype.card I : ℝ) * ccrMeanEnergy A - ccrNumberVariance A B) =
      (Fintype.card I : ℝ) ^ 2 * ccrPairwiseMixedCommutatorEnergy A +
        ccrScaledTracelessLeakageEnergy A B := by
  rw [ccrPairwiseMixedCommutatorEnergy_eq A hcomm]
  exact ccr_dimension_fluctuation_identity A B hcomm hccr

/-- The total number variance of a `d`-mode finite CCR compression is at most `d` times its mean
energy. -/
theorem ccr_numberVariance_le_card_mul_mean
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B)
    (hI : 0 < Fintype.card I) :
    ccrNumberVariance A B ≤ (Fintype.card I : ℝ) * ccrMeanEnergy A := by
  have hid := ccr_dimension_fluctuation_identity A B hcomm hccr
  have hC := ccrMixedCommutatorEnergy_nonneg A
  have hK := ccrScaledTracelessLeakageEnergy_nonneg A B
  have hd : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hI
  have hd1 : 0 < (Fintype.card I : ℝ) + 1 := by linarith
  nlinarith [mul_pos hd hd1]

/-- Saturation of the dimension--fluctuation bound is equivalent to simultaneous vanishing of
mixed nonnormality and traceless leakage. -/
theorem ccr_numberVariance_eq_card_mul_mean_iff
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B)
    (hI : 0 < Fintype.card I) :
    ccrNumberVariance A B = (Fintype.card I : ℝ) * ccrMeanEnergy A ↔
      ccrMixedCommutatorEnergy A = 0 ∧
        ccrScaledTracelessLeakageEnergy A B = 0 := by
  have hid := ccr_dimension_fluctuation_identity A B hcomm hccr
  have hC := ccrMixedCommutatorEnergy_nonneg A
  have hK := ccrScaledTracelessLeakageEnergy_nonneg A B
  have hd : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hI
  constructor
  · intro h
    rw [h, sub_self, mul_zero] at hid
    constructor <;> nlinarith [sq_pos_of_pos hd]
  · rintro ⟨hC0, hK0⟩
    rw [hC0, hK0, mul_zero, add_zero] at hid
    have hd1 : 0 < (Fintype.card I : ℝ) + 1 := by linarith
    nlinarith [mul_pos hd hd1]

/-- Equality criterion with the literal pairwise mixed-commutator energy. -/
theorem ccr_numberVariance_eq_card_mul_mean_pairwise_iff
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B)
    (hI : 0 < Fintype.card I) :
    ccrNumberVariance A B = (Fintype.card I : ℝ) * ccrMeanEnergy A ↔
      ccrPairwiseMixedCommutatorEnergy A = 0 ∧
        ccrScaledTracelessLeakageEnergy A B = 0 := by
  rw [ccr_numberVariance_eq_card_mul_mean_iff A B hcomm hccr hI,
    ccrPairwiseMixedCommutatorEnergy_eq A hcomm]

/-- At one mode the traceless leakage tensor vanishes, so the universal law reduces exactly to
the self-commutator Fano identity. -/
theorem oneMode_ccr_two_mul_mean_sub_variance_eq_pairwiseCommutator
    (A : Unit → Matrix n n ℝ) (B : Unit → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B) :
    2 * (ccrMeanEnergy A - ccrNumberVariance A B) =
      ccrPairwiseMixedCommutatorEnergy A := by
  have h := ccr_dimension_fluctuation_pairwise_identity A B hcomm hccr
  have hK : ccrScaledTracelessLeakageEnergy A B = 0 := by
    unfold ccrScaledTracelessLeakageEnergy ccrScaledTracelessLeakage ccrLeakageTrace
      rectangularMatrixHilbertSchmidtEnergy
    simp
  rw [hK, add_zero] at h
  norm_num at h ⊢
  nlinarith

omit [DecidableEq I] [DecidableEq n] in
/-- Zero pairwise mixed energy is exactly literal vanishing of every mixed commutator. -/
theorem ccrPairwiseMixedCommutatorEnergy_eq_zero_iff (A : I → Matrix n n ℝ) :
    ccrPairwiseMixedCommutatorEnergy A = 0 ↔
      ∀ i j, ccrMixedCommutator A i j = 0 := by
  unfold ccrPairwiseMixedCommutatorEnergy
  constructor
  · intro h i j
    have hi : (∑ j, matrixHilbertSchmidtEnergy (ccrMixedCommutator A i j)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => matrixHilbertSchmidtEnergy_nonneg _).mp
          h i (Finset.mem_univ i)
    have hij : matrixHilbertSchmidtEnergy (ccrMixedCommutator A i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        matrixHilbertSchmidtEnergy_nonneg _).mp hi j (Finset.mem_univ j)
    exact (matrixHilbertSchmidtEnergy_eq_zero_iff _).mp hij
  · intro h
    simp [h, matrixHilbertSchmidtEnergy]

omit [DecidableEq I] [DecidableEq n] in
/-- Zero collective mixed energy means literal vanishing of the row--column commutator tensor. -/
theorem ccrMixedCommutatorEnergy_eq_zero_iff (A : I → Matrix n n ℝ) :
    ccrMixedCommutatorEnergy A = 0 ↔
      ccrColumnEnergyMatrix A = ccrRowEnergyMatrix A := by
  unfold ccrMixedCommutatorEnergy
  rw [matrixHilbertSchmidtEnergy_eq_zero_iff]
  constructor <;> intro h
  · exact sub_eq_zero.mp h
  · exact sub_eq_zero.mpr h

omit [DecidableEq n] in
/-- Zero traceless leakage energy is exactly the pure-trace tensor condition. -/
theorem ccrScaledTracelessLeakageEnergy_eq_zero_iff
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ) :
    ccrScaledTracelessLeakageEnergy A B = 0 ↔
      ∀ i j, ccrScaledTracelessLeakage A B i j = 0 := by
  unfold ccrScaledTracelessLeakageEnergy
  constructor
  · intro h i j
    have hi : (∑ j, rectangularMatrixHilbertSchmidtEnergy
        (ccrScaledTracelessLeakage A B i j)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => rectangularMatrixHilbertSchmidtEnergy_nonneg _).mp
          h i (Finset.mem_univ i)
    have hij : rectangularMatrixHilbertSchmidtEnergy
        (ccrScaledTracelessLeakage A B i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        rectangularMatrixHilbertSchmidtEnergy_nonneg _).mp hi j (Finset.mem_univ j)
    exact (rectangularMatrixHilbertSchmidtEnergy_eq_zero_iff _).mp hij
  · intro h
    simp [h, rectangularMatrixHilbertSchmidtEnergy]

/-- Literal rigidity classification at equality in the dimension--fluctuation bound. -/
theorem ccr_numberVariance_eq_card_mul_mean_literal_iff
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B)
    (hI : 0 < Fintype.card I) :
    ccrNumberVariance A B = (Fintype.card I : ℝ) * ccrMeanEnergy A ↔
      (∀ i j, ccrMixedCommutator A i j = 0) ∧
        ∀ i j, ccrScaledTracelessLeakage A B i j = 0 := by
  rw [ccr_numberVariance_eq_card_mul_mean_pairwise_iff A B hcomm hccr hI,
    ccrPairwiseMixedCommutatorEnergy_eq_zero_iff,
    ccrScaledTracelessLeakageEnergy_eq_zero_iff]

end

end GaloisForLFunctions.HilbertMetric
