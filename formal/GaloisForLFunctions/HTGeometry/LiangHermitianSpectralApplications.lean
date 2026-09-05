import GaloisForLFunctions.HTGeometry.LiangScalarCurvatureAlgebra
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum
import GaloisForLFunctions.HTGeometry.SpectralEnsembleEigenvalueBound
import Mathlib.Analysis.Matrix.PosDef

/-!
# Liang curvature identities in spectral form

Recasts scalar-curvature identities as finite spectral statements. Results include the cubic
commutator as a nonnegative pair-difference energy on positive spectra, the full symmetric
3-tensor repeated-index lower bound, applications to Hermitian matrices and spectral ensembles,
and positivity of the parallel hypersurface Jacobian factors.
-/

open scoped BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Liang

variable {ι : Type*} [Fintype ι]

def curvatureCommutator (κ : ι → ℝ) : ℝ :=
  sigmaOne κ * (∑ i, κ i ^ 3) - (∑ i, κ i ^ 2) ^ 2

def pairDifferenceEnergy (κ : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, κ i * κ j * (κ i - κ j) ^ 2

theorem double_sum_mul (f g : ι → ℝ) :
    (∑ i, ∑ j, f i * g j) = (∑ i, f i) * ∑ j, g j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

theorem curvatureCommutator_eq_pairDifferenceEnergy (κ : ι → ℝ) :
    curvatureCommutator κ = pairDifferenceEnergy κ := by
  have hexpand :
      (∑ i, ∑ j, κ i * κ j * (κ i - κ j) ^ 2) =
        ∑ i, ∑ j,
          ((κ i ^ 3) * κ j + κ i * (κ j ^ 3) - (2 * κ i ^ 2) * κ j ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hfirst : (∑ i, ∑ j, (κ i ^ 3) * κ j) =
      (∑ i, κ i ^ 3) * sigmaOne κ := by
    simpa [sigmaOne] using double_sum_mul (fun i => κ i ^ 3) κ
  have hsecond : (∑ i, ∑ j, κ i * (κ j ^ 3)) =
      sigmaOne κ * ∑ j, κ j ^ 3 := by
    simpa [sigmaOne] using double_sum_mul κ (fun j => κ j ^ 3)
  have hthird : (∑ i, ∑ j, (2 * κ i ^ 2) * κ j ^ 2) =
      2 * (∑ i, κ i ^ 2) * ∑ j, κ j ^ 2 := by
    have h := double_sum_mul (fun i => 2 * κ i ^ 2) (fun j => κ j ^ 2)
    rw [← Finset.mul_sum] at h
    simpa [mul_assoc] using h
  rw [curvatureCommutator, pairDifferenceEnergy, hexpand]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hfirst, hsecond, hthird]
  ring

theorem pairDifferenceEnergy_nonneg (κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    0 ≤ pairDifferenceEnergy κ := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (hκ i) (hκ j)) (sq_nonneg _)

theorem curvatureCommutator_nonneg (κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    0 ≤ curvatureCommutator κ := by
  rw [curvatureCommutator_eq_pairDifferenceEnergy]
  exact pairDifferenceEnergy_nonneg κ hκ

def IsSymmetric3 (T : ι → ι → ι → ℝ) : Prop :=
  (∀ i j k, T i j k = T j i k) ∧ (∀ i j k, T i j k = T i k j)

omit [Fintype ι] in
theorem symmetric3_repeated_index_orbit
    {T : ι → ι → ι → ℝ} (hT : IsSymmetric3 T) (i k : ι) :
    T i i k ^ 2 + T i k i ^ 2 + T k i i ^ 2 = 3 * T i i k ^ 2 := by
  have h₁ : T i k i = T i i k := (hT.2 i i k).symm
  have h₂ : T k i i = T i i k := by
    rw [hT.1 k i i, h₁]
  rw [h₁, h₂]
  ring

theorem symmetric3_repeated_index_multiplicity
    {T : ι → ι → ι → ℝ} (hT : IsSymmetric3 T) :
    (∑ i, ∑ k, (T i i k ^ 2 + T i k i ^ 2 + T k i i ^ 2)) =
      3 * ∑ i, ∑ k, T i i k ^ 2 := by
  simp_rw [symmetric3_repeated_index_orbit hT]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

def tensorEnergy (T : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, T i j k ^ 2

section TensorInequality

variable [DecidableEq ι]

def selectedTensorEnergy (T : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k,
    if i = j ∨ i = k ∨ j = k then T i j k ^ 2 else 0

def repeatedTensorLowerEnergy (T : ι → ι → ι → ℝ) : ℝ :=
  (∑ i, T i i i ^ 2) +
    3 * ∑ i, ∑ k ∈ Finset.univ.erase i, T i i k ^ 2

theorem selectedTensorEnergy_le_tensorEnergy (T : ι → ι → ι → ℝ) :
    selectedTensorEnergy T ≤ tensorEnergy T := by
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro k hk
  by_cases h : i = j ∨ i = k ∨ j = k
  · simp [h]
  · simp [h, sq_nonneg]

omit [Fintype ι] in
theorem selected_term_inclusion_exclusion
    (T : ι → ι → ι → ℝ) (i j k : ι) :
    (if i = j ∨ i = k ∨ j = k then T i j k ^ 2 else 0) =
      (if i = j then T i j k ^ 2 else 0) +
      (if i = k then T i j k ^ 2 else 0) +
      (if j = k then T i j k ^ 2 else 0) -
      2 * (if i = j ∧ j = k then T i j k ^ 2 else 0) := by
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp
      ring
    · simp [hik]
  · by_cases hik : i = k
    · subst k
      have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]
    · by_cases hjk : j = k
      · subst k
        simp [hij]
      · simp [hij, hik, hjk]

theorem sum_eq12_slice (T : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, if i = j then T i j k ^ 2 else 0) =
      ∑ i, ∑ k, T i i k ^ 2 := by
  simp

theorem sum_eq13_slice (T : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, if i = k then T i j k ^ 2 else 0) =
      ∑ i, ∑ j, T i j i ^ 2 := by
  simp

theorem sum_eq23_slice (T : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, if j = k then T i j k ^ 2 else 0) =
      ∑ i, ∑ j, T i j j ^ 2 := by
  simp

theorem sum_allEqual_slice (T : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, if i = j ∧ j = k then T i j k ^ 2 else 0) =
      ∑ i, T i i i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j, ∑ k, if i = j ∧ j = k then T i j k ^ 2 else 0) =
        ∑ j, if i = j then T i j j ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    _ = T i i i ^ 2 := by simp

theorem repeated_all_eq_diag_add_off
    (T : ι → ι → ι → ℝ) :
    (∑ i, ∑ k, T i i k ^ 2) =
      (∑ i, T i i i ^ 2) +
        ∑ i, ∑ k ∈ Finset.univ.erase i, T i i k ^ 2 := by
  calc
    (∑ i, ∑ k, T i i k ^ 2) =
        ∑ i, ((∑ k ∈ Finset.univ.erase i, T i i k ^ 2) + T i i i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_erase_add Finset.univ (fun k => T i i k ^ 2)
        (Finset.mem_univ i) |>.symm
    _ = _ := by
      rw [Finset.sum_add_distrib]
      ring

theorem selectedTensorEnergy_eq_repeatedTensorLowerEnergy
    {T : ι → ι → ι → ℝ} (hT : IsSymmetric3 T) :
    selectedTensorEnergy T = repeatedTensorLowerEnergy T := by
  have h13 : (∑ i, ∑ j, T i j i ^ 2) = ∑ i, ∑ k, T i i k ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hT.2 i i j]
  have h23 : (∑ i, ∑ j, T i j j ^ 2) = ∑ i, ∑ k, T i i k ^ 2 := by
    calc
      (∑ i, ∑ j, T i j j ^ 2) = ∑ i, ∑ j, T j j i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hT.1 i j j, ← hT.2 j j i]
      _ = ∑ i, ∑ k, T i i k ^ 2 := Finset.sum_comm
  rw [selectedTensorEnergy]
  simp_rw [selected_term_inclusion_exclusion T]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hfactor :
      (∑ x, ∑ y, ∑ z, 2 *
        (if x = y ∧ y = z then T x y z ^ 2 else 0)) =
        2 * ∑ x, ∑ y, ∑ z,
          (if x = y ∧ y = z then T x y z ^ 2 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
  rw [hfactor, sum_eq12_slice, sum_eq13_slice, sum_eq23_slice,
    sum_allEqual_slice, h13, h23, repeated_all_eq_diag_add_off]
  simp only [repeatedTensorLowerEnergy]
  ring

theorem symmetric3_repeated_index_energy_le
    {T : ι → ι → ι → ℝ} (hT : IsSymmetric3 T) :
    repeatedTensorLowerEnergy T ≤ tensorEnergy T := by
  rw [← selectedTensorEnergy_eq_repeatedTensorLowerEnergy hT]
  exact selectedTensorEnergy_le_tensorEnergy T

def diagonalSlice (T : ι → ι → ι → ℝ) (k : ι) : ι → ℝ :=
  fun i => T i i k

theorem sum_dQuadratic_diagonalSlice_eq_repeatedTensorLowerEnergy
    (T : ι → ι → ι → ℝ) :
    (∑ k, dQuadratic k (diagonalSlice T k)) = repeatedTensorLowerEnergy T := by
  have hoff :
      (∑ k, ∑ i ∈ Finset.univ.erase k, T i i k ^ 2) =
        ∑ i, ∑ k ∈ Finset.univ.erase i, T i i k ^ 2 := by
    have hleft :
        (∑ k, ∑ i ∈ Finset.univ.erase k, T i i k ^ 2) =
          (∑ k, ∑ i, T i i k ^ 2) - ∑ k, T k k k ^ 2 := by
      calc
        (∑ k, ∑ i ∈ Finset.univ.erase k, T i i k ^ 2) =
            ∑ k, ((∑ i, T i i k ^ 2) - T k k k ^ 2) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hsplit := Finset.sum_erase_add Finset.univ
            (fun i => T i i k ^ 2) (Finset.mem_univ k)
          linarith
        _ = _ := by simp only [Finset.sum_sub_distrib]
    have hright :
        (∑ i, ∑ k ∈ Finset.univ.erase i, T i i k ^ 2) =
          (∑ i, ∑ k, T i i k ^ 2) - ∑ i, T i i i ^ 2 := by
      calc
        (∑ i, ∑ k ∈ Finset.univ.erase i, T i i k ^ 2) =
            ∑ i, ((∑ k, T i i k ^ 2) - T i i i ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hsplit := Finset.sum_erase_add Finset.univ
            (fun k => T i i k ^ 2) (Finset.mem_univ i)
          linarith
        _ = _ := by simp only [Finset.sum_sub_distrib]
    rw [hleft, hright, Finset.sum_comm]
  simp only [dQuadratic, diagonalSlice, sumSqAway,
    repeatedTensorLowerEnergy, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hoff]

/-- Pure tensor-reduction step in Liang's tensor proposition. -/
theorem symmetric3_sum_slice_defect_le_tensor_defect
    {T : ι → ι → ι → ℝ} (hT : IsSymmetric3 T) :
    (∑ k, (dQuadratic k (diagonalSlice T k) - sigmaOne (diagonalSlice T k) ^ 2)) ≤
      tensorEnergy T - ∑ k, sigmaOne (diagonalSlice T k) ^ 2 := by
  rw [Finset.sum_sub_distrib,
    sum_dQuadratic_diagonalSlice_eq_repeatedTensorLowerEnergy]
  exact sub_le_sub_right (symmetric3_repeated_index_energy_le hT) _

/-- Any family of one-slice quadratic lower bounds lifts to a full symmetric-tensor bound. -/
theorem symmetric3_tensor_bound_of_slice_bounds
    {T : ι → ι → ι → ℝ} (hT : IsSymmetric3 T)
    (ell : ι → ℝ) (a : ι → ℝ) (C : ℝ)
    (hslice : ∀ k,
      a k * sigmaOne (diagonalSlice T k) ^ 2 -
          C * dot ell (diagonalSlice T k) ^ 2 ≤
        dQuadratic k (diagonalSlice T k) - sigmaOne (diagonalSlice T k) ^ 2) :
    (∑ k, a k * sigmaOne (diagonalSlice T k) ^ 2) -
        C * ∑ k, dot ell (diagonalSlice T k) ^ 2 ≤
      tensorEnergy T - ∑ k, sigmaOne (diagonalSlice T k) ^ 2 := by
  have hsum :
      (∑ k, (a k * sigmaOne (diagonalSlice T k) ^ 2 -
        C * dot ell (diagonalSlice T k) ^ 2)) ≤
        ∑ k, (dQuadratic k (diagonalSlice T k) -
          sigmaOne (diagonalSlice T k) ^ 2) :=
    Finset.sum_le_sum fun k hk => hslice k
  refine le_trans ?_ (symmetric3_sum_slice_defect_le_tensor_defect hT)
  rw [Finset.mul_sum]
  simpa only [Finset.sum_sub_distrib] using hsum

end TensorInequality

section MatrixApplications

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem hermitian_curvatureCommutator_trace_identity
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A.trace.re * (A ^ 3).trace.re - (A ^ 2).trace.re ^ 2) =
      pairDifferenceEnergy hA.eigenvalues := by
  have h₁ := sum_pow_eigenvalues_eq_trace_pow_re' hA 1
  have h₂ := sum_pow_eigenvalues_eq_trace_pow_re' hA 2
  have h₃ := sum_pow_eigenvalues_eq_trace_pow_re' hA 3
  have h₁' : ∑ i, hA.eigenvalues i = A.trace.re := by simpa using h₁
  have h₂' : ∑ i, hA.eigenvalues i ^ 2 = (A ^ 2).trace.re := h₂
  have h₃' : ∑ i, hA.eigenvalues i ^ 3 = (A ^ 3).trace.re := h₃
  rw [← curvatureCommutator_eq_pairDifferenceEnergy]
  simp only [curvatureCommutator]
  rw [← h₁', ← h₂', ← h₃']
  rfl

theorem posSemidef_trace_cubic_commutator_nonneg
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    0 ≤ A.trace.re * (A ^ 3).trace.re - (A ^ 2).trace.re ^ 2 := by
  rw [hermitian_curvatureCommutator_trace_identity hA.isHermitian]
  exact pairDifferenceEnergy_nonneg hA.isHermitian.eigenvalues hA.eigenvalues_nonneg

/-- Spectral form of the hypersurface estimate `|A|² ≤ H²`: for a positive-semidefinite
Hermitian matrix, trace-square energy is bounded by the square of the trace. -/
theorem posSemidef_trace_sq_le_sq_trace
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (A ^ 2).trace.re ≤ A.trace.re ^ 2 := by
  have h₁ := sum_pow_eigenvalues_eq_trace_pow_re' hA.isHermitian 1
  have hsum : sigmaOne hA.isHermitian.eigenvalues = A.trace.re := by
    simpa [sigmaOne] using h₁
  calc
    (A ^ 2).trace.re = ∑ i, hA.isHermitian.eigenvalues i ^ 2 :=
      (sum_sq_eigenvalues_eq_trace_sq_re hA.isHermitian).symm
    _ ≤ sigmaOne hA.isHermitian.eigenvalues ^ 2 :=
      sum_sq_le_sigmaOne_sq_of_nonneg _ hA.eigenvalues_nonneg
    _ = A.trace.re ^ 2 := by rw [hsum]

/-- Square-root form of `posSemidef_trace_sq_le_sq_trace`, directly mirroring `|A| ≤ H`. -/
theorem posSemidef_sqrt_trace_sq_le_trace
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    Real.sqrt (A ^ 2).trace.re ≤ A.trace.re := by
  have h₁ := sum_pow_eigenvalues_eq_trace_pow_re' hA.isHermitian 1
  have hsum : sigmaOne hA.isHermitian.eigenvalues = A.trace.re := by
    simpa [sigmaOne] using h₁
  have htrace : 0 ≤ A.trace.re := by
    rw [← hsum]
    exact Finset.sum_nonneg fun i hi => hA.eigenvalues_nonneg i
  calc
    Real.sqrt (A ^ 2).trace.re ≤ Real.sqrt (A.trace.re ^ 2) :=
      Real.sqrt_le_sqrt (posSemidef_trace_sq_le_sq_trace hA)
    _ = |A.trace.re| := Real.sqrt_sq_eq_abs _
    _ = A.trace.re := abs_of_nonneg htrace

theorem hermitian_newton_weight_bound
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : n) (htrace : 0 < A.trace.re) :
    sigmaTwo hA.eigenvalues / A.trace.re ≤ A.trace.re - hA.eigenvalues k := by
  have h₁ := sum_pow_eigenvalues_eq_trace_pow_re' hA 1
  have hsum : sigmaOne hA.eigenvalues = A.trace.re := by
    simpa [sigmaOne] using h₁
  rw [← hsum] at htrace ⊢
  exact sigmaTwo_div_sigmaOne_le_shiftedTrace hA.eigenvalues k htrace

theorem spectralEnsemble_curvatureCommutator_trace_identity
    {N D : ℕ} (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) :
    ((spectralEnsembleMatrix P θ).trace.re *
        ((spectralEnsembleMatrix P θ) ^ 3).trace.re -
      ((spectralEnsembleMatrix P θ) ^ 2).trace.re ^ 2) =
      pairDifferenceEnergy (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues :=
  hermitian_curvatureCommutator_trace_identity
    (isHermitian_spectralEnsembleMatrix hP θ)

theorem posSemidef_spectralEnsembleMatrix
    {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).PosSemidef) {θ : Fin N → ℝ} (hθ : ∀ a, 0 ≤ θ a) :
    (spectralEnsembleMatrix P θ).PosSemidef := by
  rw [spectralEnsembleMatrix]
  exact Matrix.posSemidef_sum Finset.univ fun a ha =>
    (hP a).smul (by simpa using hθ a)

theorem nonnegative_spectralEnsemble_trace_sq_le_sq_trace
    {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).PosSemidef) {θ : Fin N → ℝ} (hθ : ∀ a, 0 ≤ θ a) :
    ((spectralEnsembleMatrix P θ) ^ 2).trace.re ≤
      (spectralEnsembleMatrix P θ).trace.re ^ 2 :=
  posSemidef_trace_sq_le_sq_trace (posSemidef_spectralEnsembleMatrix hP hθ)

theorem nonnegative_spectralEnsemble_cubic_commutator_nonneg
    {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).PosSemidef) {θ : Fin N → ℝ} (hθ : ∀ a, 0 ≤ θ a) :
    0 ≤ (spectralEnsembleMatrix P θ).trace.re *
        ((spectralEnsembleMatrix P θ) ^ 3).trace.re -
      ((spectralEnsembleMatrix P θ) ^ 2).trace.re ^ 2 :=
  posSemidef_trace_cubic_commutator_nonneg
    (posSemidef_spectralEnsembleMatrix hP hθ)

end MatrixApplications

def parallelTime (K : ℝ) : ℝ := 1 / (4 * (K + 1))

def parallelFactor (K x : ℝ) : ℝ := 1 + parallelTime K * x

def parallelJacobian (K : ℝ) (κ : ι → ℝ) : ℝ :=
  ∏ i, parallelFactor K (κ i)

theorem parallelFactor_ge_three_quarters
    {K x : ℝ} (hK : 0 ≤ K) (hx : -K ≤ x) :
    (3 / 4 : ℝ) ≤ parallelFactor K x := by
  have hd : 0 < 4 * (K + 1) := mul_pos (by norm_num) (by linarith)
  have hdiv : (-K) / (4 * (K + 1)) ≤ x / (4 * (K + 1)) :=
    (div_le_div_iff_of_pos_right hd).2 hx
  have hbase : (3 / 4 : ℝ) ≤ 1 + (-K) / (4 * (K + 1)) := by
    rw [div_eq_mul_inv]
    have hne : 4 * (K + 1) ≠ 0 := ne_of_gt hd
    field_simp
    linarith
  simp only [parallelFactor, parallelTime]
  rw [one_div_mul_eq_div]
  linarith

theorem parallelJacobian_pos
    {K : ℝ} (hK : 0 ≤ K) (κ : ι → ℝ) (hκ : ∀ i, -K ≤ κ i) :
    0 < parallelJacobian K κ := by
  apply Finset.prod_pos
  intro i hi
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4)
    (parallelFactor_ge_three_quarters hK (hκ i))

theorem posSemidef_parallelJacobian_pos
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    0 < parallelJacobian 0 hA.isHermitian.eigenvalues := by
  exact parallelJacobian_pos (by norm_num) hA.isHermitian.eigenvalues
    (fun i => by simpa using hA.eigenvalues_nonneg i)

theorem nonnegative_spectralEnsemble_parallelJacobian_pos
    {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).PosSemidef) {θ : Fin N → ℝ} (hθ : ∀ a, 0 ≤ θ a) :
    0 < parallelJacobian 0
      (isHermitian_spectralEnsembleMatrix (fun a => (hP a).isHermitian) θ).eigenvalues := by
  simpa using posSemidef_parallelJacobian_pos
    (posSemidef_spectralEnsembleMatrix hP hθ)

end GaloisForLFunctions.HTGeometry.Liang
