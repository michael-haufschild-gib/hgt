import GaloisForLFunctions.HTGeometry.PositiveConeDeterminantMonotone
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-!
# Determinant floor for bistochastic Kraus maps

A finite Kraus map which is both unital and trace preserving cannot decrease the determinant on
the positive-definite cone.  The proof diagonalizes input and output, observes that transition
probabilities between their eigenbases form a doubly stochastic matrix, and applies scalar
weighted log concavity row by row.
-/

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d κ : Type*} [Fintype d] [DecidableEq d] [Fintype κ] [DecidableEq κ]

/-- Finite weighted log concavity, in the exact form used for eigenvalue transport. -/
theorem weighted_log_le_log_weighted_sum
    {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    ∑ i, w i * Real.log (x i) ≤ Real.log (∑ i, w i * x i) := by
  classical
  let m : ℝ := ∑ i, w i * x i
  have hw_exists : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have hs : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  have hm : 0 < m := by
    obtain ⟨i, hi⟩ := hw_exists
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (le_of_lt (hx j)))
      ⟨i, Finset.mem_univ i, mul_pos hi (hx i)⟩
  have hterm (i : ι) :
      w i * (Real.log (x i) - Real.log m) ≤ w i * (x i / m - 1) := by
    rw [← Real.log_div (ne_of_gt (hx i)) (ne_of_gt hm)]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (hx i) hm)) (hw i)
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  have hleft :
      ∑ i, w i * (Real.log (x i) - Real.log m) =
        (∑ i, w i * Real.log (x i)) - Real.log m := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum]
    ring
  have hright : ∑ i, w i * (x i / m - 1) = 0 := by
    simp_rw [mul_sub, mul_one]
    simp_rw [← mul_div_assoc]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hw_sum]
    change m / m - 1 = 0
    rw [div_self (ne_of_gt hm), sub_self]
  rw [hleft, hright] at hsum
  linarith

/-- A Kraus operator expressed between the output and input eigenbases. -/
def bistochasticKrausEigenMatrix (B : κ → Matrix d d ℂ)
    {X Y : Matrix d d ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (k : κ) :
    Matrix d d ℂ :=
  (hY.eigenvectorUnitary : Matrix d d ℂ)ᴴ * B k *
    (hX.eigenvectorUnitary : Matrix d d ℂ)

/-- Squared transition mass between an input and output eigenvector. -/
def bistochasticKrausEigenWeight (B : κ → Matrix d d ℂ)
    {X Y : Matrix d d ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (i j : d) : ℝ :=
  ∑ k, Complex.normSq (bistochasticKrausEigenMatrix B hX hY k i j)

theorem bistochasticKrausEigenWeight_nonneg (B : κ → Matrix d d ℂ)
    {X Y : Matrix d d ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (i j : d) :
    0 ≤ bistochasticKrausEigenWeight B hX hY i j :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

set_option maxHeartbeats 800000 in
theorem sum_bistochasticKrausEigenMatrix_conjTranspose_mul_self
    (B : κ → Matrix d d ℂ) {X Y : Matrix d d ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hB : ∑ k, (B k)ᴴ * B k = 1) :
    ∑ k, (bistochasticKrausEigenMatrix B hX hY k)ᴴ *
        bistochasticKrausEigenMatrix B hX hY k = 1 := by
  classical
  let U : Matrix d d ℂ := hX.eigenvectorUnitary
  let V : Matrix d d ℂ := hY.eigenvectorUnitary
  have hUU : Uᴴ * U = 1 := by
    change (hX.eigenvectorUnitary : Matrix d d ℂ)ᴴ *
        (hX.eigenvectorUnitary : Matrix d d ℂ) = 1
    exact (Unitary.mem_iff.mp hX.eigenvectorUnitary.property).1
  have hVV : V * Vᴴ = 1 := by
    change (hY.eigenvectorUnitary : Matrix d d ℂ) *
        (hY.eigenvectorUnitary : Matrix d d ℂ)ᴴ = 1
    exact (Unitary.mem_iff.mp hY.eigenvectorUnitary.property).2
  have hterm (k : κ) :
      (bistochasticKrausEigenMatrix B hX hY k)ᴴ *
          bistochasticKrausEigenMatrix B hX hY k =
        Uᴴ * ((B k)ᴴ * B k) * U := by
    simp only [bistochasticKrausEigenMatrix, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    change (Uᴴ * ((B k)ᴴ * V)) * (Vᴴ * B k * U) = Uᴴ * ((B k)ᴴ * B k) * U
    calc
      (Uᴴ * ((B k)ᴴ * V)) * (Vᴴ * B k * U) =
          Uᴴ * (B k)ᴴ * (V * Vᴴ) * B k * U := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * ((B k)ᴴ * B k) * U := by rw [hVV]; simp only [Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hB, Matrix.mul_one, hUU]

set_option maxHeartbeats 800000 in
theorem sum_bistochasticKrausEigenMatrix_mul_conjTranspose
    (B : κ → Matrix d d ℂ) {X Y : Matrix d d ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hB : ∑ k, B k * (B k)ᴴ = 1) :
    ∑ k, bistochasticKrausEigenMatrix B hX hY k *
        (bistochasticKrausEigenMatrix B hX hY k)ᴴ = 1 := by
  classical
  let U : Matrix d d ℂ := hX.eigenvectorUnitary
  let V : Matrix d d ℂ := hY.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := by
    change (hX.eigenvectorUnitary : Matrix d d ℂ) *
        (hX.eigenvectorUnitary : Matrix d d ℂ)ᴴ = 1
    exact (Unitary.mem_iff.mp hX.eigenvectorUnitary.property).2
  have hVV : Vᴴ * V = 1 := by
    change (hY.eigenvectorUnitary : Matrix d d ℂ)ᴴ *
        (hY.eigenvectorUnitary : Matrix d d ℂ) = 1
    exact (Unitary.mem_iff.mp hY.eigenvectorUnitary.property).1
  have hterm (k : κ) :
      bistochasticKrausEigenMatrix B hX hY k *
          (bistochasticKrausEigenMatrix B hX hY k)ᴴ =
        Vᴴ * (B k * (B k)ᴴ) * V := by
    simp only [bistochasticKrausEigenMatrix, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    change (Vᴴ * B k * U) * (Uᴴ * ((B k)ᴴ * V)) = Vᴴ * (B k * (B k)ᴴ) * V
    calc
      (Vᴴ * B k * U) * (Uᴴ * ((B k)ᴴ * V)) =
          Vᴴ * B k * (U * Uᴴ) * (B k)ᴴ * V := by simp only [Matrix.mul_assoc]
      _ = Vᴴ * (B k * (B k)ᴴ) * V := by rw [hUU]; simp only [Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hB, Matrix.mul_one, hVV]

/-- Row squared masses are normalized by the unital Kraus identity. -/
theorem sum_normSq_row_eq_one_of_sum_mul_conjTranspose
    (C : κ → Matrix d d ℂ) (hC : ∑ k, C k * (C k)ᴴ = 1) (i : d) :
    ∑ j, ∑ k, Complex.normSq (C k i j) = 1 := by
  classical
  have hentry := congrFun (congrFun hC i) i
  have hentry' : ∑ k, ∑ j, C k i j * (starRingEnd ℂ) (C k i j) = (1 : ℂ) := by
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def] using hentry
  apply Complex.ofReal_injective
  rw [Complex.ofReal_one, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  rw [Finset.sum_comm]
  simpa only [mul_comm] using hentry'

/-- Column squared masses are normalized by the trace-preserving Kraus identity. -/
theorem sum_normSq_column_eq_one_of_sum_conjTranspose_mul_self
    (C : κ → Matrix d d ℂ) (hC : ∑ k, (C k)ᴴ * C k = 1) (j : d) :
    ∑ i, ∑ k, Complex.normSq (C k i j) = 1 := by
  classical
  have hentry := congrFun (congrFun hC j) j
  have hentry' : ∑ k, ∑ i, (starRingEnd ℂ) (C k i j) * C k i j = (1 : ℂ) := by
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def] using hentry
  apply Complex.ofReal_injective
  rw [Complex.ofReal_one, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  rw [Finset.sum_comm]
  exact hentry'

theorem sum_bistochasticKrausEigenWeight_row
    (B : κ → Matrix d d ℂ) {X Y : Matrix d d ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hB : ∑ k, B k * (B k)ᴴ = 1) (i : d) :
    ∑ j, bistochasticKrausEigenWeight B hX hY i j = 1 :=
  sum_normSq_row_eq_one_of_sum_mul_conjTranspose _
    (sum_bistochasticKrausEigenMatrix_mul_conjTranspose B hX hY hB) i

theorem sum_bistochasticKrausEigenWeight_column
    (B : κ → Matrix d d ℂ) {X Y : Matrix d d ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hB : ∑ k, (B k)ᴴ * B k = 1) (j : d) :
    ∑ i, bistochasticKrausEigenWeight B hX hY i j = 1 :=
  sum_normSq_column_eq_one_of_sum_conjTranspose_mul_self _
    (sum_bistochasticKrausEigenMatrix_conjTranspose_mul_self B hX hY hB) j

/-- Conjugating a Hermitian matrix into its eigenvector unitary gives its eigenvalue diagonal. -/
theorem conjTranspose_mul_self_mul_eigenvectorUnitary
    {X : Matrix d d ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix d d ℂ)ᴴ * X *
        (hX.eigenvectorUnitary : Matrix d d ℂ) =
      Matrix.diagonal fun i => (hX.eigenvalues i : ℂ) := by
  let U : Matrix d d ℂ := hX.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal fun i => (hX.eigenvalues i : ℂ)
  have hleft : Uᴴ * U = 1 := by
    have h := (Unitary.mem_iff.mp hX.eigenvectorUnitary.property).1
    rw [Matrix.star_eq_conjTranspose] at h
    exact h
  have hspec : X = U * D * Uᴴ := by
    have h := isHermitian_eq_conj_diagonal hX
    rw [Matrix.star_eq_conjTranspose] at h
    simpa only [U, D] using h
  calc
    Uᴴ * X * U = Uᴴ * (U * D * Uᴴ) * U :=
      congrArg (fun Z : Matrix d d ℂ => Uᴴ * Z * U) hspec
    _ = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
    _ = D := by rw [hleft]; simp only [Matrix.one_mul, Matrix.mul_one]

set_option maxHeartbeats 800000 in
/-- In input/output eigenbases, a Kraus image is a stochastic mixture of input eigenvalues. -/
theorem eigenvalues_kraus_sum_eq_weighted_sum
    (B : κ → Matrix d d ℂ) {X Y : Matrix d d ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hYX : Y = ∑ k, B k * X * (B k)ᴴ) (i : d) :
    hY.eigenvalues i =
      ∑ j, bistochasticKrausEigenWeight B hX hY i j * hX.eigenvalues j := by
  classical
  let U : Matrix d d ℂ := hX.eigenvectorUnitary
  let V : Matrix d d ℂ := hY.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal fun j => (hX.eigenvalues j : ℂ)
  let C : κ → Matrix d d ℂ := bistochasticKrausEigenMatrix B hX hY
  have hXspec : X = U * D * Uᴴ := by
    have h := isHermitian_eq_conj_diagonal hX
    rw [Matrix.star_eq_conjTranspose] at h
    simpa only [U, D] using h
  have hconj :
      Matrix.diagonal (fun j => (hY.eigenvalues j : ℂ)) =
        ∑ k, C k * D * (C k)ᴴ := by
    calc
      Matrix.diagonal (fun j => (hY.eigenvalues j : ℂ)) = Vᴴ * Y * V := by
        simpa only [V] using (conjTranspose_mul_self_mul_eigenvectorUnitary hY).symm
      _ = Vᴴ * (∑ k, B k * X * (B k)ᴴ) * V :=
        congrArg (fun Z : Matrix d d ℂ => Vᴴ * Z * V) hYX
      _ = ∑ k, C k * D * (C k)ᴴ := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        apply Finset.sum_congr rfl
        intro k _hk
        calc
          Vᴴ * (B k * X * (B k)ᴴ) * V =
              Vᴴ * (B k * (U * D * Uᴴ) * (B k)ᴴ) * V :=
            congrArg (fun Z : Matrix d d ℂ => Vᴴ * (B k * Z * (B k)ᴴ) * V) hXspec
          _ = C k * D * (C k)ᴴ := by
            simp only [C, U, V, bistochasticKrausEigenMatrix, Matrix.conjTranspose_mul,
              Matrix.conjTranspose_conjTranspose]
            simp only [Matrix.mul_assoc]
  have hentry := congrFun (congrFun hconj i) i
  have hcomplex :
      (hY.eigenvalues i : ℂ) =
        ∑ j, ((bistochasticKrausEigenWeight B hX hY i j : ℝ) : ℂ) *
          (hX.eigenvalues j : ℂ) := by
    change (hY.eigenvalues i : ℂ) =
      ∑ j, ((∑ k, Complex.normSq (C k i j) : ℝ) : ℂ) * (hX.eigenvalues j : ℂ)
    rw [Matrix.diagonal_apply, if_pos rfl] at hentry
    rw [hentry]
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, D,
      Matrix.diagonal_apply]
    have hdiag (k : κ) (j : d) :
        ∑ p, C k i p * (if p = j then (hX.eigenvalues p : ℂ) else 0) =
          C k i j * (hX.eigenvalues j : ℂ) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro p _hp hpj
        simp [hpj]
      · simp
    simp_rw [hdiag]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Complex.ofReal_sum]
    simp_rw [Complex.normSq_eq_conj_mul_self]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _hk
    simp only [Complex.star_def]
    ring
  exact_mod_cast hcomplex

set_option maxHeartbeats 800000 in
/-- A bistochastic Kraus image cannot decrease the determinant of a positive-definite matrix. -/
theorem det_le_det_of_bistochasticKraus_sum
    (B : κ → Matrix d d ℂ) {X Y : Matrix d d ℂ}
    (hX : X.PosDef) (hY : Y.PosDef)
    (hYX : Y = ∑ k, B k * X * (B k)ᴴ)
    (htrace : ∑ k, (B k)ᴴ * B k = 1)
    (hunital : ∑ k, B k * (B k)ᴴ = 1) :
    X.det ≤ Y.det := by
  classical
  let w : d → d → ℝ := bistochasticKrausEigenWeight B hX.isHermitian hY.isHermitian
  have hrow (i : d) : ∑ j, w i j = 1 :=
    sum_bistochasticKrausEigenWeight_row B hX.isHermitian hY.isHermitian hunital i
  have hcolumn (j : d) : ∑ i, w i j = 1 :=
    sum_bistochasticKrausEigenWeight_column B hX.isHermitian hY.isHermitian htrace j
  have htransport (i : d) :
      hY.isHermitian.eigenvalues i = ∑ j, w i j * hX.isHermitian.eigenvalues j :=
    eigenvalues_kraus_sum_eq_weighted_sum B hX.isHermitian hY.isHermitian hYX i
  have hrow_log (i : d) :
      ∑ j, w i j * Real.log (hX.isHermitian.eigenvalues j) ≤
        Real.log (hY.isHermitian.eigenvalues i) := by
    have h := weighted_log_le_log_weighted_sum
      (w i) hX.isHermitian.eigenvalues
      (fun j => bistochasticKrausEigenWeight_nonneg B hX.isHermitian hY.isHermitian i j)
      (hrow i) hX.eigenvalues_pos
    rwa [← htransport i] at h
  have hlogs :
      ∑ j, Real.log (hX.isHermitian.eigenvalues j) ≤
        ∑ i, Real.log (hY.isHermitian.eigenvalues i) := by
    have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hrow_log i
    rw [Finset.sum_comm] at hsum
    have hleft :
        ∑ j, ∑ i, w i j * Real.log (hX.isHermitian.eigenvalues j) =
          ∑ j, Real.log (hX.isHermitian.eigenvalues j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← Finset.sum_mul, hcolumn j, one_mul]
    rwa [hleft] at hsum
  have hprod :
      ∏ j, hX.isHermitian.eigenvalues j ≤ ∏ i, hY.isHermitian.eigenvalues i := by
    have hexp := Real.exp_le_exp.mpr hlogs
    rw [Real.exp_sum, Real.exp_sum] at hexp
    simpa only [Real.exp_log (hX.eigenvalues_pos _), Real.exp_log (hY.eigenvalues_pos _)]
      using hexp
  rw [hX.isHermitian.det_eq_prod_eigenvalues, hY.isHermitian.det_eq_prod_eigenvalues]
  exact_mod_cast hprod

end

end GaloisForLFunctions.HTGeometry
