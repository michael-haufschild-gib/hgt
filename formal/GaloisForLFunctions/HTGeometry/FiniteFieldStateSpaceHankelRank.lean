import GaloisForLFunctions.HTGeometry.FiniteModalHankelRank

/-!
# Field-generic finite state-space Hankel rank

A scalar response of a `d`-dimensional realization over a field has values

`r n = output ⬝ᵥ A^n *ᵥ input`.

Its leading `d × d` Hankel block factors exactly as the product of the finite observability and
controllability matrices.  Thus a minimal realization has nonzero leading determinant in size `d`,
while every `d`-state realization has zero leading determinant in size `d+1`.  The singularity
survives pointwise limits and arbitrary finite-coordinate approximation when the dimension remains
uniformly bounded.

Unlike a diagonal modal model, arbitrary `A` permits complex, nonnormal, and nondiagonalizable
Jordan responses.  The theorem is a static constraint on observed values, not a time-propagation
claim.
-/

open Filter Topology
open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

open Module

/-- Scalar response of a finite-dimensional realization over a commutative semiring. -/
def algebraicStateSpaceResponse {K : Type*} [CommSemiring K] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) K) (input output : Fin d → K) (n : ℕ) : K :=
  output ⬝ᵥ (A ^ n) *ᵥ input

/-- A sequence has a state-space realization of dimension at most `d` over `K`. -/
def AlgebraicStateSpaceDimensionAtMost {K : Type*} [CommSemiring K]
    (d : ℕ) (m : ℕ → K) : Prop :=
  ∃ A : Matrix (Fin d) (Fin d) K, ∃ input output : Fin d → K,
    m = algebraicStateSpaceResponse A input output

/-- Every finite coordinate block is approximable by state-space responses with one fixed
dimension bound. -/
def FixedAlgebraicStateSpaceDimensionLocalClosure
    {K : Type*} [NormedField K] (d : ℕ) (target : ℕ → K) : Prop :=
  ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ A : Matrix (Fin d) (Fin d) K, ∃ input output : Fin d → K,
      ∀ n : ℕ, n < N →
        dist (algebraicStateSpaceResponse A input output n) (target n) < ε

/-- Finite modal packets are diagonal finite state-space responses. -/
theorem algebraicStateSpaceResponse_diagonal_eq_finiteModalSequence
    {K : Type*} [Field K] {d : ℕ}
    (weight node : Fin d → K) (n : ℕ) :
    algebraicStateSpaceResponse (Matrix.diagonal node) weight (fun _ ↦ 1) n =
      finiteModalSequence weight node n := by
  simp [algebraicStateSpaceResponse, Matrix.diagonal_pow, Matrix.mulVec,
    Matrix.diagonal_apply, dotProduct, finiteModalSequence, mul_comm]

/-- Every finite modal presentation is a diagonal state-space realization of the same dimension. -/
theorem algebraicStateSpaceDimensionAtMost_of_finiteModalWidthAtMost
    {K : Type*} [Field K] {d : ℕ} {m : ℕ → K}
    (h : FiniteModalWidthAtMost d m) :
    AlgebraicStateSpaceDimensionAtMost d m := by
  obtain ⟨weight, node, rfl⟩ := h
  refine ⟨Matrix.diagonal node, weight, fun _ ↦ 1, ?_⟩
  funext n
  exact (algebraicStateSpaceResponse_diagonal_eq_finiteModalSequence weight node n).symm

/-- Matrix of the first `d` reachable state vectors. -/
def algebraicStateSpaceControllabilityMatrix
    {K : Type*} [CommSemiring K] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) K) (input : Fin d → K) :
    Matrix (Fin d) (Fin d) K :=
  fun x j => ((A ^ (j : ℕ)) *ᵥ input) x

/-- Matrix of the first `d` observed state covectors. -/
def algebraicStateSpaceObservabilityMatrix
    {K : Type*} [CommSemiring K] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) K) (output : Fin d → K) :
    Matrix (Fin d) (Fin d) K :=
  fun i x => ∑ y, output y * (A ^ (i : ℕ)) y x

/-- **State-space Hankel factorization.**  The leading response Hankel block is observability times
controllability. -/
theorem algebraicHankelMatrix_stateSpaceResponse_eq_observability_mul_controllability
    {K : Type*} [Field K] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) K) (input output : Fin d → K) :
    algebraicHankelMatrix (algebraicStateSpaceResponse A input output) d =
      algebraicStateSpaceObservabilityMatrix A output *
        algebraicStateSpaceControllabilityMatrix A input := by
  ext i j
  rw [algebraicHankelMatrix, algebraicStateSpaceResponse, pow_add,
    ← Matrix.mulVec_mulVec]
  simp only [Matrix.mul_apply, algebraicStateSpaceObservabilityMatrix,
    algebraicStateSpaceControllabilityMatrix, dotProduct, Matrix.mulVec]
  calc
    ∑ y, output y * ∑ x, (A ^ (i : ℕ)) y x *
        (∑ x_1, (A ^ (j : ℕ)) x x_1 * input x_1) =
        ∑ y, ∑ x, (output y * (A ^ (i : ℕ)) y x) *
          (∑ x_1, (A ^ (j : ℕ)) x x_1 * input x_1) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x, ∑ y, (output y * (A ^ (i : ℕ)) y x) *
          (∑ x_1, (A ^ (j : ℕ)) x x_1 * input x_1) := by
      rw [Finset.sum_comm]
    _ = ∑ x, (∑ y, output y * (A ^ (i : ℕ)) y x) *
          (∑ x_1, (A ^ (j : ℕ)) x x_1 * input x_1) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]

/-- Exact determinant factorization of the active state-space Hankel block. -/
theorem det_algebraicHankelMatrix_stateSpaceResponse_eq_observability_mul_controllability
    {K : Type*} [Field K] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) K) (input output : Fin d → K) :
    (algebraicHankelMatrix (algebraicStateSpaceResponse A input output) d).det =
      (algebraicStateSpaceObservabilityMatrix A output).det *
        (algebraicStateSpaceControllabilityMatrix A input).det := by
  rw [algebraicHankelMatrix_stateSpaceResponse_eq_observability_mul_controllability,
    Matrix.det_mul]

/-- The active state-space Hankel block is nonsingular exactly when the realization is both
observable and controllable on its full state dimension. -/
theorem det_algebraicHankelMatrix_stateSpaceResponse_ne_zero_iff
    {K : Type*} [Field K] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) K) (input output : Fin d → K) :
    (algebraicHankelMatrix (algebraicStateSpaceResponse A input output) d).det ≠ 0 ↔
      (algebraicStateSpaceObservabilityMatrix A output).det ≠ 0 ∧
        (algebraicStateSpaceControllabilityMatrix A input).det ≠ 0 := by
  rw [det_algebraicHankelMatrix_stateSpaceResponse_eq_observability_mul_controllability,
    mul_ne_zero_iff]

/-- Response values at a sum of indices factor through the hidden state. -/
theorem algebraicStateSpaceResponse_add
    {K : Type*} [Field K] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) K) (input output : Fin d → K) (i j : ℕ) :
    algebraicStateSpaceResponse A input output (i + j) =
      output ⬝ᵥ (A ^ i) *ᵥ ((A ^ j) *ᵥ input) := by
  rw [algebraicStateSpaceResponse, pow_add, Matrix.mulVec_mulVec]

/-- The first `d+1` reachable vectors of a `d`-state realization are dependent. -/
theorem exists_algebraicStateSpace_controllability_relation
    {K : Type*} [Field K] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) K) (input : Fin d → K) :
    ∃ c : Fin (d + 1) → K,
      (∑ j, c j • ((A ^ (j : ℕ)) *ᵥ input)) = 0 ∧ ∃ j, c j ≠ 0 := by
  let v : Fin (d + 1) → (Fin d → K) :=
    fun j ↦ (A ^ (j : ℕ)) *ᵥ input
  have hv : ¬ LinearIndependent K v := by
    intro hli
    have hbound := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin, finrank_pi] at hbound
    omega
  simpa only [v] using Fintype.not_linearIndependent_iff.mp hv

/-- A controllability relation is a kernel vector of the oversized response Hankel block. -/
theorem algebraicHankelMatrix_mulVec_stateSpace_relation_eq_zero
    {K : Type*} [Field K] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) K) (input output : Fin d → K)
    (c : Fin (d + 1) → K)
    (hc : (∑ j, c j • ((A ^ (j : ℕ)) *ᵥ input)) = 0) :
    algebraicHankelMatrix (algebraicStateSpaceResponse A input output) (d + 1) *ᵥ c = 0 := by
  funext r
  simp only [Matrix.mulVec, algebraicHankelMatrix, Pi.zero_apply]
  change ∑ j : Fin (d + 1),
      algebraicStateSpaceResponse A input output ((r : ℕ) + (j : ℕ)) * c j = 0
  simp_rw [algebraicStateSpaceResponse_add]
  calc
    ∑ j : Fin (d + 1),
        (output ⬝ᵥ (A ^ (r : ℕ)) *ᵥ ((A ^ (j : ℕ)) *ᵥ input)) * c j =
        output ⬝ᵥ (A ^ (r : ℕ)) *ᵥ
          (∑ j : Fin (d + 1), c j • ((A ^ (j : ℕ)) *ᵥ input)) := by
      rw [Matrix.mulVec_sum, dotProduct_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mulVec_smul]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 0 := by rw [hc, Matrix.mulVec_zero, dotProduct_zero]

/-- Every `d`-state response has singular leading Hankel block in size `d+1`. -/
theorem det_algebraicHankelMatrix_stateSpaceResponse_succ_eq_zero
    {K : Type*} [Field K] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) K) (input output : Fin d → K) :
    (algebraicHankelMatrix (algebraicStateSpaceResponse A input output) (d + 1)).det = 0 := by
  obtain ⟨c, hrel, j, hj⟩ := exists_algebraicStateSpace_controllability_relation A input
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (algebraicHankelMatrix_mulVec_stateSpace_relation_eq_zero A input output c hrel)
    (i := j)
  simpa [mem_nonZeroDivisors_iff_ne_zero] using hj

/-- The determinant obstruction in representation form. -/
theorem det_algebraicHankelMatrix_succ_eq_zero_of_stateSpaceDimensionAtMost
    {K : Type*} [Field K] {d : ℕ} {m : ℕ → K}
    (hm : AlgebraicStateSpaceDimensionAtMost d m) :
    (algebraicHankelMatrix m (d + 1)).det = 0 := by
  obtain ⟨A, input, output, rfl⟩ := hm
  exact det_algebraicHankelMatrix_stateSpaceResponse_succ_eq_zero A input output

/-- **Exact positive state-dimension certificate.**  A minimal realization has nonsingular active
Hankel block and singular next block. -/
theorem algebraicStateSpaceResponse_exact_hankel_stateDimension
    {K : Type*} [Field K] {d : ℕ}
    {A : Matrix (Fin d) (Fin d) K} {input output : Fin d → K}
    (hobs : (algebraicStateSpaceObservabilityMatrix A output).det ≠ 0)
    (hctrl : (algebraicStateSpaceControllabilityMatrix A input).det ≠ 0) :
    (algebraicHankelMatrix (algebraicStateSpaceResponse A input output) d).det ≠ 0 ∧
      (algebraicHankelMatrix (algebraicStateSpaceResponse A input output) (d + 1)).det = 0 :=
  ⟨(det_algebraicHankelMatrix_stateSpaceResponse_ne_zero_iff A input output).mpr
      ⟨hobs, hctrl⟩,
    det_algebraicHankelMatrix_stateSpaceResponse_succ_eq_zero A input output⟩

/-- Exact finite state dimension implies fixed-dimensional local closure. -/
theorem fixedAlgebraicStateSpaceDimensionLocalClosure_of_dimensionAtMost
    {K : Type*} [NormedField K] {d : ℕ} {target : ℕ → K}
    (h : AlgebraicStateSpaceDimensionAtMost d target) :
    FixedAlgebraicStateSpaceDimensionLocalClosure d target := by
  obtain ⟨A, input, output, rfl⟩ := h
  intro N ε hε
  exact ⟨A, input, output, fun n _ ↦ by simpa using hε⟩

/-- Fixed state dimension remains singular under pointwise convergence. -/
theorem det_algebraicHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimension_tendsto
    {K : Type*} [NormedField K]
    {d : ℕ} {m : ℕ → ℕ → K} {target : ℕ → K}
    (hm : ∀ j, AlgebraicStateSpaceDimensionAtMost d (m j))
    (hconv : Tendsto m atTop (nhds target)) :
    (algebraicHankelMatrix target (d + 1)).det = 0 := by
  have hmatrix : Tendsto
      (fun j ↦ algebraicHankelMatrix (m j) (d + 1)) atTop
      (nhds (algebraicHankelMatrix target (d + 1))) := by
    apply tendsto_pi_nhds.mpr
    intro r
    apply tendsto_pi_nhds.mpr
    intro c
    simpa [algebraicHankelMatrix] using
      (tendsto_pi_nhds.mp hconv) ((r : ℕ) + (c : ℕ))
  have hdet : Tendsto
      (fun j ↦ (algebraicHankelMatrix (m j) (d + 1)).det) atTop
      (nhds (algebraicHankelMatrix target (d + 1)).det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix
  have hzero : Tendsto
      (fun j ↦ (algebraicHankelMatrix (m j) (d + 1)).det) atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    exact Filter.Eventually.of_forall fun j ↦
      (det_algebraicHankelMatrix_succ_eq_zero_of_stateSpaceDimensionAtMost (hm j)).symm
  exact tendsto_nhds_unique hdet hzero

/-- Uniformly bounded state dimension remains singular even when each finite observation window
may use a different realization. -/
theorem det_algebraicHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure
    {K : Type*} [NormedField K]
    {d : ℕ} {target : ℕ → K}
    (h : FixedAlgebraicStateSpaceDimensionLocalClosure d target) :
    (algebraicHankelMatrix target (d + 1)).det = 0 := by
  have happ : ∀ j : ℕ, ∃ A : Matrix (Fin d) (Fin d) K,
      ∃ input output : Fin d → K,
      ∀ n : ℕ, n < j + 1 →
        dist (algebraicStateSpaceResponse A input output n) (target n) <
          1 / ((j : ℝ) + 1) := by
    intro j
    exact h (j + 1) (1 / ((j : ℝ) + 1)) (by positivity)
  choose A input output happrox using happ
  let approx : ℕ → ℕ → K :=
    fun j ↦ algebraicStateSpaceResponse (A j) (input j) (output j)
  have hdim : ∀ j, AlgebraicStateSpaceDimensionAtMost d (approx j) := by
    intro j
    exact ⟨A j, input j, output j, rfl⟩
  have hconv : Tendsto approx atTop (nhds target) := by
    apply tendsto_pi_nhds.mpr
    intro n
    rw [Metric.tendsto_atTop]
    intro ε hε
    have herr : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < ε :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hε)
    obtain ⟨J, hJ⟩ := eventually_atTop.mp herr
    refine ⟨max J n, fun j hj ↦ ?_⟩
    exact (happrox j n (by omega)).trans
      (hJ j (le_trans (le_max_left _ _) hj))
  exact det_algebraicHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimension_tendsto hdim hconv

/-- A single nonzero Hankel determinant excludes every fixed-dimensional local state-space
approximation. -/
theorem not_fixedAlgebraicStateSpaceDimensionLocalClosure_of_det_ne_zero
    {K : Type*} [NormedField K]
    {d : ℕ} {target : ℕ → K}
    (hdet : (algebraicHankelMatrix target (d + 1)).det ≠ 0) :
    ¬ FixedAlgebraicStateSpaceDimensionLocalClosure d target := by
  intro h
  exact hdet
    (det_algebraicHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure h)

end

end HTGeometry
