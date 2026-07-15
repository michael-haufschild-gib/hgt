import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank

/-!
# Finite state-space realizations force finite Hankel rank

A scalar response of a `d`-dimensional linear realization has the static value form

`m n = output ⬝ᵥ A^n *ᵥ input`.

The Hankel entry `m (i+j)` factors through the same hidden state space because
`A^(i+j)=A^i A^j`.  Hence the first `d+1` controllability vectors are dependent and the leading
Hankel determinant of size `d+1` vanishes.  The conclusion survives pointwise limits and local
finite-coordinate approximation when the state dimension stays uniformly bounded.

This strictly enlarges the existing finite-spectral boundary: diagonal `A` recovers finite sums of
spectral lines, while arbitrary `A` also permits nonnormal and nondiagonalizable/Jordan responses.
The same value law underlies finite hidden Markov models, weighted automata, linear recurrent and
state-space machine-learning models, finite quantum transfer matrices, and finite-bond tensor
networks.  No positivity, stochasticity, diagonalizability, or temporal interpretation is assumed.
-/

open Filter Topology
open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

open Module

/-- Scalar response of a finite-dimensional linear state-space realization. -/
def finiteStateSpaceResponse {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (input output : Fin d → ℝ) (n : ℕ) : ℝ :=
  output ⬝ᵥ (A ^ n) *ᵥ input

/-- A scalar sequence has a linear state-space realization of dimension at most `d`. -/
def StateSpaceDimensionAtMost (d : ℕ) (m : ℕ → ℝ) : Prop :=
  ∃ A : Matrix (Fin d) (Fin d) ℝ, ∃ input output : Fin d → ℝ,
    m = finiteStateSpaceResponse A input output

/-- Every finite coordinate block of `target` is arbitrarily approximable by linear state-space
responses with one fixed dimension bound `d`. -/
def FixedStateSpaceDimensionLocalClosure (d : ℕ) (target : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ A : Matrix (Fin d) (Fin d) ℝ, ∃ input output : Fin d → ℝ,
      ∀ n : ℕ, n < N →
        dist (finiteStateSpaceResponse A input output n) (target n) < ε

/-- Finite spectral moments are diagonal finite state-space responses. -/
theorem finiteStateSpaceResponse_diagonal_eq_finiteSpectralMoment {d : ℕ}
    (mass node : Fin d → ℝ) (n : ℕ) :
    finiteStateSpaceResponse (Matrix.diagonal node) mass (fun _ ↦ 1) n =
      finiteSpectralMoment mass node n := by
  simp [finiteStateSpaceResponse, Matrix.diagonal_pow, Matrix.mulVec,
    Matrix.diagonal_apply, dotProduct, finiteSpectralMoment, mul_comm]

/-- The old fixed-spectral-width closure is a subclass of fixed state-space dimension. -/
theorem fixedStateSpaceDimensionLocalClosure_of_fixedSpectralWidthLocalClosure
    {d : ℕ} {target : ℕ → ℝ}
    (h : FixedSpectralWidthLocalClosure d target) :
    FixedStateSpaceDimensionLocalClosure d target := by
  intro N ε hε
  obtain ⟨mass, node, happrox⟩ := h N ε hε
  refine ⟨Matrix.diagonal node, mass, fun _ ↦ 1, ?_⟩
  intro n hn
  rw [finiteStateSpaceResponse_diagonal_eq_finiteSpectralMoment]
  exact happrox n hn

/-- The response at a sum of observation indices factors through the hidden state space. -/
theorem finiteStateSpaceResponse_add {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (input output : Fin d → ℝ) (i j : ℕ) :
    finiteStateSpaceResponse A input output (i + j) =
      output ⬝ᵥ (A ^ i) *ᵥ ((A ^ j) *ᵥ input) := by
  rw [finiteStateSpaceResponse, pow_add, Matrix.mulVec_mulVec]

/-- The first `d+1` controllability vectors of a `d`-state realization are dependent. -/
theorem exists_finiteStateSpace_controllability_relation {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (input : Fin d → ℝ) :
    ∃ c : Fin (d + 1) → ℝ,
      (∑ j, c j • ((A ^ (j : ℕ)) *ᵥ input)) = 0 ∧ ∃ j, c j ≠ 0 := by
  let v : Fin (d + 1) → (Fin d → ℝ) :=
    fun j ↦ (A ^ (j : ℕ)) *ᵥ input
  have hv : ¬ LinearIndependent ℝ v := by
    intro hli
    have hbound := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin, finrank_pi] at hbound
    omega
  simpa only [v] using Fintype.not_linearIndependent_iff.mp hv

/-- A controllability relation is a kernel vector of the leading response Hankel block. -/
theorem momentHankelMatrix_mulVec_finiteStateSpace_relation_eq_zero {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (input output : Fin d → ℝ)
    (c : Fin (d + 1) → ℝ)
    (hc : (∑ j, c j • ((A ^ (j : ℕ)) *ᵥ input)) = 0) :
    momentHankelMatrix (finiteStateSpaceResponse A input output) (d + 1) *ᵥ c = 0 := by
  funext r
  simp only [Matrix.mulVec, momentHankelMatrix, Pi.zero_apply]
  change ∑ j : Fin (d + 1),
      finiteStateSpaceResponse A input output ((r : ℕ) + (j : ℕ)) * c j = 0
  simp_rw [finiteStateSpaceResponse_add]
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

/-- **Finite state-space Hankel rank law.**  Every scalar response of a `d`-dimensional linear
realization has zero leading Hankel determinant in size `d+1`. -/
theorem det_momentHankelMatrix_finiteStateSpaceResponse_succ_eq_zero {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (input output : Fin d → ℝ) :
    (momentHankelMatrix (finiteStateSpaceResponse A input output) (d + 1)).det = 0 := by
  obtain ⟨c, hrel, j, hj⟩ := exists_finiteStateSpace_controllability_relation A input
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (momentHankelMatrix_mulVec_finiteStateSpace_relation_eq_zero A input output c hrel)
    (i := j)
  simpa [mem_nonZeroDivisors_iff_ne_zero] using hj

/-- The determinant obstruction in realization form. -/
theorem det_momentHankelMatrix_succ_eq_zero_of_stateSpaceDimensionAtMost
    {d : ℕ} {m : ℕ → ℝ} (hm : StateSpaceDimensionAtMost d m) :
    (momentHankelMatrix m (d + 1)).det = 0 := by
  obtain ⟨A, input, output, rfl⟩ := hm
  exact det_momentHankelMatrix_finiteStateSpaceResponse_succ_eq_zero A input output

/-- A fixed finite state dimension remains singular under pointwise convergence. -/
theorem det_momentHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimension_tendsto
    {d : ℕ} {m : ℕ → ℕ → ℝ} {target : ℕ → ℝ}
    (hm : ∀ j, StateSpaceDimensionAtMost d (m j))
    (hconv : Tendsto m atTop (nhds target)) :
    (momentHankelMatrix target (d + 1)).det = 0 := by
  have hmatrix : Tendsto
      (fun j ↦ momentHankelMatrix (m j) (d + 1)) atTop
      (nhds (momentHankelMatrix target (d + 1))) := by
    apply tendsto_pi_nhds.mpr
    intro r
    apply tendsto_pi_nhds.mpr
    intro c
    simpa [momentHankelMatrix] using
      (tendsto_pi_nhds.mp hconv) ((r : ℕ) + (c : ℕ))
  have hdet : Tendsto
      (fun j ↦ (momentHankelMatrix (m j) (d + 1)).det) atTop
      (nhds (momentHankelMatrix target (d + 1)).det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix
  have hzero : Tendsto
      (fun j ↦ (momentHankelMatrix (m j) (d + 1)).det) atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    exact Filter.Eventually.of_forall fun j ↦
      (det_momentHankelMatrix_succ_eq_zero_of_stateSpaceDimensionAtMost (hm j)).symm
  exact tendsto_nhds_unique hdet hzero

/-- Uniformly bounded hidden-state dimension remains impossible even when each finite observation
window may use a different realization. -/
theorem det_momentHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure
    {d : ℕ} {target : ℕ → ℝ}
    (h : FixedStateSpaceDimensionLocalClosure d target) :
    (momentHankelMatrix target (d + 1)).det = 0 := by
  have happ : ∀ j : ℕ, ∃ A : Matrix (Fin d) (Fin d) ℝ,
      ∃ input output : Fin d → ℝ,
      ∀ n : ℕ, n < j + 1 →
        dist (finiteStateSpaceResponse A input output n) (target n) <
          1 / ((j : ℝ) + 1) := by
    intro j
    exact h (j + 1) (1 / ((j : ℝ) + 1)) (by positivity)
  choose A input output happrox using happ
  let approx : ℕ → ℕ → ℝ :=
    fun j ↦ finiteStateSpaceResponse (A j) (input j) (output j)
  have hdim : ∀ j, StateSpaceDimensionAtMost d (approx j) := by
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
  exact det_momentHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimension_tendsto hdim hconv

/-- A single nonzero Hankel determinant rules out fixed-dimensional local state-space
approximation. -/
theorem not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero
    {d : ℕ} {target : ℕ → ℝ}
    (hdet : (momentHankelMatrix target (d + 1)).det ≠ 0) :
    ¬ FixedStateSpaceDimensionLocalClosure d target := by
  intro h
  exact hdet
    (det_momentHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure h)

/-- Every infinite-support moment clock escapes every uniformly bounded linear hidden-state
model. -/
theorem not_fixedStateSpaceDimensionLocalClosure_of_infiniteSupport
    {d : ℕ} {target : ℕ → ℝ} {μ : MeasureTheory.Measure ℝ}
    (hs : ∀ k, target k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, MeasureTheory.Integrable (fun x : ℝ ↦ (x : ℝ) ^ k) μ)
    (hμinf : ∀ F : Finset ℝ, 0 < μ {x : ℝ | x ∉ F}) :
    ¬ FixedStateSpaceDimensionLocalClosure d target := by
  apply not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero
  exact ne_of_gt (det_momentHankelMatrix_pos_of_infiniteSupport target hs hint hμinf (d + 1))

end

end HTGeometry
