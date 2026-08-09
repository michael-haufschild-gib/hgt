import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarReindex

/-!
# A Hermitian idempotent of unit trace is a unitary conjugate of one coordinate

Every Hermitian idempotent matrix has eigenvalues in `{0, 1}`; if its trace is one, exactly one
eigenvalue is one.  Diagonalizing therefore writes the matrix as `K E_jj K*` for a unitary `K` and
a coordinate `j`, so pairing it against any observable is the `(j, j)` entry of the conjugated
observable.  This is the statement that a pure state's expectation values are those of a prepared
coordinate state, and it is exactly what turns a product stabilizer state into an admissible
preparation for the Haar benchmark.
-/

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every eigenvalue of a Hermitian idempotent is `0` or `1`. -/
theorem hermitianEigenvalues_sq_eq_self_of_mul_self_eq_self
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hmul : A * A = A) (i : ι) :
    (hA.eigenvalues i) ^ 2 = hA.eigenvalues i := by
  let K := hA.eigenvectorUnitary
  have hdiag := congrArg
    (fun X : Matrix ι ι ℂ => ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) (star K)) X) hmul
  rw [map_mul, hA.conjStarAlgAut_star_eigenvectorUnitary] at hdiag
  have hii := congrArg (fun M : Matrix ι ι ℂ => M i i) hdiag
  simp only [Matrix.mul_apply, Matrix.diagonal_apply] at hii
  rw [Finset.sum_eq_single i] at hii
  · rw [pow_two]
    simp only [Function.comp_apply, if_true] at hii
    exact_mod_cast hii
  · intro k _hk hki
    simp [hki]
  · simp

/-- A Hermitian idempotent of unit trace has exactly one eigenvalue equal to one. -/
theorem exists_unique_eigenvalue_one_of_isIdempotent_trace_one
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hmul : A * A = A) (htr : A.trace = 1) :
    ∃ j : ι, hA.eigenvalues j = 1 ∧ ∀ i, i ≠ j → hA.eigenvalues i = 0 := by
  classical
  have hsum : ∑ i, hA.eigenvalues i = 1 := by
    have h := hA.trace_eq_sum_eigenvalues
    rw [htr] at h
    have hre := congrArg Complex.re h
    simp only [Complex.one_re, Complex.re_sum] at hre
    norm_num at hre
    exact hre.symm
  have hzeroone : ∀ i, hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
    intro i
    have h := hermitianEigenvalues_sq_eq_self_of_mul_self_eq_self hA hmul i
    have : hA.eigenvalues i * (hA.eigenvalues i - 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by linarith)
  set S : Finset ι := Finset.univ.filter fun i => hA.eigenvalues i = 1 with hS
  have hsplit : ∑ i, hA.eigenvalues i = (S.card : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => hA.eigenvalues i = 1) hA.eigenvalues]
    have hone : ∑ i ∈ S, hA.eigenvalues i = (S.card : ℝ) := by
      rw [hS]
      rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2]
      simp
    have hnot : ∑ i ∈ Finset.univ.filter (fun i => ¬ hA.eigenvalues i = 1),
        hA.eigenvalues i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      exact (hzeroone i).resolve_right (Finset.mem_filter.mp hi).2
    rw [hone, hnot, add_zero]
  have hcard : S.card = 1 := by
    have : (S.card : ℝ) = 1 := by rw [← hsplit, hsum]
    exact_mod_cast this
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  refine ⟨j, ?_, ?_⟩
  · have : j ∈ S := by rw [hj]; exact Finset.mem_singleton_self j
    exact (Finset.mem_filter.mp this).2
  · intro i hij
    refine (hzeroone i).resolve_right fun hcon => ?_
    have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcon⟩
    rw [hj, Finset.mem_singleton] at this
    exact hij this

/-- **A pure state's expectations are those of a prepared coordinate state.**  A Hermitian
idempotent of unit trace pairs with every observable as one diagonal entry of the observable
conjugated by a fixed unitary. -/
theorem exists_unitary_trace_mul_eq_conj_entry
    {ρ : Matrix ι ι ℂ} (hherm : ρ.IsHermitian) (hidem : ρ * ρ = ρ) (htr : ρ.trace = 1) :
    ∃ (K : Matrix ι ι ℂ) (j : ι), K ∈ Matrix.unitaryGroup ι ℂ ∧
      ∀ A : Matrix ι ι ℂ, Matrix.trace (ρ * A) = (star K * A * K) j j := by
  classical
  obtain ⟨j, hj1, hj0⟩ := exists_unique_eigenvalue_one_of_isIdempotent_trace_one hherm hidem htr
  refine ⟨(hherm.eigenvectorUnitary : Matrix ι ι ℂ), j, hherm.eigenvectorUnitary.2, ?_⟩
  intro A
  have hspec : ρ = (hherm.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hherm.eigenvalues i : ℂ)) *
      star (hherm.eigenvectorUnitary : Matrix ι ι ℂ) := by
    convert hherm.spectral_theorem using 1
    rfl
  set K : Matrix ι ι ℂ := (hherm.eigenvectorUnitary : Matrix ι ι ℂ) with hK
  set D : Matrix ι ι ℂ := Matrix.diagonal fun i => (hherm.eigenvalues i : ℂ) with hD
  have hcyc : Matrix.trace (ρ * A) = Matrix.trace (D * (star K * A * K)) := by
    rw [hspec]
    rw [show K * D * star K * A = K * (D * (star K * A)) by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hcyc, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, hD, Matrix.diagonal_apply]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk])
    (by simp)]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, hj1]
    simp
  · intro i _ hij
    rw [if_pos rfl, hj0 i hij]
    simp
  · simp

end

end GaloisForLFunctions.HTGeometry
