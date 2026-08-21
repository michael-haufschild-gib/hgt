/-
# The two-qubit Pauli seed of the endpoint-complete path

The corpus's graph-state edge, recentred to zero energy sum and transported to the two-qubit Pauli
register, is an endpoint-complete seed *inside the bounded-weight Pauli span*: its Hamiltonian is a
traceless Hermitian matrix, hence a real combination of the fifteen nonidentity Pauli strings, and
its endpoint probe is a weight-one Pauli string whose spectral matrix has no zero off-diagonal
entry.

Main results:
* `exists_twoQubit_pauliSeed` — **the base case of the Pauli-path induction**.
-/
import GaloisForLFunctions.HTGeometry.TwoQubitSeedPauliTransport
import GaloisForLFunctions.HTGeometry.PauliChainSpan
import GaloisForLFunctions.HTGeometry.TracelessHermitianPauliSpan
import GaloisForLFunctions.HTGeometry.MaximallyProjectiveShift
import GaloisForLFunctions.HTGeometry.PhysicalObserverSpectralRealization
import GaloisForLFunctions.HTGeometry.WeakInteractionRecurrenceSingularityLaw
import GaloisForLFunctions.HTGeometry.HermitianCoveringProbe

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The seed's endpoint probe is supported at the second site. -/
theorem endpointProbe_mem_pauliSiteSpan (q : Fin 3) :
    Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv (twoQubitEndpointProbe true q)
      ∈ pauliSiteSpan 2 (Fin.last 1) := by
  have hprobe : twoQubitEndpointProbe true q
      = layerMatrixCoupling (1 : Matrix Bool Bool ℂ) (boolPauliOption (some q)) := by
    rw [twoQubitEndpointProbe, if_neg (by simp), boolPauli_eq_boolPauliOption]
  rw [hprobe, reindex_twoQubitConfigEquiv_layerMatrixCoupling_one]
  exact couple_field_mem_pauliSiteSpan 1 q

theorem realMatrixFamilyCombination_mem_pauliSiteSpan (c : Fin 3 → ℝ) :
    Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv
        (realMatrixFamilyCombination (twoQubitEndpointProbe true) c)
      ∈ pauliSiteSpan 2 (Fin.last 1) := by
  have hsum : Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv
      (realMatrixFamilyCombination (twoQubitEndpointProbe true) c)
      = ∑ j : Fin 3, (c j) •
        Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv
          (twoQubitEndpointProbe true j) := by
    ext x y
    rw [Matrix.sum_apply]
    show (∑ i, (c i : ℂ) * twoQubitEndpointProbe true i
        (twoQubitConfigEquiv.symm x) (twoQubitConfigEquiv.symm y)) = _
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [hsum]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem _ _ (endpointProbe_mem_pauliSiteSpan j)

theorem realMatrixFamilyCombination_mem_pauliSpan {q₀ : ℕ} (hq : 1 ≤ q₀) (c : Fin 3 → ℝ) :
    Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv
        (realMatrixFamilyCombination (twoQubitEndpointProbe true) c)
      ∈ pauliSpan 2 q₀ := by
  have hsum : Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv
      (realMatrixFamilyCombination (twoQubitEndpointProbe true) c)
      = ∑ j : Fin 3, (c j) •
        Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv
          (twoQubitEndpointProbe true j) := by
    ext x y
    rw [Matrix.sum_apply]
    show (∑ i, (c i : ℂ) * twoQubitEndpointProbe true i
        (twoQubitConfigEquiv.symm x) (twoQubitConfigEquiv.symm y)) = _
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [hsum]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem _ _ (endpointProbe_mem_pauliSpan hq j)

/-- **The base case of the Pauli-path induction.**  A two-qubit endpoint-complete seed whose
Hamiltonian lies in the nearest-neighbour Pauli span and whose probe is a one-site string at the
second site. -/
theorem exists_twoQubit_pauliSeed :
    ∃ (E : Bool × Bool → ℝ)
      (U : Matrix (FiniteQubitConfiguration (Fin 2)) (Bool × Bool) ℂ)
      (V : Matrix (FiniteQubitConfiguration (Fin 2)) (FiniteQubitConfiguration (Fin 2)) ℂ),
      MaximallyProjectiveEnergy E ∧
      (∑ i, E i) = 0 ∧
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      V.IsHermitian ∧ V ∈ pauliSiteSpan 2 (Fin.last 1) ∧
      (U * Matrix.diagonal (fun i => (E i : ℂ)) * Uᴴ) ∈ pauliChainSpan 2 ∧
      (∀ a b : Bool × Bool, a ≠ b → (Uᴴ * V * U) a b ≠ 0) := by
  classical
  obtain ⟨E₀, hE₀max, -⟩ :=
    exists_maximallyProjectiveEnergy_close_fintype (fun _ : Bool × Bool => 0) 1 (by norm_num)
  obtain ⟨E, hEmax, hEsum⟩ :
      ∃ E : Bool × Bool → ℝ, MaximallyProjectiveEnergy E ∧ (∑ i, E i) = 0 :=
    ⟨recentredEnergy E₀, maximallyProjectiveEnergy_recentredEnergy hE₀max,
      sum_recentredEnergy E₀⟩
  have hcover : ∀ a b : Bool × Bool, a ≠ b →
      ∃ q : Fin 3, twoQubitEndpointTransition true q a b ≠ 0 := by
    intro a b hab
    have hadj :
        (transitionFamilySupportGraph (twoQubitEndpointTransition true)).Adj a b := by
      rw [transitionFamilySupportGraph_twoQubitEndpointTransition]
      simpa using hab
    obtain ⟨q, hq⟩ := hadj
    refine ⟨q, ?_⟩
    intro hz
    exact hq.2 (by simp [hz])
  obtain ⟨coefficient, hcoefficient⟩ :=
    exists_realProbeCombination_ne_zero (twoQubitEndpointTransition true) hcover
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (FiniteQubitConfiguration (Fin 2)) (Bool × Bool) ℂ,
      U = twoQubitGraphBasis.submatrix ⇑twoQubitConfigEquiv.symm
        ⇑(Equiv.refl (Bool × Bool)) := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (FiniteQubitConfiguration (Fin 2))
      (FiniteQubitConfiguration (Fin 2)) ℂ,
      V = Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv
        (realMatrixFamilyCombination (twoQubitEndpointProbe true) coefficient) := ⟨_, rfl⟩
  have hUconj : Uᴴ = twoQubitGraphBasisᴴ.submatrix ⇑(Equiv.refl (Bool × Bool))
      ⇑twoQubitConfigEquiv.symm := by
    rw [hUdef]
    rfl
  have hUleft : Uᴴ * U = 1 := by
    rw [hUconj, hUdef, Matrix.submatrix_mul_equiv twoQubitGraphBasisᴴ twoQubitGraphBasis
      ⇑(Equiv.refl (Bool × Bool)) twoQubitConfigEquiv.symm ⇑(Equiv.refl (Bool × Bool)),
      twoQubitGraphBasis_conjTranspose_mul_self]
    rfl
  have hUright : U * Uᴴ = 1 := by
    rw [hUconj, hUdef, Matrix.submatrix_mul_equiv twoQubitGraphBasis twoQubitGraphBasisᴴ
      ⇑twoQubitConfigEquiv.symm (Equiv.refl (Bool × Bool)) ⇑twoQubitConfigEquiv.symm,
      twoQubitGraphBasis_mul_conjTranspose_self]
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · rw [if_neg h, if_neg fun hcon => h (twoQubitConfigEquiv.symm.injective hcon)]
  have hVherm : V.IsHermitian := by
    rw [hVdef]
    exact (realMatrixFamilyCombination_isHermitian (twoQubitEndpointProbe true)
      (twoQubitEndpointProbe_isHermitian true) coefficient).submatrix _
  have hVspan : V ∈ pauliSiteSpan 2 (Fin.last 1) := by
    rw [hVdef]
    exact realMatrixFamilyCombination_mem_pauliSiteSpan coefficient
  have hHspan : (U * Matrix.diagonal (fun i => (E i : ℂ)) * Uᴴ) ∈ pauliChainSpan 2 := by
    refine pauliSpan_two_le_pauliChainSpan 2 ?_
    refine mem_pauliSpan_of_isHermitian_of_trace_zero le_rfl ?_ ?_
    · refine Matrix.isHermitian_mul_mul_conjTranspose U ?_
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
      simp
    · rw [trace_unitary_conj_diagonal hUleft]
      rw [← Complex.ofReal_sum, hEsum]
      simp
  have hVtrans : Uᴴ * V * U
      = twoQubitGraphBasisᴴ *
        realMatrixFamilyCombination (twoQubitEndpointProbe true) coefficient *
        twoQubitGraphBasis := by
    rw [hUconj, hUdef, hVdef]
    rw [show (Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv
        (realMatrixFamilyCombination (twoQubitEndpointProbe true) coefficient))
        = (realMatrixFamilyCombination (twoQubitEndpointProbe true) coefficient).submatrix
            twoQubitConfigEquiv.symm twoQubitConfigEquiv.symm from rfl]
    rw [Matrix.submatrix_mul_equiv twoQubitGraphBasisᴴ
      (realMatrixFamilyCombination (twoQubitEndpointProbe true) coefficient)
      ⇑(Equiv.refl (Bool × Bool)) twoQubitConfigEquiv.symm ⇑twoQubitConfigEquiv.symm]
    rw [Matrix.submatrix_mul_equiv (twoQubitGraphBasisᴴ *
      realMatrixFamilyCombination (twoQubitEndpointProbe true) coefficient)
      twoQubitGraphBasis ⇑(Equiv.refl (Bool × Bool)) twoQubitConfigEquiv.symm
      ⇑(Equiv.refl (Bool × Bool))]
    rfl
  refine ⟨E, U, V, hEmax, hEsum, hUleft, hUright, hVherm, hVspan, hHspan, ?_⟩
  intro a b hab
  rw [hVtrans]
  have hcoord : realMatrixFamilyCombination (twoQubitEndpointTransition true) coefficient
      = twoQubitGraphBasisᴴ *
        realMatrixFamilyCombination (twoQubitEndpointProbe true) coefficient *
        twoQubitGraphBasis :=
    realMatrixFamilyCombination_coordinate twoQubitGraphBasis (twoQubitEndpointProbe true)
      (twoQubitEndpointTransition true) coefficient (fun _ => rfl)
  rw [← hcoord]
  have hc := hcoefficient a b hab
  rw [Matrix.sum_apply] at hc
  simpa [realMatrixFamilyCombination, Matrix.smul_apply] using hc

end GaloisForLFunctions.HTGeometry

end
