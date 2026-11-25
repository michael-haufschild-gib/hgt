import GaloisForLFunctions.RHTower.PiTranscendenceSetup
import GaloisForLFunctions.HTGeometry.AlgebraicClosureDerivationClosed
import GaloisForLFunctions.HTGeometry.SortedSpectrumGapExtremality
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.Discriminant

/-! # Algebraic specialization of the sorted energies of the Pauli chain -/

open Set MeasureTheory Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
noncomputable section

/-- Algebraic matrix entries give algebraic roots of the characteristic
relation, regardless of multiplicity. -/
theorem algebraic_matrix_root {F ι : Type*} [Field F] [Algebra F ℂ] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hm : ∀ i j, IsAlgebraic F (M i j)) {z : ℂ}
    (hz : matrixCharpolyRelation (M,z)=0) : IsAlgebraic F z := by
  let K := algebraicClosure F ℂ
  let A : Matrix ι ι K := fun i j => ⟨M i j,mem_algebraicClosure_iff.mpr (hm i j)⟩
  have hA : A.map (algebraMap K ℂ)=M := rfl
  have hr : IsAlgebraic K z := by
    refine ⟨A.charpoly,A.charpoly_monic.ne_zero,?_⟩
    rwa [Polynomial.aeval_def,Polynomial.eval₂_eq_eval_map,←Matrix.charpoly_map,hA,Matrix.eval_charpoly]
  exact mem_algebraicClosure_iff.mp (mem_algebraicClosure_of_isAlgebraic hr)

/-- The complex coefficients of the Pauli generators are Gaussian integers. -/
theorem pauli_entries_mem {F : Type*} [Field F] [Algebra F ℂ] (K : IntermediateField F ℂ)
    (hI : Complex.I∈K) (N : ℕ) (x : Fin (Fintype.card (ChainLabel N)) → ℝ)
    (hx : ∀ i, (x i:ℂ)∈K) (i l : Fin (2^N)) :
    spectralEnsembleMatrix (chainPauliFin N) x i l ∈ K := by
  simp only [spectralEnsembleMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply K.sum_mem
  intro a _
  apply K.mul_mem (hx a)
  obtain ⟨v,hv⟩ := chainPauliFin_entry_mem_gaussianInt N a i l
  rw [←hv]
  change (v:ℂ)∈K
  rw [GaussianInt.toComplex_def]
  exact K.add_mem (K.intCast_mem _) (K.mul_mem (K.intCast_mem _) hI)

theorem rational_pauli_energy (N : ℕ) (q : Fin (Fintype.card (ChainLabel N)) → ℚ) (j : Fin (2^N)) :
    IsAlgebraic ℚ ((sortedEnsembleSpectrum (chainPauliFin_isHermitian N) (fun i => (q i:ℝ)) j:ℝ):ℂ) := by
  let K := algebraicClosure ℚ ℂ
  apply algebraic_matrix_root _ _ (matrixCharpolyRelation_sortedEnsembleSpectrum (chainPauliFin_isHermitian N) _ j)
  intro i l
  apply mem_algebraicClosure_iff.mp
  apply pauli_entries_mem K (mem_algebraicClosure_iff.mpr GaloisForLFunctions.RHTower.isAlgebraic_I)
  intro a
  rw [Complex.ofReal_ratCast]
  exact K.ratCast_mem _

#print axioms rational_pauli_energy
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
