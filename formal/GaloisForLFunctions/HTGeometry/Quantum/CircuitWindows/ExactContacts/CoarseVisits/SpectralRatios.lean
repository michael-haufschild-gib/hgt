import GaloisForLFunctions.HTGeometry.SpectralTorusContinuousCircuitHardnessLaw
import GaloisForLFunctions.HTGeometry.StateFieldTrdeg
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! # Transcendence rank of a circuit spectrum in an arbitrary basis -/

open Matrix Set
namespace GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits
noncomputable section

private theorem algebraic_spectral_point {I : Type} [Fintype I] [DecidableEq I]
    (E : IntermediateField ℚ ℂ) (M : Matrix I I ℂ) (hm : ∀ i j, M i j ∈ E)
    {z : ℂ} (hz : z ∈ spectrum ℂ M) : IsAlgebraic E z := by
  let A : Matrix I I E := fun i j => ⟨M i j,hm i j⟩
  have heq : A.map (algebraMap E ℂ)=M := rfl
  refine ⟨A.charpoly,A.charpoly_monic.ne_zero,?_⟩
  have h := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
  rw [←heq,Matrix.charpoly_map] at h
  simpa only [Polynomial.IsRoot,Polynomial.eval_map,Polynomial.aeval_def] using h

/-- A circuit with j physical gates carries at most 16j algebraically
independent ratios of eigenvalues. Passing to any basis and multiplying
every eigenvalue by the same phase both preserve the ratios. -/
theorem spectral_ratio_gate_bound {N : ℕ} (C : TwoQubitCircuit N)
    {I : Type} [Fintype I] (a : ℂ) (ha : a ∈ spectrum ℂ C.eval.val)
    (f : I → ℂ) (hf : ∀ i, f i ∈ spectrum ℂ C.eval.val)
    (h : AlgebraicIndependent ℚ (fun i => f i/a)) : Fintype.card I ≤ C.gateCount*16 := by
  obtain ⟨g,hg⟩ := C.exists_sixteenGenerators_eval_entries (K:=ℚ)
  let E := IntermediateField.adjoin ℚ (range g)
  let F := (algebraicClosure E ℂ).restrictScalars ℚ
  have incl : Algebra.adjoin ℚ (range g) ≤ E.toSubalgebra :=
    Algebra.adjoin_le (IntermediateField.subset_adjoin ℚ (range g))
  have hroot (z : ℂ) (hz : z ∈ spectrum ℂ C.eval.val) : z ∈ F :=
    mem_algebraicClosure_iff.mpr (algebraic_spectral_point E _ (fun i j => incl (hg i j)) hz)
  let y (i : I) : F := ⟨f i/a,F.div_mem (hroot _ (hf i)) (hroot _ ha)⟩
  have hy : AlgebraicIndependent ℚ y := AlgebraicIndependent.of_comp F.val h
  have hh := hy.cardinalMk_le_trdeg.trans (trdeg_algebraicClosure_adjoin_range_le (K:=ℚ) g)
  simpa only [Cardinal.mk_fintype,Fintype.card_fin,Nat.cast_le] using hh

#print axioms spectral_ratio_gate_bound
end
end GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits
