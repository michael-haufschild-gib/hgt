import GaloisForLFunctions.RHTower.VonMangoldtSuccessorDiracKreinEdge
import GaloisForLFunctions.RHTower.VonMangoldtSuccessorTransportInertia
import GaloisForLFunctions.RHTower.VonMangoldtBivariateMarginalTraceLock

/-!
# Von Mangoldt Dirac--Krein inertia/marginal universality

The explicit source-edge exchange Gram is exactly the successor principal-relative moment matrix.
Transporting terminal results back across that realization gives its full positive, negative, and
null signature, unbounded negative index, and the impossibility of sharing one fixed source
marginal across consecutive jet sections.
-/

open scoped BigOperators Matrix

namespace RHTower

noncomputable section

/-- Exact negative index of the source-edge Dirac--Krein realization. -/
theorem sigNeg_finiteVonMangoldtSuccessorDiracKreinGram (M : ℕ) :
    sigNeg
        (finiteVonMangoldtSuccessorDiracKreinGram
          M (M + 1)).toQuadraticForm' =
      {i | vonMangoldtSuccessorTransportMass M i < 0}.ncard := by
  rw [finiteVonMangoldtSuccessorDiracKreinGram_eq]
  exact sigNeg_finiteVonMangoldtSuccessorPrincipalRelativeMatrix M

/-- Exact positive index of the source-edge Dirac--Krein realization. -/
theorem sigPos_finiteVonMangoldtSuccessorDiracKreinGram (M : ℕ) :
    sigPos
        (finiteVonMangoldtSuccessorDiracKreinGram
          M (M + 1)).toQuadraticForm' =
      {i | 0 < vonMangoldtSuccessorTransportMass M i}.ncard := by
  rw [finiteVonMangoldtSuccessorDiracKreinGram_eq]
  exact sigPos_finiteVonMangoldtSuccessorPrincipalRelativeMatrix M

/-- Exact null index of the source-edge Dirac--Krein realization. -/
theorem finrank_radical_finiteVonMangoldtSuccessorDiracKreinGram (M : ℕ) :
    Module.finrank ℝ
        (finiteVonMangoldtSuccessorDiracKreinGram
          M (M + 1)).toQuadraticForm'.radical =
      {i | vonMangoldtSuccessorTransportMass M i = 0}.ncard := by
  rw [finiteVonMangoldtSuccessorDiracKreinGram_eq]
  exact finrank_radical_finiteVonMangoldtSuccessorPrincipalRelativeMatrix M

/-- Every nonempty full-jet source-edge realization has a negative direction. -/
theorem sigNeg_finiteVonMangoldtSuccessorDiracKreinGram_pos
    (M : ℕ) (hM : 0 < M) :
    0 < sigNeg
        (finiteVonMangoldtSuccessorDiracKreinGram
          M (M + 1)).toQuadraticForm' := by
  rw [finiteVonMangoldtSuccessorDiracKreinGram_eq]
  exact sigNeg_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_pos M hM

/-- Source-edge Dirac--Krein negative index is unbounded over finite apertures. -/
theorem sigNeg_finiteVonMangoldtSuccessorDiracKreinGram_unbounded
    (K : ℕ) :
    ∃ M, K < sigNeg
        (finiteVonMangoldtSuccessorDiracKreinGram
          M (M + 1)).toQuadraticForm' := by
  obtain ⟨M, hM⟩ :=
    sigNeg_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_unbounded K
  refine ⟨M, ?_⟩
  rw [finiteVonMangoldtSuccessorDiracKreinGram_eq]
  exact hM

/-- Consecutive source-edge Dirac--Krein sections cannot share a fixed coordinate marginal. -/
theorem not_exists_two_bivariateMarginals_finiteVonMangoldtSuccessorDiracKrein
    {P : Type*} [Fintype P]
    (M N : ℕ) (hM : 0 < M) (B : Matrix P P ℝ) :
    ¬ ((∃ C : Matrix (P × Fin N) (P × Fin N) ℝ,
          GaloisForLFunctions.HTGeometry.bivariateJetMarginal C =
            finiteVonMangoldtSuccessorDiracKreinGram M N ∧
          GaloisForLFunctions.HTGeometry.bivariateSourceMarginal C = B) ∧
        (∃ C : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ,
          GaloisForLFunctions.HTGeometry.bivariateJetMarginal C =
            finiteVonMangoldtSuccessorDiracKreinGram M (N + 1) ∧
          GaloisForLFunctions.HTGeometry.bivariateSourceMarginal C = B)) := by
  simpa only [finiteVonMangoldtSuccessorDiracKreinGram_eq] using
    not_exists_two_bivariateMarginals_finiteVonMangoldtSuccessor M N hM B

end

end RHTower
