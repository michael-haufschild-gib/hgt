import GaloisForLFunctions.HTGeometry.MatrixWignerSmithReporterField
import GaloisForLFunctions.HTGeometry.ErlangWignerSmithPacket

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Set

noncomputable section

universe u

set_option maxHeartbeats 800000 in
/-- If one scattering entry is hypertranscendental, the fixed finite delay
panel contains a hypertranscendental scalar reporter. -/
theorem exists_hypertranscendental_matrixDelayPanelField
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (ι : F) (hι : ι * ι = -1)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hdet : S.det ≠ 0)
    {a b : Fin (n + 1)} (hSab : HypertranscendentalOver F (S a b)) :
    ∃ p : Fin (n + 1) × Fin (n + 1),
      HypertranscendentalOver F
        (matrixDelayPanelField ι (matrixWignerSmith ι S) p) := by
  let Q := matrixWignerSmith ι S
  let panel : Fin (n + 1) × Fin (n + 1) → E := matrixDelayPanelField ι Q
  by_contra hnone
  have hpanel : ∀ p, DifferentialAlgebraicOver F (panel p) := by
    intro p
    by_contra hp
    exact hnone ⟨p, hp⟩
  have hSOverPanel :=
    differentialAlgebraicOver_matrixWignerSmith_entries ι hι S hdet a b
  rw [← differentialAdjoin_matrixDelayPanelField_eq_entries ι hι Q] at hSOverPanel
  let M := differentialMatroid F E
  let z : Fin 1 → E := fun _ => algebraMap F E 0
  have hz : ∀ i, DifferentialAlgebraicOver F (z i) := by
    intro i
    exact differentialAlgebraicOver_algebraMap 0
  have hpanelZ : Set.range panel ⊆ M.closure (Set.range z) := by
    rintro _ ⟨p, rfl⟩
    apply (differentialMatroid_mem_closure_range_fintype_iff
      (F := F) (E := E) z (panel p)).2
    exact differentialAlgebraicOver_mono (hpanel p)
  have hSclosure : S a b ∈ M.closure (Set.range panel) :=
    (differentialMatroid_mem_closure_range_fintype_iff
      (F := F) (E := E) panel (S a b)).2 hSOverPanel
  have hSZclosure : S a b ∈ M.closure (Set.range z) := by
    have := M.closure_mono hpanelZ hSclosure
    simpa using this
  have hSOverZ : DifferentialAlgebraicOver
      (differentialAdjoin F (Set.range z)) (S a b) :=
    (differentialMatroid_mem_closure_range_fintype_iff
      (F := F) (E := E) z (S a b)).1 hSZclosure
  exact hSab (differentialAlgebraicOver_trans_fin_succ_narrow z hz
    (S a b) hSOverZ)

/-- Every positive-width Erlang realization of the complete finite panel
inherits a hypertranscendental scalar response whenever one scattering entry
is hypertranscendental. -/
theorem exists_hypertranscendental_erlangMatrixDelayReporter
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (ι : F) (hι : ι * ι = -1)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hdet : S.det ≠ 0)
    (ε : F) (hε : ε ≠ 0)
    (R : Fin (n + 1) × Fin (n + 1) → E)
    (hR : ∀ p, erlangThirdRecoveryElement ε (R p) =
      matrixDelayPanelField ι (matrixWignerSmith ι S) p)
    {a b : Fin (n + 1)} (hSab : HypertranscendentalOver F (S a b)) :
    ∃ p : Fin (n + 1) × Fin (n + 1), HypertranscendentalOver F (R p) := by
  obtain ⟨p, hp⟩ :=
    exists_hypertranscendental_matrixDelayPanelField ι hι S hdet hSab
  exact ⟨p,
    (hypertranscendentalOver_erlangThirdRecoveryElement_iff ε hε (hR p)).2 hp⟩

end

end GaloisForLFunctions.HTGeometry

