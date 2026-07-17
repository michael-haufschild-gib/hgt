import GaloisForLFunctions.HTGeometry.MatrixWignerSmithHTReporter

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Set

noncomputable section

universe u

/-- The physically normalized panel: diagonal channel states are unchanged,
while the two-channel superpositions are divided by their squared norm `2`. -/
def matrixNormalizedDelayPanelField
    {F E : Type u} [Field F] [Field E] [Algebra F E] {n : ℕ}
    (ι : F) (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    Fin (n + 1) × Fin (n + 1) → E := fun p =>
  if p.1 = p.2 then matrixDelayPanelField ι Q p
  else matrixDelayPanelField ι Q p / 2

@[simp]
theorem matrixNormalizedDelayPanelField_diagonal
    {F E : Type u} [Field F] [Field E] [Algebra F E] {n : ℕ}
    (ι : F) (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (j : Fin (n + 1)) :
    matrixNormalizedDelayPanelField ι Q (j, j) = Q j j := by
  simp [matrixNormalizedDelayPanelField]

theorem matrixNormalizedDelayPanelField_offDiagonal
    {F E : Type u} [Field F] [Field E] [Algebra F E] {n : ℕ}
    (ι : F) (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (p : Fin (n + 1) × Fin (n + 1)) (hp : p.1 ≠ p.2) :
    matrixNormalizedDelayPanelField ι Q p =
      matrixDelayPanelField ι Q p / 2 := by
  simp [matrixNormalizedDelayPanelField, hp]

theorem matrixNormalizedDelayPanelField_mem_panel_differentialAdjoin
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E]
    {n : ℕ} (ι : F)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (p : Fin (n + 1) × Fin (n + 1)) :
    matrixNormalizedDelayPanelField ι Q p ∈
      differentialAdjoin F (Set.range (matrixDelayPanelField ι Q)) := by
  let B := differentialAdjoin F (Set.range (matrixDelayPanelField ι Q))
  have hp : matrixDelayPanelField ι Q p ∈ B :=
    subset_differentialAdjoin F _ ⟨p, rfl⟩
  by_cases hdiag : p.1 = p.2
  · simpa [matrixNormalizedDelayPanelField, hdiag] using hp
  · rw [matrixNormalizedDelayPanelField, if_neg hdiag]
    exact B.div_mem hp (B.natCast_mem 2)

theorem matrixDelayPanelField_mem_normalized_differentialAdjoin
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E]
    [CharZero E] {n : ℕ} (ι : F)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (p : Fin (n + 1) × Fin (n + 1)) :
    matrixDelayPanelField ι Q p ∈
      differentialAdjoin F (Set.range (matrixNormalizedDelayPanelField ι Q)) := by
  let B := differentialAdjoin F (Set.range (matrixNormalizedDelayPanelField ι Q))
  have hp : matrixNormalizedDelayPanelField ι Q p ∈ B :=
    subset_differentialAdjoin F _ ⟨p, rfl⟩
  by_cases hdiag : p.1 = p.2
  · simpa [matrixNormalizedDelayPanelField, hdiag] using hp
  · have hscale : matrixDelayPanelField ι Q p =
        (2 : E) * matrixNormalizedDelayPanelField ι Q p := by
      rw [matrixNormalizedDelayPanelField, if_neg hdiag]
      field_simp
    rw [hscale]
    exact B.mul_mem (B.natCast_mem 2) hp

/-- Dividing the off-diagonal reporters by the known normalization constant
does not change the generated differential field. -/
theorem differentialAdjoin_matrixNormalizedDelayPanelField_eq
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (ι : F)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    differentialAdjoin F (Set.range (matrixNormalizedDelayPanelField ι Q)) =
      differentialAdjoin F (Set.range (matrixDelayPanelField ι Q)) := by
  apply le_antisymm
  · apply differentialAdjoin_le F
    · rintro _ ⟨p, rfl⟩
      exact matrixNormalizedDelayPanelField_mem_panel_differentialAdjoin ι Q p
    · exact derivationClosed_differentialAdjoin F _
  · apply differentialAdjoin_le F
    · rintro _ ⟨p, rfl⟩
      exact matrixDelayPanelField_mem_normalized_differentialAdjoin ι Q p
    · exact derivationClosed_differentialAdjoin F _

theorem differentialAdjoin_matrixNormalizedDelayPanelField_eq_entries
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (ι : F) (hι : ι * ι = -1)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    differentialAdjoin F (Set.range (matrixNormalizedDelayPanelField ι Q)) =
      differentialAdjoin F
        (Set.range fun p : Fin (n + 1) × Fin (n + 1) => Q p.1 p.2) := by
  rw [differentialAdjoin_matrixNormalizedDelayPanelField_eq,
    differentialAdjoin_matrixDelayPanelField_eq_entries ι hι]

theorem exists_hypertranscendental_matrixNormalizedDelayPanelField
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (ι : F) (hι : ι * ι = -1)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hdet : S.det ≠ 0)
    {a b : Fin (n + 1)} (hSab : HypertranscendentalOver F (S a b)) :
    ∃ p : Fin (n + 1) × Fin (n + 1),
      HypertranscendentalOver F
        (matrixNormalizedDelayPanelField ι (matrixWignerSmith ι S) p) := by
  obtain ⟨p, hp⟩ :=
    exists_hypertranscendental_matrixDelayPanelField ι hι S hdet hSab
  refine ⟨p, ?_⟩
  by_cases hdiag : p.1 = p.2
  · simpa [matrixNormalizedDelayPanelField, hdiag] using hp
  · intro hnormalized
    apply hp
    have htwo : DifferentialAlgebraicOver F (2 : E) := by
      simpa only [map_ofNat] using
        differentialAlgebraicOver_algebraMap (F := F) (E := E) (2 : F)
    have hscale : matrixDelayPanelField ι (matrixWignerSmith ι S) p =
        (2 : E) * matrixNormalizedDelayPanelField ι (matrixWignerSmith ι S) p := by
      rw [matrixNormalizedDelayPanelField, if_neg hdiag]
      field_simp
    rw [hscale]
    exact differentialAlgebraicOver_mul htwo hnormalized

theorem exists_hypertranscendental_erlangMatrixNormalizedDelayReporter
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (ι : F) (hι : ι * ι = -1)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hdet : S.det ≠ 0)
    (ε : F) (hε : ε ≠ 0)
    (R : Fin (n + 1) × Fin (n + 1) → E)
    (hR : ∀ p, erlangThirdRecoveryElement ε (R p) =
      matrixNormalizedDelayPanelField ι (matrixWignerSmith ι S) p)
    {a b : Fin (n + 1)} (hSab : HypertranscendentalOver F (S a b)) :
    ∃ p : Fin (n + 1) × Fin (n + 1), HypertranscendentalOver F (R p) := by
  obtain ⟨p, hp⟩ :=
    exists_hypertranscendental_matrixNormalizedDelayPanelField ι hι S hdet hSab
  exact ⟨p,
    (hypertranscendentalOver_erlangThirdRecoveryElement_iff ε hε (hR p)).2 hp⟩

end

end GaloisForLFunctions.HTGeometry

