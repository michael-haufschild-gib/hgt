import GaloisForLFunctions.HTGeometry.MatrixWignerSmithNormalizedReporter
import GaloisForLFunctions.HTGeometry.ProjectiveReciprocalWignerSmithTomographyLaw

/-!
# Wigner--Smith trace-gauge tomography

Full normalized delay tomography and reciprocal projective tomography were previously separate.
The canonical traceless decomposition identifies their exact field gap: after scattering entries
are adjoined, the full panel is the projective reciprocal panel plus one scalar trace gauge.
-/

open scoped Differential Matroid Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Set

noncomputable section

universe u

private theorem differentialAdjoin_union_right_congr
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    {s t v : Set E}
    (h : differentialAdjoin F s = differentialAdjoin F t) :
    differentialAdjoin F (s ∪ v) = differentialAdjoin F (t ∪ v) := by
  have hsv : differentialAdjoin F s ≤ differentialAdjoin F (t ∪ v) := by
    rw [h]
    apply differentialAdjoin_le F
    · exact fun x hx ↦ subset_differentialAdjoin F (t ∪ v) (Or.inl hx)
    · exact derivationClosed_differentialAdjoin F _
  have htv : differentialAdjoin F t ≤ differentialAdjoin F (s ∪ v) := by
    rw [← h]
    apply differentialAdjoin_le F
    · exact fun x hx ↦ subset_differentialAdjoin F (s ∪ v) (Or.inl hx)
    · exact derivationClosed_differentialAdjoin F _
  apply le_antisymm
  · apply differentialAdjoin_le F
    · rintro x (hx | hx)
      · exact hsv (subset_differentialAdjoin F s hx)
      · exact subset_differentialAdjoin F (t ∪ v) (Or.inr hx)
    · exact derivationClosed_differentialAdjoin F _
  · apply differentialAdjoin_le F
    · rintro x (hx | hx)
      · exact htv (subset_differentialAdjoin F t hx)
      · exact subset_differentialAdjoin F (s ∪ v) (Or.inr hx)
    · exact derivationClosed_differentialAdjoin F _

theorem differentialAdjoin_base_union_matrixEntries_eq_traceless_trace
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {n : ℕ} (base : Set E)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    differentialAdjoin F
        (base ∪ Set.range (fun p : Fin (n + 1) × Fin (n + 1) ↦ Q p.1 p.2)) =
      differentialAdjoin F
        ((base ∪ Set.range (fun p : Fin (n + 1) × Fin (n + 1) ↦
          matrixTracelessPartField Q p.1 p.2)) ∪ {Matrix.trace Q}) := by
  let qSet : Set E :=
    Set.range (fun p : Fin (n + 1) × Fin (n + 1) ↦ Q p.1 p.2)
  let q₀Set : Set E :=
    Set.range (fun p : Fin (n + 1) × Fin (n + 1) ↦
      matrixTracelessPartField Q p.1 p.2)
  let BQ := differentialAdjoin F (base ∪ qSet)
  let B₀ := differentialAdjoin F ((base ∪ q₀Set) ∪ {Matrix.trace Q})
  have hbaseQ : ∀ x ∈ base, x ∈ BQ := fun x hx ↦
    subset_differentialAdjoin F (base ∪ qSet) (Or.inl hx)
  have hbase₀ : ∀ x ∈ base, x ∈ B₀ := fun x hx ↦
    subset_differentialAdjoin F ((base ∪ q₀Set) ∪ {Matrix.trace Q})
      (Or.inl (Or.inl hx))
  have hqQ : ∀ i j, Q i j ∈ BQ := fun i j ↦
    subset_differentialAdjoin F (base ∪ qSet) (Or.inr ⟨(i, j), rfl⟩)
  have hq₀₀ : ∀ i j, matrixTracelessPartField Q i j ∈ B₀ := fun i j ↦
    subset_differentialAdjoin F ((base ∪ q₀Set) ∪ {Matrix.trace Q})
      (Or.inl (Or.inr ⟨(i, j), rfl⟩))
  have htrace₀ : Matrix.trace Q ∈ B₀ :=
    subset_differentialAdjoin F ((base ∪ q₀Set) ∪ {Matrix.trace Q})
      (Or.inr (Set.mem_singleton _))
  have htraceQ : Matrix.trace Q ∈ BQ := by
    rw [Matrix.trace]
    exact BQ.sum_mem fun i _ ↦ hqQ i i
  have hcard₀ : (n + 1 : E) ∈ B₀ := by
    simpa only [Nat.cast_add, Nat.cast_one] using B₀.natCast_mem (n + 1)
  have hcardQ : (n + 1 : E) ∈ BQ := by
    simpa only [Nat.cast_add, Nat.cast_one] using BQ.natCast_mem (n + 1)
  have hgauge₀ : Matrix.trace Q / (n + 1 : E) ∈ B₀ :=
    B₀.div_mem htrace₀ hcard₀
  have hnegGaugeQ : -(Matrix.trace Q / (n + 1 : E)) ∈ BQ :=
    BQ.neg_mem (BQ.div_mem htraceQ hcardQ)
  apply le_antisymm
  · apply differentialAdjoin_le F
    · rintro x (hx | hx)
      · exact hbase₀ x hx
      · rcases hx with ⟨⟨i, j⟩, rfl⟩
        change Q i j ∈ B₀
        rw [matrix_eq_tracelessPartField_add_scalar Q]
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        by_cases hij : i = j
        · subst j
          simp only [if_pos, mul_one]
          exact B₀.add_mem (hq₀₀ i i) hgauge₀
        · simp only [if_neg hij, mul_zero, add_zero]
          exact hq₀₀ i j
    · exact derivationClosed_differentialAdjoin F _
  · apply differentialAdjoin_le F
    · rintro x (hx | hx)
      · rcases hx with hx | hx
        · exact hbaseQ x hx
        · rcases hx with ⟨⟨i, j⟩, rfl⟩
          change matrixTracelessPartField Q i j ∈ BQ
          rw [matrixTracelessPartField]
          simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
          by_cases hij : i = j
          · subst j
            simp only [if_pos, mul_one]
            exact BQ.add_mem (hqQ i i) hnegGaugeQ
          · simp only [if_neg hij, mul_zero, add_zero]
            exact hqQ i j
      · rw [Set.mem_singleton_iff] at hx
        subst x
        exact htraceQ
    · exact derivationClosed_differentialAdjoin F _

/-- **Wigner--Smith trace-gauge tomography law.**  After adjoining the scattering entries, the
physically normalized full delay panel generates exactly the projective reciprocal tangent
reporter together with one scalar, the trace of the full Wigner--Smith connection. -/
theorem differentialAdjoin_normalizedDelay_eq_projectiveReciprocal_traceGauge
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero E] {n : ℕ}
    (iota : F) (hiota : iota * iota = -1)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hS : S.IsSymm) (hdet : S.det ≠ 0) :
    differentialAdjoin F
        (Set.range (fun p : Fin (n + 1) × Fin (n + 1) ↦ S p.1 p.2) ∪
          Set.range (matrixNormalizedDelayPanelField iota (matrixWignerSmith iota S))) =
      differentialAdjoin F
        ((Set.range (fun p : Fin (n + 1) × Fin (n + 1) ↦ S p.1 p.2) ∪
          Set.range (symmetricMatrixReporter
            (projectiveReciprocalWignerSmithTangent iota S)
            (projectiveReciprocalWignerSmithTangent_isSymm iota S hS hdet))) ∪
          {Matrix.trace (matrixWignerSmith iota S)}) := by
  let sSet : Set E :=
    Set.range (fun p : Fin (n + 1) × Fin (n + 1) ↦ S p.1 p.2)
  let nSet : Set E :=
    Set.range (matrixNormalizedDelayPanelField iota (matrixWignerSmith iota S))
  let qSet : Set E :=
    Set.range (fun p : Fin (n + 1) × Fin (n + 1) ↦
      matrixWignerSmith iota S p.1 p.2)
  let q₀Set : Set E :=
    Set.range (fun p : Fin (n + 1) × Fin (n + 1) ↦
      matrixTracelessPartField (matrixWignerSmith iota S) p.1 p.2)
  let rSet : Set E :=
    Set.range (symmetricMatrixReporter
      (projectiveReciprocalWignerSmithTangent iota S)
      (projectiveReciprocalWignerSmithTangent_isSymm iota S hS hdet))
  have hnq : differentialAdjoin F nSet = differentialAdjoin F qSet := by
    exact differentialAdjoin_matrixNormalizedDelayPanelField_eq_entries
      iota hiota (matrixWignerSmith iota S)
  have hsnq : differentialAdjoin F (sSet ∪ nSet) =
      differentialAdjoin F (sSet ∪ qSet) := by
    simpa [Set.union_comm] using
      differentialAdjoin_union_right_congr (v := sSet) hnq
  have hdecomp : differentialAdjoin F (sSet ∪ qSet) =
      differentialAdjoin F
        ((sSet ∪ q₀Set) ∪ {Matrix.trace (matrixWignerSmith iota S)}) := by
    exact differentialAdjoin_base_union_matrixEntries_eq_traceless_trace
      sSet (matrixWignerSmith iota S)
  have hrq₀ : differentialAdjoin F (sSet ∪ rSet) =
      differentialAdjoin F (sSet ∪ q₀Set) := by
    exact differentialAdjoin_projectiveReciprocalWignerSmithReporter_eq_entries
      iota S hS hdet
  have hrq₀trace :
      differentialAdjoin F
          ((sSet ∪ rSet) ∪ {Matrix.trace (matrixWignerSmith iota S)}) =
        differentialAdjoin F
          ((sSet ∪ q₀Set) ∪ {Matrix.trace (matrixWignerSmith iota S)}) :=
    differentialAdjoin_union_right_congr hrq₀
  change differentialAdjoin F (sSet ∪ nSet) =
    differentialAdjoin F
      ((sSet ∪ rSet) ∪ {Matrix.trace (matrixWignerSmith iota S)})
  exact hsnq.trans (hdecomp.trans hrq₀trace.symm)

end

end GaloisForLFunctions.HTGeometry
