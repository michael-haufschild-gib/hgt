import GaloisForLFunctions.HTGeometry.HistogramCentralizerDimension

/-!
# Joint commutants recover finite observation dependencies

A family of diagonal observations partitions coordinates by their joint
values. Its commutant consists exactly of matrices supported inside those
blocks. A further observation is determined precisely when this commutant
commutes with its diagonal matrix. Failed recovery has a single matrix-unit
witness. This realizes Proposition 5.1 of arXiv:2610.33092 directly in the
finite observation and histogram-centralizer setting.
-/

namespace GaloisForLFunctions.HilbertMetric.Observation

open HTGeometry Matrix
open scoped BigOperators
noncomputable section

/-- Matrices commuting with every selected diagonal observation. -/
def jointCommutant {m n : ℕ} (E : Fin m → Fin n → ℂ) (S : Set (Fin m)) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  ⨅ a ∈ S, commutantSubmodule (diagonal (E a))

/-- Labels whose values are determined by the selected observation tuple. -/
def determinedLabels {m n : ℕ} (E : Fin m → Fin n → ℂ) (S : Set (Fin m)) :
    Set (Fin m) :=
  {b | ∀ i j, (∀ a ∈ S, E a i = E a j) → E b i = E b j}

/-- Joint commutation is an entrywise support condition on observation fibres. -/
theorem mem_jointCommutant_iff {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) (X : Matrix (Fin n) (Fin n) ℂ) :
    X ∈ jointCommutant E S ↔
      ∀ i j, (∃ a ∈ S, E a i ≠ E a j) → X i j = 0 := by
  simp only [jointCommutant, Submodule.mem_iInf, mem_commutantSubmodule_diagonal]
  constructor
  · rintro h i j ⟨a, ha, hij⟩
    exact h a ha i j hij
  · intro h a ha i j hij
    exact h i j ⟨a, ha, hij⟩

/-- Matrix units inside one observation fibre are exactly the elementary joint symmetries. -/
theorem matrixUnit_mem_joint_iff {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) (i j : Fin n) :
    Matrix.stdBasis ℂ (Fin n) (Fin n) (i, j) ∈ jointCommutant E S ↔
      ∀ a ∈ S, E a i = E a j := by
  rw [mem_jointCommutant_iff]
  constructor
  · intro h a ha
    by_contra hij
    have hz := h i j ⟨a, ha, hij⟩
    simpa [stdBasis_apply'] using hz
  · intro h k l hsep
    rw [stdBasis_apply']
    apply if_neg
    rintro ⟨rfl, rfl⟩
    obtain ⟨a, ha, hne⟩ := hsep
    exact hne (h a ha)

/-- Inclusion of commutants is equivalent to exact determination of an observation. -/
theorem jointCommutant_le_iff {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) (b : Fin m) :
    jointCommutant E S ≤ commutantSubmodule (diagonal (E b)) ↔
      b ∈ determinedLabels E S := by
  constructor
  · intro h i j hij
    have hu := h ((matrixUnit_mem_joint_iff E S i j).mpr hij)
    rw [mem_commutantSubmodule_diagonal] at hu
    by_contra hne
    have hz := hu i j hne
    simpa [stdBasis_apply'] using hz
  · intro hb X hX
    rw [mem_commutantSubmodule_diagonal]
    intro i j hij
    apply (mem_jointCommutant_iff E S X).mp hX i j
    by_contra h
    push Not at h
    exact hij (hb i j h)

/-- Every failure of recovery has a rank-one matrix-unit obstruction. -/
theorem recovery_failure_iff_matrixUnit {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) (b : Fin m) :
    b ∉ determinedLabels E S ↔ ∃ i j,
      Matrix.stdBasis ℂ (Fin n) (Fin n) (i, j) ∈ jointCommutant E S ∧
      Matrix.stdBasis ℂ (Fin n) (Fin n) (i, j) ∉
        commutantSubmodule (diagonal (E b)) := by
  constructor
  · intro h
    change ¬ (∀ i j, (∀ a ∈ S, E a i = E a j) → E b i = E b j) at h
    push Not at h
    obtain ⟨i, j, hij, hb⟩ := h
    refine ⟨i, j, (matrixUnit_mem_joint_iff E S i j).mpr hij, ?_⟩
    intro hu
    have hz := mem_commutantSubmodule_diagonal.mp hu i j hb
    simpa [stdBasis_apply'] using hz
  · rintro ⟨i, j, hij, hb⟩ h
    exact hb ((jointCommutant_le_iff E S b).mpr h hij)

theorem subset_determinedLabels {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) : S ⊆ determinedLabels E S :=
  fun _ hb _ _ h => h _ hb

/-- Adding all recoverable labels leaves the full matrix commutant unchanged. -/
theorem jointCommutant_determined {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) : jointCommutant E (determinedLabels E S) = jointCommutant E S := by
  apply le_antisymm
  · intro X hX
    simp only [jointCommutant, Submodule.mem_iInf] at hX ⊢
    exact fun a ha => hX a (subset_determinedLabels E S ha)
  · intro X hX
    simp only [jointCommutant, Submodule.mem_iInf]
    exact fun a ha => (jointCommutant_le_iff E S a).mpr ha hX

/-- Recoverability is idempotent; derived observations supply no extra distinctions. -/
theorem determinedLabels_idempotent {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) :
    determinedLabels E (determinedLabels E S) = determinedLabels E S := by
  ext b
  rw [← jointCommutant_le_iff, jointCommutant_determined, jointCommutant_le_iff]

/-- The dependency closure and the joint commutant contain precisely the same information. -/
theorem jointCommutant_eq_iff {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S T : Set (Fin m)) :
    jointCommutant E S = jointCommutant E T ↔
      determinedLabels E S = determinedLabels E T := by
  constructor
  · intro h
    ext b
    rw [← jointCommutant_le_iff, ← jointCommutant_le_iff, h]
  · intro h
    rw [← jointCommutant_determined E S, ← jointCommutant_determined E T, h]

/-- Coordinate pairs that no selected observation distinguishes. -/
def jointAgreementFinset {m n : ℕ} (E : Fin m → Fin n → ℂ) (S : Set (Fin m)) :
    Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p => ∀ a ∈ S, E a p.1 = E a p.2

/-- Matrix units on the joint fibres span every simultaneous symmetry. -/
theorem jointCommutant_eq_span {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) :
    jointCommutant E S = Submodule.span ℂ
      (Set.range (⇑(Matrix.stdBasis ℂ (Fin n) (Fin n)) ∘
        (Subtype.val : {p : Fin n × Fin n // ∀ a ∈ S, E a p.1 = E a p.2} →
          Fin n × Fin n))) := by
  classical
  refine le_antisymm ?_ ?_
  · intro X hX
    have hrep : X = ∑ p ∈ jointAgreementFinset E S,
        X p.1 p.2 • Matrix.stdBasis ℂ (Fin n) (Fin n) p := by
      ext i j
      rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
      · rw [Matrix.smul_apply, stdBasis_apply']
        simp
      · intro p _ hp
        rw [Matrix.smul_apply, stdBasis_apply']
        have hne : ¬ (p.1 = i ∧ p.2 = j) := by
          rintro ⟨rfl, rfl⟩
          exact hp rfl
        rw [if_neg hne, smul_zero]
      · intro hmem
        have hsep : ∃ a ∈ S, E a i ≠ E a j := by
          by_contra h
          push Not at h
          exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        rw [Matrix.smul_apply, (mem_jointCommutant_iff E S X).mp hX i j hsep]
        simp
    rw [hrep]
    refine Submodule.sum_mem _ fun p hp => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact (matrixUnit_mem_joint_iff E S p.val.1 p.val.2).mpr p.property

/-- The full symmetry dimension is exactly the number of unresolved ordered pairs. -/
theorem finrank_jointCommutant {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) :
    Module.finrank ℂ (jointCommutant E S) = (jointAgreementFinset E S).card := by
  classical
  rw [jointCommutant_eq_span,
    finrank_span_eq_card ((Matrix.stdBasis ℂ (Fin n) (Fin n)).linearIndependent.comp
      (Subtype.val : {p : Fin n × Fin n // ∀ a ∈ S, E a p.1 = E a p.2} →
        Fin n × Fin n) Subtype.val_injective),
    jointAgreementFinset, Fintype.card_subtype]

theorem jointCommutant_insert {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) (b : Fin m) :
    jointCommutant E (insert b S) =
      commutantSubmodule (diagonal (E b)) ⊓ jointCommutant E S := by
  ext X
  simp only [jointCommutant, Submodule.mem_iInf, Submodule.mem_inf, Set.mem_insert_iff]
  constructor
  · intro h
    exact ⟨h b (Or.inl rfl), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨hb, hS⟩ a (rfl | ha)
    · exact hb
    · exact hS a ha

/-- A new label adds information precisely when it removes a joint matrix symmetry. -/
theorem jointCommutant_insert_eq_iff {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) (b : Fin m) :
    jointCommutant E (insert b S) = jointCommutant E S ↔ b ∈ determinedLabels E S := by
  rw [jointCommutant_insert, inf_eq_right, jointCommutant_le_iff]

/-- Every genuinely new observation strictly lowers the dimension of unresolved symmetries. -/
theorem finrank_insert_lt_iff {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) (b : Fin m) :
    Module.finrank ℂ (jointCommutant E (insert b S)) <
      Module.finrank ℂ (jointCommutant E S) ↔ b ∉ determinedLabels E S := by
  have hle : jointCommutant E (insert b S) ≤ jointCommutant E S := by
    rw [jointCommutant_insert]
    exact inf_le_right
  constructor
  · intro h hb
    rw [(jointCommutant_insert_eq_iff E S b).mpr hb] at h
    exact (lt_irrefl _) h
  · intro hb
    apply Submodule.finrank_lt_finrank_of_lt
    exact lt_of_le_of_ne hle (fun he => hb ((jointCommutant_insert_eq_iff E S b).mp he))

#print axioms mem_jointCommutant_iff
#print axioms jointCommutant_le_iff
#print axioms recovery_failure_iff_matrixUnit
#print axioms jointCommutant_determined
#print axioms jointCommutant_eq_iff
#print axioms finrank_jointCommutant
#print axioms finrank_insert_lt_iff

end
end GaloisForLFunctions.HilbertMetric.Observation
