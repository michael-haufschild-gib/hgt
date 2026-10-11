import GaloisForLFunctions.HTGeometry.ModulationWeakEscape
import GaloisForLFunctions.HTGeometry.CompactCofinalEssentialMargin

/-!
# The compact ideal is faithful on the modulation commutant

Every bounded multiplier on continuous L² commutes with modulation. Escaping modulation
orbits show that passage to the compact quotient preserves every norm and distance in this
algebra. The proven TraceCone ideal weight therefore vanishes exactly on its zero element.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open MeasureTheory Filter Classical
open scoped ENNReal Topology

/-- The bounded operators commuting with every modulation on continuous L². -/
def paperModulationCommutant :
    Subalgebra ℂ (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :=
  Subalgebra.centralizer ℂ (Set.range modulationMul)

theorem mem_paperModulationCommutant_iff
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :
    T ∈ paperModulationCommutant ↔
      ∀ t f, T (modulationMul t f) = modulationMul t (T f) := by
  rw [paperModulationCommutant, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h t f
    exact (congrArg (fun A => A f) (h _ ⟨t, rfl⟩)).symm
  · intro h S hS
    obtain ⟨t, rfl⟩ := hS
    apply ContinuousLinearMap.ext
    intro f
    exact (h t f).symm

/-- Any bounded operator acting by a scalar symbol belongs to the commutant. -/
theorem mem_paperModulationCommutant_of_mul
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (φ : ℝ → ℂ)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun x => φ x * f x) :
    T ∈ paperModulationCommutant := by
  rw [mem_paperModulationCommutant_iff]
  intro t f
  apply Lp.ext
  filter_upwards [hT (modulationMul t f), coeFn_modulationMul t f,
    coeFn_modulationMul t (T f), hT f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  ring

/-- The standard bounded multiplier construction lies in this same algebra. -/
theorem lpBoundedMulCLM_mem_paperModulationCommutant
    {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖φ x‖ ≤ C) :
    lpBoundedMulCLM (p := 2) (μ := volume) hφ hC hbound ∈ paperModulationCommutant :=
  mem_paperModulationCommutant_of_mul _ φ (lpBoundedMulCLM_coeFn hφ hC hbound)

/-- Compact conjugates vanish strongly along integer-frequency modulations. -/
theorem modulationMul_compact_conjugation_tendsto
    (K : compactOperatorStarAlgebra (Lp ℂ 2 (volume : Measure ℝ)))
    (v : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n : ℕ => modulationMul (-(n : ℝ)) (K.1 (modulationMul (n : ℝ) v)))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_modulationMul_eq] using
    tendsto_zero_iff_norm_tendsto_zero.mp (modulationMul_compact_tendsto K v)

/-- No compact correction can reduce the norm of an element of the commutant. -/
theorem paperModulationCommutant_norm_le_sub_compact (A : paperModulationCommutant)
    (K : compactOperatorStarAlgebra (Lp ℂ 2 (volume : Measure ℝ))) :
    ‖A.1‖ ≤ ‖A.1 - K.1‖ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
  intro v hv
  have h := ((tendsto_const_nhds (x := A.1 v)).sub
    (modulationMul_compact_conjugation_tendsto K v)).norm
  simp only [sub_zero] at h
  apply le_of_tendsto' h
  intro n
  have he : A.1 v - modulationMul (-(n : ℝ)) (K.1 (modulationMul (n : ℝ) v)) =
      modulationMul (-(n : ℝ)) ((A.1 - K.1) (modulationMul (n : ℝ) v)) := by
    rw [sub_apply, map_sub,
      (mem_paperModulationCommutant_iff A.1).mp A.2,
      modulationMul_neg_modulationMul]
  rw [he, norm_modulationMul_eq]
  simpa only [norm_modulationMul_eq, hv, mul_one] using
    (A.1 - K.1).le_opNorm (modulationMul (n : ℝ) v)

/-- Passing to the compact quotient preserves the full norm. -/
theorem paperModulationCommutant_compactIdealDistance (A : paperModulationCommutant) :
    compactIdealDistance A.1 = ‖A.1‖ := by
  apply le_antisymm
  · simpa using compactIdealDistance_le A.1 0 isCompactOperator_zero
  · exact le_compactIdealDistance A.1 ‖A.1‖ fun K hK =>
      paperModulationCommutant_norm_le_sub_compact A ⟨K, hK⟩

/-- Zero is the only compact element of the entire commutant. -/
theorem paperModulationCommutant_compact_iff_zero (A : paperModulationCommutant) :
    IsCompactOperator A.1 ↔ A = 0 := by
  constructor
  · intro h
    have hn := paperModulationCommutant_norm_le_sub_compact A ⟨A.1, h⟩
    rw [sub_self, norm_zero] at hn
    apply Subtype.ext
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  · rintro rfl
    exact isCompactOperator_zero

/-- Equality modulo compacts is literal equality throughout the commutant. -/
theorem paperModulationCommutant_compact_sub_iff_eq (A B : paperModulationCommutant) :
    IsCompactOperator (A.1 - B.1) ↔ A = B := by
  change IsCompactOperator (A - B).1 ↔ _
  rw [paperModulationCommutant_compact_iff_zero, sub_eq_zero]

/-- Every pairwise distance survives passage to the compact quotient. -/
theorem paperModulationCommutant_compactIdealDistance_sub (A B : paperModulationCommutant) :
    compactIdealDistance (A.1 - B.1) = dist A B := by
  simpa [dist_eq_norm] using paperModulationCommutant_compactIdealDistance (A - B)

/-- The proven paper ideal weight detects exactly the zero multiplier. -/
theorem paperModulationCommutant_traceCost (A : paperModulationCommutant) :
    compactOperatorTraceCost (Lp ℂ 2 (volume : Measure ℝ)) A.1 =
      if A = 0 then 0 else ∞ := by
  classical
  rw [compactOperatorTraceCost_eq, paperModulationCommutant_compact_iff_zero]
  split_ifs <;> rfl

/-- Compact corrections do not affect this exact classification. -/
theorem paperModulationCommutant_traceCost_add_compact (A : paperModulationCommutant)
    (K : compactOperatorStarAlgebra (Lp ℂ 2 (volume : Measure ℝ))) :
    compactOperatorTraceCost (Lp ℂ 2 (volume : Measure ℝ)) (A.1 + K.1) =
      if A = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperModulationCommutant_traceCost]

end
end GaloisForLFunctions.HTGeometry
