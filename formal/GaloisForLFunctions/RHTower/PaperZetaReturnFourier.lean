import GaloisForLFunctions.RHTower.PaperZetaReturnProfile

/-! # Fourier recovery of the actual deterministic return indicator

The upstream Fourier theorem is applied to sharp indicators, with the entire
sequence of symmetric partial sums. Countably many windows share an exceptional
set on the physical height line, even when their lengths differ.
-/

namespace RHTower
noncomputable section
open Set MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

theorem paperZetaReturnProfile_common_span_convergence {κ : Type*} [Countable κ]
    (D : κ → PaperZetaReturnDisc) (ε T : κ → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => fourierPartialSum
          (fun y => ∑ j ∈ S, c j * paperZetaReturnProfile (D j) (ε j) (T j) y) N x)
          atTop (𝓝 (∑ j ∈ S, c j * paperZetaReturnProfile (D j) (ε j) (T j) x)) :=
  paperUnitIntervalMemLp_common_span_convergence _
    (fun j => paperZetaReturnProfile_memLp (D j) (ε j) (T j))

theorem paperZetaReturnProfile_common_convergence {κ : Type*} [Countable κ]
    (D : κ → PaperZetaReturnDisc) (ε T : κ → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ j,
        Tendsto (fun N => fourierPartialSum
          (paperZetaReturnProfile (D j) (ε j) (T j)) N x) atTop
          (𝓝 (paperZetaReturnProfile (D j) (ε j) (T j) x)) := by
  classical
  obtain ⟨E, hm, hz, hc⟩ := paperZetaReturnProfile_common_span_convergence D ε T
  exact ⟨E, hm, hz, fun x hx he j => by simpa using hc x hx he {j} (fun _ => 1)⟩

/-- The exception is chosen before the disc, tolerance and positive window. -/
theorem paperZetaReturnProfile_common_physical_convergence {κ : Type*} [Countable κ]
    (D : κ → PaperZetaReturnDisc) (ε : κ → ℝ) (T : κ → {t : ℝ // 0 < t}) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ τ ∉ E, ∀ j, τ ∈ Ioc 0 (T j).val →
        Tendsto (fun N => fourierPartialSum
          (paperZetaReturnProfile (D j) (ε j) (T j).val) N ((T j).val⁻¹ * τ)) atTop
          (𝓝 ((paperZetaReturnTimes (D j) (ε j)).indicator (fun _ => (1 : ℂ)) τ)) := by
  classical
  obtain ⟨F, hm, hz, hc⟩ := paperZetaReturnProfile_common_convergence D ε (fun j => (T j).val)
  let E := ⋃ j, (fun τ : ℝ => (T j).val⁻¹ * τ) ⁻¹' F
  have hEnull : volume E = 0 := by
    apply measure_iUnion_null
    intro j
    rw [Real.volume_preimage_mul_left (inv_ne_zero (ne_of_gt (T j).property)), hz, mul_zero]
  refine ⟨E, MeasurableSet.iUnion (fun j => hm.preimage (measurable_const.mul measurable_id)),
    hEnull, ?_⟩
  intro τ hτ j hj
  have he : (T j).val⁻¹ * τ ∉ F := by
    intro hf
    exact hτ (mem_iUnion.mpr ⟨j, hf⟩)
  have hx : (T j).val⁻¹ * τ ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · exact mul_pos (inv_pos.mpr (T j).property) hj.1
    · calc
        (T j).val⁻¹ * τ ≤ (T j).val⁻¹ * (T j).val :=
          mul_le_mul_of_nonneg_left hj.2 (inv_nonneg.mpr (T j).property.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt (T j).property)
  simpa [paperZetaReturnProfile, ← mul_assoc, ne_of_gt (T j).property] using
    hc _ hx he j

/-- Every finite complex mixture is reconstructed at the same actual height. -/
theorem paperZetaReturnProfile_common_physical_span_convergence {κ : Type*} [Countable κ]
    (D : κ → PaperZetaReturnDisc) (ε : κ → ℝ) (T : κ → {t : ℝ // 0 < t}) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ τ ∉ E, ∀ (S : Finset κ) (c : κ → ℂ), (∀ j ∈ S, τ ∈ Ioc 0 (T j).val) →
        Tendsto (fun N => ∑ j ∈ S, c j * fourierPartialSum
          (paperZetaReturnProfile (D j) (ε j) (T j).val) N ((T j).val⁻¹ * τ)) atTop
          (𝓝 (∑ j ∈ S, c j *
            (paperZetaReturnTimes (D j) (ε j)).indicator (fun _ => (1 : ℂ)) τ)) := by
  obtain ⟨E, hm, hz, hc⟩ := paperZetaReturnProfile_common_physical_convergence D ε T
  exact ⟨E, hm, hz, fun τ hτ S c hS =>
    tendsto_finsetSum S (fun j hj => (hc τ hτ j (hS j hj)).const_mul (c j))⟩

end
end RHTower
