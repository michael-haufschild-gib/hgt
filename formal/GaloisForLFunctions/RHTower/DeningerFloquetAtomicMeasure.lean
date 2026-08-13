import GaloisForLFunctions.RHTower.DeningerFloquetLatticeMeasure

/-!
# The arithmetic lattice measure is atomic

Every node of the arithmetic frequency lattice carries positive finite mass, and the complement of
the node set is null.  Consequently a function vanishing at every node vanishes almost everywhere,
which is what turns the separate approximability of the nodes into density in `L²(μ_Fl)`.

* `deningerFloquetMeasure_singleton_pos` : **every node is an atom.**
* `deningerFloquetMeasure_singleton_lt_top` : the atoms have finite mass.
* `deningerFloquetMeasure_ae_eq_zero` : **vanishing on the nodes is vanishing almost everywhere.**
-/

namespace RHTower

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The lattice counting measure gives each of its nodes mass at least one. -/
theorem one_le_deningerFloquetLattice_singleton (q : ℕ) (m : ℤ) :
    1 ≤ deningerFloquetLattice q {deningerFloquetNode q m} := by
  rw [deningerFloquetLattice, Measure.sum_apply _ (measurableSet_singleton _)]
  refine le_trans ?_ (ENNReal.le_tsum m)
  rw [Measure.dirac_apply' _ (measurableSet_singleton _),
    Set.indicator_of_mem (Set.mem_singleton _)]
  exact le_rfl

/-- **Every node of the arithmetic lattice is an atom of `μ_Fl`.** -/
theorem deningerFloquetMeasure_singleton_pos {ξ : ℝ} (hξ : ξ ∈ deningerFloquetSupport) :
    0 < deningerFloquetMeasure {ξ} := by
  obtain ⟨⟨q, m⟩, hqm⟩ := hξ
  have hnode : deningerFloquetNode (q : ℕ) m = ξ := hqm
  rw [deningerFloquetMeasure, Measure.sum_apply _ (measurableSet_singleton _)]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum q)
  rw [Measure.smul_apply, smul_eq_mul, ← hnode]
  have hone := one_le_deningerFloquetLattice_singleton (q : ℕ) m
  have hw := deningerFloquetWeight_pos q
  calc (0 : ℝ≥0∞) < deningerFloquetWeight (q : ℕ) * 1 := by rwa [mul_one]
    _ ≤ deningerFloquetWeight (q : ℕ)
        * deningerFloquetLattice (q : ℕ) {deningerFloquetNode (q : ℕ) m} := by gcongr

theorem deningerFloquetMeasure_singleton_lt_top (ξ : ℝ) : deningerFloquetMeasure {ξ} < ⊤ := by
  have hsub : ({ξ} : Set ℝ) ⊆ Set.Icc (-|ξ|) |ξ| := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨neg_abs_le x, le_abs_self x⟩
  exact lt_of_le_of_lt (measure_mono hsub) (deningerFloquetMeasure_Icc_lt_top (abs_nonneg ξ))

theorem deningerFloquetMeasure_singleton_ne_zero {ξ : ℝ} (hξ : ξ ∈ deningerFloquetSupport) :
    deningerFloquetMeasure {ξ} ≠ 0 :=
  (deningerFloquetMeasure_singleton_pos hξ).ne'

/-- **Vanishing at every node is vanishing almost everywhere.** -/
theorem deningerFloquetMeasure_ae_eq_zero {α : Type*} [Zero α] {f : ℝ → α}
    (hf : ∀ ξ ∈ deningerFloquetSupport, f ξ = 0) : f =ᵐ[deningerFloquetMeasure] 0 := by
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) deningerFloquetMeasure_compl_support
  intro hmem
  exact hx (hf x hmem)

end

end RHTower
