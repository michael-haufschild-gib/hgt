import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Order.Compact

/-!
# Uniform finite detection on compact families

A compact family of sequences avoids zero exactly when finitely many
coordinates detect every member. In a normed group, their total norm even
has a uniform positive lower bound. The finite-subcover step is the
compactness mechanism in Zehavi, Lemma 3.28, arXiv:2611.18218; here both
detection and its quantitative margin are proved directly.
-/

namespace GaloisForLFunctions.HilbertMetric.Observation

variable {E : Type*} [NormedAddCommGroup E]

/-- Compactness turns pointwise nonzero coordinates into a uniform finite horizon. -/
theorem compact_finite_detection_iff (K : TopologicalSpace.Compacts (ℕ → E)) :
    (∃ N, ∀ f ∈ K, ∃ i < N, f i ≠ 0) ↔ (0 : ℕ → E) ∉ K := by
  constructor
  · rintro ⟨N, hN⟩ hzero
    obtain ⟨i, _, hi⟩ := hN 0 hzero
    exact hi rfl
  · intro hzero
    have hcover : (K : Set (ℕ → E)) ⊆ ⋃ i : ℕ, {f | f i ≠ 0} := by
      intro f hf
      have hf0 : f ≠ 0 := by rintro rfl; exact hzero hf
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hf0
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    obtain ⟨s, hs⟩ := K.isCompact.elim_finite_subcover
      (fun i : ℕ => {f : ℕ → E | f i ≠ 0})
      (fun i => isOpen_ne_fun (continuous_apply i) continuous_const) hcover
    refine ⟨s.sup id + 1, ?_⟩
    intro f hf
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hf)
    obtain ⟨his, hfi⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) his), hfi⟩

/-- A compact family avoiding zero admits finitely many observations with a positive margin. -/
theorem compact_uniform_detection_iff (K : TopologicalSpace.Compacts (ℕ → E)) :
    (∃ N ε, 0 < ε ∧ ∀ f ∈ K, ε ≤ ∑ i ∈ Finset.range N, ‖f i‖) ↔
      (0 : ℕ → E) ∉ K := by
  constructor
  · rintro ⟨N, ε, hε, h⟩ hzero
    have := h 0 hzero
    simp only [Pi.zero_apply, norm_zero, Finset.sum_const_zero] at this
    exact (not_le_of_gt hε) this
  · intro hzero
    obtain ⟨N, hN⟩ := (compact_finite_detection_iff K).mpr hzero
    have hc : Continuous (fun f : ℕ → E => ∑ i ∈ Finset.range N, ‖f i‖) := by
      fun_prop
    have hp (f : ℕ → E) (hf : f ∈ K) : 0 < ∑ i ∈ Finset.range N, ‖f i‖ := by
      obtain ⟨i, hi, hfi⟩ := hN f hf
      exact Finset.sum_pos' (fun j _ => norm_nonneg (f j))
        ⟨i, Finset.mem_range.mpr hi, norm_pos_iff.mpr hfi⟩
    obtain ⟨ε, hε, h⟩ := K.isCompact.exists_forall_le' hc.continuousOn hp
    exact ⟨N, ε, hε, h⟩

end GaloisForLFunctions.HilbertMetric.Observation

#print axioms GaloisForLFunctions.HilbertMetric.Observation.compact_finite_detection_iff
#print axioms GaloisForLFunctions.HilbertMetric.Observation.compact_uniform_detection_iff
