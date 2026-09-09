import GaloisForLFunctions.HTGeometry.FokasLenellsRawComplexCoreGroup

/-!
# Sharp continuity and extension gates on the common entire core

Having an entire L² orbit for each core vector does not give a bounded
operator on the core with its inherited L² norm. The exact cutoff graph
decomposition and core density force the same sharp real zeroth-order gate.
All continuous extensions are classified, including their unique actual value.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem core_projection_contract (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖rawComplexGraphCutoff a u‖ ≤ ‖u‖ := by
  have hn : ‖rawComplexGraphCutoff a‖ ≤ 1 := by
    unfold rawComplexGraphCutoff
    exact norm_lpBoundedMulCLM_le _ _ _
  calc
    _ ≤ ‖rawComplexGraphCutoff a‖ * ‖u‖ := (rawComplexGraphCutoff a).le_opNorm u
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg u)
    _ = _ := one_mul _

private theorem good_core_value (n : ℕ) (τ : ℂ) (hn : n = 0) (hi : τ.im = 0)
    (u : rawComplexEntireCore) :
    (rawComplexCoreHierarchy n τ u).val = evolution τ.re u.val := by
  have he : τ = (τ.re : ℂ) := by apply Complex.ext <;> simp [hi]
  rw [hn,he,rawComplexCoreHierarchy_zero_ofReal,Complex.ofReal_re]

/-- The raw core hierarchy is bounded in the original L² norm exactly at real zeroth order. -/
theorem rawComplexCoreHierarchy_bounded_iff (n : ℕ) (τ : ℂ) :
    (∃ B : ℝ, ∀ u : rawComplexEntireCore, ‖rawComplexCoreHierarchy n τ u‖ ≤ B * ‖u‖) ↔
      n = 0 ∧ τ.im = 0 := by
  constructor
  · rintro ⟨B,hB⟩
    let C := max B 0
    have hC0 : 0 ≤ C := le_max_right _ _
    have hC : ∀ u : rawComplexEntireCore, ‖rawComplexCoreHierarchy n τ u‖ ≤ C * ‖u‖ :=
      fun u => (hB u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg u))
    apply (cutoffComplexOperator_uniform_norm_bound_iff n τ).1
    refine ⟨C+2,fun a => (cutoffComplexOperator a n τ).opNorm_le_bound (by linarith) ?_⟩
    have hcore : ∀ u : rawComplexEntireCore,
        ‖cutoffComplexOperator a n τ u.val‖ ≤ (C+2) * ‖u.val‖ := by
      intro u
      let c : ℂ := if n = 0 then 1 else 0
      have hc : ‖c‖ ≤ 1 := by dsimp only [c]; split_ifs <;> simp
      have hcu : ‖c • u.val‖ ≤ ‖u.val‖ := by
        rw [norm_smul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg u.val)
      have he : cutoffComplexOperator a n τ u.val = c • u.val +
          rawComplexGraphCutoff a ((rawComplexCoreHierarchy n τ u).val - c • u.val) :=
        rawComplexGraph_cutoff_decomposition n τ
          ⟨(u.val,(rawComplexCoreHierarchy n τ u).val),rawComplexCoreHierarchy_mem_graph n τ u⟩ a
      rw [he]
      calc
        _ ≤ ‖c • u.val‖ + ‖rawComplexGraphCutoff a ((rawComplexCoreHierarchy n τ u).val - c • u.val)‖ := norm_add_le _ _
        _ ≤ ‖u.val‖ + ‖(rawComplexCoreHierarchy n τ u).val - c • u.val‖ :=
          add_le_add hcu (core_projection_contract _ _)
        _ ≤ ‖u.val‖ + (‖(rawComplexCoreHierarchy n τ u).val‖ + ‖c • u.val‖) :=
          add_le_add (le_refl ‖u.val‖) (norm_sub_le _ _)
        _ ≤ ‖u.val‖ + (C * ‖u.val‖ + ‖u.val‖) :=
          add_le_add (le_refl ‖u.val‖) (add_le_add
            (show ‖(rawComplexCoreHierarchy n τ u).val‖ ≤ C * ‖u.val‖ from hC u) hcu)
        _ = _ := by ring
    have hclosed : IsClosed {u : Lp ℂ 2 (volume : Measure ℝ) |
        ‖cutoffComplexOperator a n τ u‖ ≤ (C+2) * ‖u‖} :=
      isClosed_le (cutoffComplexOperator a n τ).continuous.norm (continuous_const.mul continuous_norm)
    have hsub : (rawComplexEntireCore : Set (Lp ℂ 2 (volume : Measure ℝ))) ⊆
        {u | ‖cutoffComplexOperator a n τ u‖ ≤ (C+2) * ‖u‖} := fun u hu => hcore ⟨u,hu⟩
    intro u
    exact closure_minimal hsub hclosed (dense_rawComplexEntireCore u)
  · rintro ⟨hn,hi⟩
    refine ⟨1,fun u => ?_⟩
    change ‖(rawComplexCoreHierarchy n τ u).val‖ ≤ 1 * ‖u.val‖
    rw [good_core_value n τ hn hi,(evolution τ.re).norm_map,one_mul]

/-- Outside the real zeroth-order gate, core vectors exceed every proposed norm bound. -/
theorem rawComplexCoreHierarchy_unbounded_growth_iff (n : ℕ) (τ : ℂ) :
    (∀ B : ℝ, ∃ u : rawComplexEntireCore, B * ‖u‖ < ‖rawComplexCoreHierarchy n τ u‖) ↔
      n ≠ 0 ∨ τ.im ≠ 0 := by
  simpa only [not_exists,not_forall,not_le,not_and_or] using
    not_congr (rawComplexCoreHierarchy_bounded_iff n τ)

/-- Continuity of the actual linear hierarchy on the inherited core norm has the same exact gate. -/
theorem rawComplexCoreHierarchy_continuous_iff (n : ℕ) (τ : ℂ) :
    Continuous (rawComplexCoreHierarchy n τ) ↔ n = 0 ∧ τ.im = 0 := by
  constructor
  · intro hc
    let T : rawComplexEntireCore →L[ℂ] rawComplexEntireCore := ⟨rawComplexCoreHierarchy n τ,hc⟩
    exact (rawComplexCoreHierarchy_bounded_iff n τ).1 ⟨‖T‖,fun u => T.le_opNorm u⟩
  · intro h
    exact ((rawComplexCoreHierarchy n τ).mkContinuousOfExistsBound
      ((rawComplexCoreHierarchy_bounded_iff n τ).2 h)).continuous

/-- Every continuous extension is uniquely the original real-time raw evolution. -/
theorem rawComplexCoreHierarchy_extension_iff (n : ℕ) (τ : ℂ)
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :
    (∀ u : rawComplexEntireCore, T u.val = (rawComplexCoreHierarchy n τ u).val) ↔
      n = 0 ∧ τ.im = 0 ∧ T = (evolution τ.re).toContinuousLinearEquiv.toContinuousLinearMap := by
  constructor
  · intro h
    have hg : n = 0 ∧ τ.im = 0 := (rawComplexCoreHierarchy_bounded_iff n τ).1
      ⟨‖T‖,fun u => by change ‖(rawComplexCoreHierarchy n τ u).val‖ ≤ ‖T‖ * ‖u.val‖; rw [← h u]; exact T.le_opNorm _⟩
    refine ⟨hg.1,hg.2,?_⟩
    apply ContinuousLinearMap.ext
    intro u
    have hsub : (rawComplexEntireCore : Set (Lp ℂ 2 (volume : Measure ℝ))) ⊆
        {u | T u = (evolution τ.re).toContinuousLinearEquiv.toContinuousLinearMap u} := by
      intro u hu
      exact (h ⟨u,hu⟩).trans (good_core_value n τ hg.1 hg.2 ⟨u,hu⟩)
    exact closure_minimal hsub
      (isClosed_eq T.continuous (evolution τ.re).toContinuousLinearEquiv.toContinuousLinearMap.continuous)
      (dense_rawComplexEntireCore u)
  · rintro ⟨hn,hi,rfl⟩ u
    exact (good_core_value n τ hn hi u).symm

/-- A bounded extension to all L² exists exactly at real zeroth order. -/
theorem rawComplexCoreHierarchy_has_continuous_extension_iff (n : ℕ) (τ : ℂ) :
    (∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ u : rawComplexEntireCore, T u.val = (rawComplexCoreHierarchy n τ u).val) ↔
      n = 0 ∧ τ.im = 0 := by
  constructor
  · rintro ⟨T,hT⟩
    have h := (rawComplexCoreHierarchy_extension_iff n τ T).1 hT
    exact ⟨h.1,h.2.1⟩
  · intro h
    refine ⟨(evolution τ.re).toContinuousLinearEquiv.toContinuousLinearMap,?_⟩
    exact (rawComplexCoreHierarchy_extension_iff n τ _).2 ⟨h.1,h.2,rfl⟩

/-- The genuine complex group acts continuously on the inherited core norm exactly on the real axis. -/
theorem rawComplexCoreGroup_continuous_iff (τ : ℂ) :
    Continuous (rawComplexCoreGroup τ) ↔ τ.im = 0 := by
  change Continuous (rawComplexCoreHierarchy 0 τ) ↔ _
  rw [rawComplexCoreHierarchy_continuous_iff]
  simp

/-- The real axis is precisely the isometric locus of the actual complex group on the core. -/
theorem rawComplexCoreGroup_isometry_iff (τ : ℂ) : Isometry (rawComplexCoreGroup τ) ↔ τ.im = 0 := by
  constructor
  · intro h
    exact (rawComplexCoreGroup_continuous_iff τ).1 h.continuous
  · intro hi
    apply AddMonoidHomClass.isometry_of_norm (rawComplexCoreGroup τ)
    intro u
    change ‖(rawComplexCoreHierarchy 0 τ u).val‖ = ‖u.val‖
    rw [good_core_value 0 τ rfl hi]
    exact (evolution τ.re).norm_map _

end
end GaloisForLFunctions.HTGeometry.FokasLenells
