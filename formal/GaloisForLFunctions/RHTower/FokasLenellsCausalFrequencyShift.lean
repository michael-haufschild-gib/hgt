import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyRecurrence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
open Complex Set Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section GenericShift
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem eigen_span_invariant (T : E →L[ℂ] E) (v : I → E) (z : I → ℂ)
    (he : ∀ i, T (v i) = z i • v i) :
    ∀ u ∈ Submodule.span ℂ (Set.range v), T u ∈ Submodule.span ℂ (Set.range v) := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb ia ib => rw [map_add]; exact Submodule.add_mem _ ia ib
  | smul c a ha ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

private theorem closure_invariant (T : E →L[ℂ] E) (A : Submodule ℂ E)
    (ha : ∀ u ∈ A, T u ∈ A) :
    ∀ u ∈ A.topologicalClosure, T u ∈ A.topologicalClosure := by
  have hc : IsClosed {u : E | T u ∈ A.topologicalClosure} :=
    A.isClosed_topologicalClosure.preimage T.continuous
  exact hc.closure_subset_iff.mpr (fun u hu => A.le_topologicalClosure (ha u hu))

private def invariantIsometry (T : E →L[ℂ] E) (D : Submodule ℂ E)
    (hi : ∀ u ∈ D, T u ∈ D) (hn : ∀ u : D, ‖T u.val‖ = ‖u‖) : D →ₗᵢ[ℂ] D where
  toLinearMap := ((T.comp D.subtypeL).codRestrict D (fun u => hi u.val u.property)).toLinearMap
  norm_map' := hn

private theorem invariantIsometry_val (T : E →L[ℂ] E) (D : Submodule ℂ E)
    (hi : ∀ u ∈ D, T u ∈ D) (hn : ∀ u : D, ‖T u.val‖ = ‖u‖) (u : D) :
    (invariantIsometry T D hi hn u).val = T u.val := rfl

private theorem closed_span_surjective (D : Submodule ℂ E) [CompleteSpace D]
    (v : I → D) (z : I → ℂ) (hz : ∀ i, z i ≠ 0) (J : D →ₗᵢ[ℂ] D)
    (he : ∀ i, J (v i) = z i • v i)
    (hd : D = (Submodule.span ℂ (Set.range (fun i => (v i).val))).topologicalClosure) :
    Function.Surjective J := by
  let F : D →ₗᵢ[ℂ] E :=
    { toLinearMap := D.subtype.comp J.toLinearMap
      norm_map' := fun u => J.norm_map u }
  have hr : IsClosed (LinearMap.range F.toLinearMap : Set E) :=
    F.isometry.isClosedEmbedding.isClosed_range
  have hs : Submodule.span ℂ (Set.range (fun i => (v i).val)) ≤ LinearMap.range F.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro w ⟨i, rfl⟩
    refine ⟨(z i)⁻¹ • v i, ?_⟩
    change (J ((z i)⁻¹ • v i)).val = (v i).val
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ (hz i), one_smul]
  intro u
  have hu : u.val ∈ (Submodule.span ℂ (Set.range (fun i => (v i).val))).topologicalClosure :=
    (congrArg (fun A : Submodule ℂ E => u.val ∈ A) hd).mp u.property
  obtain ⟨w, hw⟩ := hr.closure_subset_iff.mpr hs hu
  exact ⟨w, Subtype.ext hw⟩

private theorem equiv_inverse_eigen (e : E ≃ₗᵢ[ℂ] E) (v : E) (z : ℂ)
    (hz : z ≠ 0) (he : e v = z • v) : e.symm v = z⁻¹ • v := by
  apply e.injective
  rw [e.apply_symm_apply, map_smul, he, smul_smul, inv_mul_cancel₀ hz, one_smul]
end GenericShift
private theorem frequency_invariant (b : ℝ) :
    ∀ u ∈ causalFrequencySpace b, causalBoundedChainShift u ∈ causalFrequencySpace b :=
  closure_invariant causalBoundedChainShift (causalFrequencyCore b)
    (eigen_span_invariant causalBoundedChainShift (causalBoundedUnitEigenchain b)
      (fun ω => (causalUnitBoundaryRate b ω).val) (causalBoundedChainShift_unitEigenchain b))

private def frequencyShiftIsometry (b : ℝ) :
    causalFrequencySpace b →ₗᵢ[ℂ] causalFrequencySpace b :=
  invariantIsometry causalBoundedChainShift (causalFrequencySpace b)
    (frequency_invariant b) (causalBoundedChainShift_frequency_norm b)

private theorem frequencyShiftIsometry_val (b : ℝ) (u : causalFrequencySpace b) :
    (frequencyShiftIsometry b u).val = causalBoundedChainShift u.val := by
  simpa only [frequencyShiftIsometry] using!
    invariantIsometry_val causalBoundedChainShift (causalFrequencySpace b)
      (frequency_invariant b) (causalBoundedChainShift_frequency_norm b) u

private theorem frequencyShiftIsometry_mode (b ω : ℝ) :
    frequencyShiftIsometry b (causalFrequencyMode b ω) =
      (causalUnitBoundaryRate b ω).val • causalFrequencyMode b ω := by
  apply Subtype.ext
  exact (frequencyShiftIsometry_val b (causalFrequencyMode b ω)).trans
    (causalBoundedChainShift_unitEigenchain b ω)

private theorem unit_rate_ne_zero (b ω : ℝ) : (causalUnitBoundaryRate b ω).val ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_causalUnitBoundaryRate]; exact one_ne_zero)

private theorem frequencyShiftIsometry_surjective (b : ℝ) :
    Function.Surjective (frequencyShiftIsometry b) := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  exact closed_span_surjective (causalFrequencySpace b) (causalFrequencyMode b)
    (fun ω => (causalUnitBoundaryRate b ω).val) (unit_rate_ne_zero b)
    (frequencyShiftIsometry b) (frequencyShiftIsometry_mode b) rfl

/-- The actual bounded derivative shift is a bijective complex linear isometry
on the genuine completed span of unit frequency modes. Its inverse stays in that same space. -/
def causalFrequencyShift (b : ℝ) : causalFrequencySpace b ≃ₗᵢ[ℂ] causalFrequencySpace b :=
  LinearIsometryEquiv.ofSurjective (frequencyShiftIsometry b) (frequencyShiftIsometry_surjective b)

/-- The isometric automorphism is exactly the existing derivative shift on the underlying chain. -/
theorem causalFrequencyShift_val (b : ℝ) (u : causalFrequencySpace b) :
    (causalFrequencyShift b u).val = causalBoundedChainShift u.val := by
  have h := congrFun (LinearIsometryEquiv.coe_ofSurjective
    (frequencyShiftIsometry b) (frequencyShiftIsometry_surjective b)) u
  exact (congrArg Subtype.val h).trans (frequencyShiftIsometry_val b u)

/-- The actual shift automorphism acts on each genuine mode by its unit complex rate. -/
theorem causalFrequencyShift_mode (b ω : ℝ) :
    causalFrequencyShift b (causalFrequencyMode b ω) =
      (causalUnitBoundaryRate b ω).val • causalFrequencyMode b ω := by
  apply Subtype.ext
  exact (causalFrequencyShift_val b (causalFrequencyMode b ω)).trans
    (causalBoundedChainShift_unitEigenchain b ω)

/-- The genuine inverse derivative shift acts on every unit mode by its reciprocal rate. -/
theorem causalFrequencyShift_symm_mode (b ω : ℝ) :
    (causalFrequencyShift b).symm (causalFrequencyMode b ω) =
      (causalUnitBoundaryRate b ω).val⁻¹ • causalFrequencyMode b ω :=
  equiv_inverse_eigen (causalFrequencyShift b) (causalFrequencyMode b ω)
    (causalUnitBoundaryRate b ω).val (unit_rate_ne_zero b ω) (causalFrequencyShift_mode b ω)

end RHTower.FokasLenells
