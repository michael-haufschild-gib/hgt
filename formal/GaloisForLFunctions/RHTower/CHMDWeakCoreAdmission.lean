import GaloisForLFunctions.RHTower.CHMDCompactGraphCutoffs
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Weak admission into the compact CHMD core

Uniform graph bounds and strong source convergence suffice to identify a compact-core
limit. This uses weak Hilbert compactness, not compactness of the source projection.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph

instance sFinite_archMeasure : SFinite archMeasure := by
  unfold archMeasure archBase
  infer_instance

instance sFinite_primeMeasure (n : ℕ) : SFinite (primeMeasure n) := by
  unfold primeMeasure
  infer_instance

instance sFinite_edgeMeasure : SFinite edgeMeasure := by
  unfold edgeMeasure
  infer_instance

instance secondCountable_sourceGraph : SecondCountableTopology SourceGraph := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  letI : SecondCountableTopology (Lp ℝ 2 massMeasure) := Lp.SecondCountableTopology
  letI : SecondCountableTopology (Lp ℝ 2 edgeMeasure) := Lp.SecondCountableTopology
  letI : SecondCountableTopology (CHMDClosedJump.Carrier massMeasure edgeMeasure) := inferInstance
  infer_instance

def sourceMap : SourceGraph →L[ℝ] Lp ℝ 2 massMeasure :=
  (WithLp.fstL 2 ℝ _ _).comp SourceGraph.subtypeL

theorem exists_real_weak_subseq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (u : ℕ → H)
    (M : ℝ) (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ w : H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ y : H, Tendsto (fun n => ⟪u (φ n), y⟫_ℝ) atTop (𝓝 ⟪w, y⟫_ℝ) := by
  let d : ℕ → WeakDual ℝ H := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u n))
  have hd : ∀ n, d n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) M := by
    intro n
    change dist (InnerProductSpace.toDual ℝ H (u n)) 0 ≤ M
    rw [dist_zero_right, (InnerProductSpace.toDual ℝ H).norm_map]
    exact hM n
  obtain ⟨a, _, φ, hφ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H 0 M).subseq_of_frequently_in
      (Eventually.of_forall hd).frequently
  let w := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual a)
  refine ⟨w, φ, hφ, fun y => ?_⟩
  have heval := ((WeakDual.eval_continuous y).tendsto a).comp hlim
  have hw : ⟪w, y⟫_ℝ = a y := by
    change ⟪(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual a), y⟫_ℝ = _
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  rw [hw]
  exact heval

/-- Bounded smooth approximants need only converge strongly in the source coordinate. -/
theorem mem_core_of_bounded_source_approx (p : SourceGraph) (u : ℕ → SourceGraph)
    (hu : ∀ n, u n ∈ compactCore) (M : ℝ) (hM : ∀ n, ‖u n‖ ≤ M)
    (hs : Tendsto (fun n => (u n).val.fst) atTop (𝓝 p.val.fst)) : p ∈ compactCore := by
  obtain ⟨w, φ, hφ, hw⟩ := exists_real_weak_subseq u M hM
  letI : CompleteSpace compactCore := complete_compactCore
  have hwcore : w ∈ compactCore := by
    rw [← compactCore.orthogonal_orthogonal, Submodule.mem_orthogonal']
    intro y hy
    have hzero : ∀ n, ⟪u (φ n), y⟫_ℝ = 0 :=
      fun n => compactCore.inner_right_of_mem_orthogonal (hu (φ n)) hy
    exact tendsto_nhds_unique (hw y) (by simp only [hzero]; exact tendsto_const_nhds)
  have hwp : w = p := by
    apply source_projection_injective
    apply ext_inner_right ℝ
    intro y
    have hwsource : Tendsto (fun n => ⟪(u (φ n)).val.fst, y⟫_ℝ) atTop (𝓝 ⟪w.val.fst, y⟫_ℝ) := by
      change Tendsto (fun n => ⟪sourceMap (u (φ n)), y⟫_ℝ) atTop (𝓝 ⟪sourceMap w, y⟫_ℝ)
      simpa only [ContinuousLinearMap.adjoint_inner_right] using hw (sourceMap.adjoint y)
    have hpsource : Tendsto (fun n => ⟪(u (φ n)).val.fst, y⟫_ℝ) atTop (𝓝 ⟪p.val.fst, y⟫_ℝ) :=
      (hs.comp hφ.tendsto_atTop).inner (tendsto_const_nhds (x := y))
    exact tendsto_nhds_unique hwsource hpsource
  rwa [← hwp]

end RHTower.CHMDDoobGraph
