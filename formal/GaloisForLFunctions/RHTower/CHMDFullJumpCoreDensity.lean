import GaloisForLFunctions.RHTower.CHMDGraphMollification
import GaloisForLFunctions.RHTower.CHMDBoundedCompactDomain

/-!
# The compact C2 core is the complete maximal CHMD jump domain

Bounded truncation, spatial cutoff, stationary Levy smoothing, and weak closedness
identify the two domains for the literal full arithmetic edge measure. No compact
embedding or primitive sign is assumed. The signed mass subtraction is unchanged.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph

/-- Every maximal-domain vector is a graph limit of actual compact C2 source tests. -/
theorem compactCore_eq_top : compactCore = ⊤ := by
  have hsubset : boundedCompactDomain ⊆ (compactCore : Set SourceGraph) := by
    rintro p ⟨v, hv, hs, hd, M, hM, hb, hc, rfl⟩
    exact bounded_compact_mem_core v hv hc hs hd M hM hb
  have hclosure := closure_minimal hsubset isClosed_compactCore
  apply top_unique
  intro p _
  exact hclosure (dense_boundedCompactDomain p)

/-- The literal compact C2 tests already form a linear subspace. -/
def compactTests : Submodule ℝ SourceGraph where
  carrier := {p | ∃ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v), p = compactLift v hv hc}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    apply source_projection_injective
    rfl
  add_mem' := by
    rintro p q ⟨v, hv, hc, rfl⟩ ⟨w, hw, hwc, rfl⟩
    refine ⟨v + w, hv.add hw, hc.add hwc, ?_⟩
    apply source_projection_injective
    change (compact_memLp_mass hv.continuous hc).toLp v +
      (compact_memLp_mass hw.continuous hwc).toLp w = _
    exact (MemLp.toLp_add _ _).symm
  smul_mem' := by
    rintro c p ⟨v, hv, hc, rfl⟩
    refine ⟨fun x => c * v x, contDiff_const.mul hv, hc.mul_left, ?_⟩
    apply source_projection_injective
    change c • (compact_memLp_mass hv.continuous hc).toLp v = _
    exact (MemLp.toLp_const_smul c _).symm

theorem compactTests_closure : compactTests.topologicalClosure = compactCore := by
  change compactTests.topologicalClosure =
    (Submodule.span ℝ (compactTests : Set SourceGraph)).topologicalClosure
  rw [Submodule.span_eq]

/-- Single genuine compact smooth tests, not merely auxiliary graph vectors, are dense. -/
theorem dense_compactTests : Dense (compactTests : Set SourceGraph) := by
  rw [dense_iff_closure_eq]
  change (compactTests.topologicalClosure : Set SourceGraph) = univ
  rw [compactTests_closure, compactCore_eq_top]
  rfl

end RHTower.CHMDDoobGraph
