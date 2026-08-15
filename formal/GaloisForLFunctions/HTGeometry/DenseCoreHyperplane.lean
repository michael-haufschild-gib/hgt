import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Dense-core hyperplane closure

A dense algebraic core remains dense after imposing one continuous linear constraint, provided the
core contains a normalized vector for that constraint.  The proof constructs the explicit
rank-one correction projection; it does not assume that the core injection is continuous.

This is the functional-analytic step needed to recover a closed codimension-one shifted range from
an exact moment identity on a smooth core.
-/

open Set Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.DenseCoreHyperplane

variable {𝕜 C H : Type*}
  [RCLike 𝕜]
  [AddCommGroup C] [Module 𝕜 C]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Correct a core vector by a normalized core direction so that one functional vanishes. -/
def correction (J : C →ₗ[𝕜] H) (φ : H →L[𝕜] 𝕜) (q : C) : C →ₗ[𝕜] H :=
  J - (LinearMap.toSpanSingleton 𝕜 H (J q)).comp (φ.toLinearMap.comp J)

@[simp] theorem correction_apply
    (J : C →ₗ[𝕜] H) (φ : H →L[𝕜] 𝕜) (q c : C) :
    correction J φ q c = J c - φ (J c) • J q := rfl

/-- The normalized core vector as a continuous right-inverse candidate for the functional. -/
def rightSection (J : C →ₗ[𝕜] H) (q : C) : 𝕜 →L[𝕜] H :=
  ContinuousLinearMap.toSpanSingleton 𝕜 (J q)

theorem rightSection_rightInverse
    (J : C →ₗ[𝕜] H) (φ : H →L[𝕜] 𝕜) (q : C)
    (hq : φ (J q) = 1) : Function.RightInverse (rightSection J q) φ := by
  intro c
  simp [rightSection, hq]

/-- Continuous rank-one projection onto the functional's kernel. -/
def projection
    (J : C →ₗ[𝕜] H) (φ : H →L[𝕜] 𝕜) (q : C)
    (hq : φ (J q) = 1) : H →L[𝕜] LinearMap.ker φ.toLinearMap :=
  φ.projKerOfRightInverse (rightSection J q) (rightSection_rightInverse J φ q hq)

@[simp] theorem projection_coe_apply
    (J : C →ₗ[𝕜] H) (φ : H →L[𝕜] 𝕜) (q : C)
    (hq : φ (J q) = 1) (x : H) :
    ((projection J φ q hq x : LinearMap.ker φ.toLinearMap) : H) =
      x - φ x • J q := by
  simp [projection, rightSection]

theorem projection_surjective
    (J : C →ₗ[𝕜] H) (φ : H →L[𝕜] 𝕜) (q : C)
    (hq : φ (J q) = 1) : Function.Surjective (projection J φ q hq) := by
  intro x
  refine ⟨x, ?_⟩
  apply Subtype.ext
  simp [projection]

/-- Algebraically, corrected core vectors are exactly core vectors in the hyperplane. -/
theorem range_correction_eq
    (J : C →ₗ[𝕜] H) (φ : H →L[𝕜] 𝕜) (q : C)
    (hq : φ (J q) = 1) :
    LinearMap.range (correction J φ q) =
      LinearMap.range J ⊓ LinearMap.ker φ.toLinearMap := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    constructor
    · refine ⟨c - φ (J c) • q, ?_⟩
      simp [correction]
    · change φ (correction J φ q c) = 0
      simp [correction, hq]
  · rintro ⟨⟨c, rfl⟩, hc⟩
    change φ (J c) = 0 at hc
    refine ⟨c, ?_⟩
    simp [correction, hc]

/-- The corrected dense core has dense range in the kernel subtype. -/
theorem denseRange_projection_comp
    (J : C →ₗ[𝕜] H) (φ : H →L[𝕜] 𝕜) (q : C)
    (hq : φ (J q) = 1) (hJ : DenseRange J) :
    DenseRange ((projection J φ q hq).toLinearMap.comp J) := by
  exact (projection_surjective J φ q hq).denseRange.comp hJ
    (projection J φ q hq).continuous

/-- **Dense-core hyperplane theorem.**  A dense core, corrected along a normalized core vector,
has ambient closure equal to the exact closed kernel of the functional. -/
theorem topologicalClosure_range_correction_eq_ker
    (J : C →ₗ[𝕜] H) (φ : H →L[𝕜] 𝕜) (q : C)
    (hq : φ (J q) = 1) (hJ : DenseRange J) :
    (LinearMap.range (correction J φ q)).topologicalClosure =
      LinearMap.ker φ.toLinearMap := by
  let K : Submodule 𝕜 H := LinearMap.ker φ.toLinearMap
  let P : H →L[𝕜] K := projection J φ q hq
  let S₀ : C →ₗ[𝕜] K := P.toLinearMap.comp J
  have hS₀ : DenseRange S₀ := by
    exact denseRange_projection_comp J φ q hq hJ
  have htop : (LinearMap.range S₀).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hS₀
  have hmap := (LinearMap.range S₀).topologicalClosure_map K.subtypeL
  have hrange_map_le :
      (LinearMap.range S₀).map K.subtype ≤ LinearMap.range (correction J φ q) := by
    rintro y ⟨z, ⟨c, rfl⟩, rfl⟩
    refine ⟨c, ?_⟩
    rfl
  have hK_le : K ≤ (LinearMap.range (correction J φ q)).topologicalClosure := by
    intro x hx
    have hxmap : x ∈ (⊤ : Submodule 𝕜 K).map K.subtype := by
      exact ⟨⟨x, hx⟩, Submodule.mem_top, rfl⟩
    rw [← htop] at hxmap
    have hxclosure : x ∈
        ((LinearMap.range S₀).map K.subtype).topologicalClosure := hmap hxmap
    exact Submodule.topologicalClosure_mono hrange_map_le hxclosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rw [range_correction_eq J φ q hq]
      exact inf_le_right
    · exact φ.isClosed_ker
  · exact hK_le

end GaloisForLFunctions.HTGeometry.DenseCoreHyperplane
