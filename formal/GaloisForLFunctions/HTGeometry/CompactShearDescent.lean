import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Compact families and unmatched vanishing-cycle directions

A compact subset of a Hausdorff complex topological vector space cannot contain a
nonconstant affine integer lattice: that lattice is closed and discrete. This gives an exact
classification of continuous families of linear maps stable under all integer shear translates.
They descend uniquely through the quotient by the span of the shear images, and the descended
family remains continuous under every evaluation.

This is an affine topological obstruction. It does not identify the monodromy of a geometric
family, assert compactness of an arbitrary infinite cover, or classify projective-valued maps.
The proof uses closed embeddings and compactness, with no orbit estimate or positive form.
-/

open Topology


namespace HTGeometry.CompactShear

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]

/-- A compact set contains no nonconstant translated integer lattice. -/
theorem lattice_direction_eq_zero {K : Set E} (hK : IsCompact K)
    (v w : E) (h : ∀ n : ℤ, v + (n : ℂ) • w ∈ K) : w = 0 := by
  by_contra hw
  have he : IsClosedEmbedding (fun n : ℤ => v + (n : ℂ) • w) :=
    (Homeomorph.addLeft v).isClosedEmbedding.comp
      ((isClosedEmbedding_smul_left (𝕜 := ℂ) hw).comp
        Complex.isClosedEmbedding_intCast)
  have hc := he.isCompact_preimage hK
  have hu : (fun n : ℤ => v + (n : ℂ) • w) ⁻¹' K = Set.univ := by
    ext n
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact h n
  rw [hu] at hc
  exact Set.infinite_univ (isCompact_iff_finite.mp hc)

end HTGeometry.CompactShear

namespace HTGeometry.CompactShear

variable {X V E ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [AddCommGroup V] [Module ℂ V]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]

/-- Every integer shear translate of a family member occurs in the same family. -/
def IntegerShearStable (A : X → V →ₗ[ℂ] E) (N : ι → V →ₗ[ℂ] V) : Prop :=
  ∀ i x (n : ℤ), ∃ y, ∀ v, A y v = A x v + (n : ℂ) • A x (N i v)

/-- The source directions swept out by all prescribed shears. -/
def shearSpan (N : ι → V →ₗ[ℂ] V) : Submodule ℂ V :=
  ⨆ i, (N i).range

/-- Compact shear stability is exactly pointwise annihilation of every shear image. -/
theorem integerShearStable_iff_annihilates
    (A : X → V →ₗ[ℂ] E) (N : ι → V →ₗ[ℂ] V)
    (hA : ∀ v, Continuous (fun x => A x v)) :
    IntegerShearStable A N ↔ ∀ x i v, A x (N i v) = 0 := by
  constructor
  · intro h x i v
    apply lattice_direction_eq_zero (isCompact_range (hA v)) (A x v)
    intro n
    obtain ⟨y, hy⟩ := h i x n
    exact ⟨y, hy v⟩
  · intro h i x n
    refine ⟨x, ?_⟩
    intro v
    simp only [h x i v, smul_zero, add_zero]

/-- All transported vanishing-cycle directions lie in every comparison kernel. -/
theorem integerShearStable_iff_span_le_ker
    (A : X → V →ₗ[ℂ] E) (N : ι → V →ₗ[ℂ] V)
    (hA : ∀ v, Continuous (fun x => A x v)) :
    IntegerShearStable A N ↔ ∀ x, shearSpan N ≤ (A x).ker := by
  rw [integerShearStable_iff_annihilates A N hA]
  constructor
  · intro h x
    apply iSup_le
    intro i v hv
    obtain ⟨w, rfl⟩ := hv
    exact h x i w
  · intro h x i v
    exact h x ((le_iSup (fun i => (N i).range) i) ⟨v, rfl⟩)

/-- The quotient by the swept source directions is the exact positive survivor. -/
theorem integerShearStable_iff_unique_quotient
    (A : X → V →ₗ[ℂ] E) (N : ι → V →ₗ[ℂ] V)
    (hA : ∀ v, Continuous (fun x => A x v)) :
    IntegerShearStable A N ↔
      ∀ x, ∃! B : (V ⧸ shearSpan N) →ₗ[ℂ] E,
        B.comp (shearSpan N).mkQ = A x := by
  rw [integerShearStable_iff_span_le_ker A N hA]
  constructor
  · intro h x
    refine ⟨(shearSpan N).liftQ (A x) (h x), Submodule.liftQ_mkQ _ _ _, ?_⟩
    intro B hB
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := (shearSpan N).mkQ_surjective q
    exact LinearMap.congr_fun hB v
  · intro h x v hv
    obtain ⟨B, hB, _⟩ := h x
    have hzero : (shearSpan N).mkQ v = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (shearSpan N)).mpr hv
    have he := LinearMap.congr_fun hB v
    change A x v = 0
    simpa only [LinearMap.comp_apply, hzero, map_zero] using he.symm

/-- If the transported directions span the source, every family member vanishes. -/
theorem integerShearStable_eq_zero_of_span_eq_top
    (A : X → V →ₗ[ℂ] E) (N : ι → V →ₗ[ℂ] V)
    (hA : ∀ v, Continuous (fun x => A x v))
    (h : IntegerShearStable A N) (hspan : shearSpan N = ⊤) : A = 0 := by
  funext x
  ext v
  have hk := (integerShearStable_iff_span_le_ker A N hA).mp h x
  rw [hspan] at hk
  exact hk (Submodule.mem_top)

/-- Quotient descent preserves continuity under each evaluation. -/
theorem integerShearStable_continuous_quotient
    (A : X → V →ₗ[ℂ] E) (N : ι → V →ₗ[ℂ] V)
    (hA : ∀ v, Continuous (fun x => A x v))
    (h : IntegerShearStable A N) :
    ∃ B : X → (V ⧸ shearSpan N) →ₗ[ℂ] E,
      (∀ q, Continuous (fun x => B x q)) ∧
      ∀ x, (B x).comp (shearSpan N).mkQ = A x := by
  have hk := (integerShearStable_iff_span_le_ker A N hA).mp h
  refine ⟨fun x => (shearSpan N).liftQ (A x) (hk x), ?_, ?_⟩
  · intro q
    obtain ⟨v, rfl⟩ := (shearSpan N).mkQ_surjective q
    exact hA v
  · intro x
    exact Submodule.liftQ_mkQ _ _ _

end HTGeometry.CompactShear
