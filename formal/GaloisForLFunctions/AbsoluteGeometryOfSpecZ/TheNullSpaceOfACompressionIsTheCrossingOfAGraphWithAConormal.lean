import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The null space of a compression is the crossing of a graph with a conormal

On `H × H`, `H` a Hilbert space, the form `ω((x, y), (x', y')) = ⟨y, x'⟩ − ⟨x, y'⟩` is
symplectic (`sympForm`). Two kinds of subspaces are Lagrangian for it, equal to their own
annihilator:

* the graph of a self-adjoint operator `T` (`mem_operatorGraph_iff_forall_sympForm`);
* the conormal `K × Kᗮ` of a closed subspace `K` (`mem_conormal_iff_forall_sympForm`).

The graph of `T` meets the conormal of `K` in the vectors `x ∈ K` with `T x ⊥ K`
(`mem_operatorGraph_inf_conormal`): the null space of the form of `T` restricted to `K`. If `K`
is the image of an isometry `ι : G → H` and `S` is the compression of `T` to `G`,
`⟨T ι u, ι v⟩ = ⟨S u, v⟩`, the crossing has the dimension of the kernel of `S`
(`finrank_operatorGraph_inf_conormal`).
-/

open Module
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The symplectic form on `H × H`. -/
def sympForm (p q : H × H) : ℂ :=
  ⟪p.2, q.1⟫_ℂ - ⟪p.1, q.2⟫_ℂ

/-- The graph of an operator. -/
def operatorGraph (T : H →L[ℂ] H) : Submodule ℂ (H × H) :=
  (T : H →ₗ[ℂ] H).graph

theorem mem_operatorGraph {T : H →L[ℂ] H} {p : H × H} : p ∈ operatorGraph T ↔ p.2 = T p.1 :=
  LinearMap.mem_graph_iff _ p

/-- The conormal of a subspace `K`: a vector of `K` paired with a vector orthogonal to `K`. -/
def conormal (K : Submodule ℂ H) : Submodule ℂ (H × H) :=
  K.prod Kᗮ

theorem mem_conormal {K : Submodule ℂ H} {p : H × H} : p ∈ conormal K ↔ p.1 ∈ K ∧ p.2 ∈ Kᗮ :=
  Submodule.mem_prod

/-- **The graph of a self-adjoint operator is Lagrangian**: it is its own annihilator for the
symplectic form. -/
theorem mem_operatorGraph_iff_forall_sympForm [CompleteSpace H] {T : H →L[ℂ] H}
    (hT : IsSelfAdjoint T) (p : H × H) :
    p ∈ operatorGraph T ↔ ∀ q ∈ operatorGraph T, sympForm p q = 0 := by
  have hsymm : ∀ x y : H, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
    intro x y
    have h := ContinuousLinearMap.adjoint_inner_left T y x
    rwa [hT.adjoint_eq] at h
  constructor
  · intro hp q hq
    rw [mem_operatorGraph] at hp hq
    rw [sympForm, hp, hq, hsymm, sub_self]
  · intro h
    rw [mem_operatorGraph]
    refine ext_inner_right ℂ fun x => ?_
    have h1 : ⟪p.2, x⟫_ℂ - ⟪p.1, T x⟫_ℂ = 0 := h (x, T x) (mem_operatorGraph.mpr rfl)
    rw [hsymm]
    exact sub_eq_zero.mp h1

/-- **The conormal of a closed subspace is Lagrangian.** -/
theorem mem_conormal_iff_forall_sympForm (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (p : H × H) : p ∈ conormal K ↔ ∀ q ∈ conormal K, sympForm p q = 0 := by
  constructor
  · rintro ⟨h1, h2⟩ q ⟨hq1, hq2⟩
    rw [sympForm, Submodule.inner_left_of_mem_orthogonal hq1 h2,
      Submodule.inner_right_of_mem_orthogonal h1 hq2, sub_zero]
  · intro h
    refine mem_conormal.mpr ⟨?_, ?_⟩
    · have hmem : p.1 ∈ Kᗮᗮ := by
        rw [Submodule.mem_orthogonal']
        intro y hy
        have h1 : ⟪p.2, (0 : H)⟫_ℂ - ⟪p.1, y⟫_ℂ = 0 :=
          h (0, y) (mem_conormal.mpr ⟨K.zero_mem, hy⟩)
        rwa [inner_zero_right, zero_sub, neg_eq_zero] at h1
      rwa [Submodule.orthogonal_orthogonal] at hmem
    · rw [Submodule.mem_orthogonal']
      intro x hx
      have h1 : ⟪p.2, x⟫_ℂ - ⟪p.1, (0 : H)⟫_ℂ = 0 :=
        h (x, 0) (mem_conormal.mpr ⟨hx, Kᗮ.zero_mem⟩)
      rwa [inner_zero_right, sub_zero] at h1

/-- The graph meets the conormal of `K` in the vectors of `K` that `T` maps orthogonally to
`K`. -/
theorem mem_operatorGraph_inf_conormal {T : H →L[ℂ] H} {K : Submodule ℂ H} {p : H × H} :
    p ∈ operatorGraph T ⊓ conormal K ↔ p.2 = T p.1 ∧ p.1 ∈ K ∧ T p.1 ∈ Kᗮ := by
  rw [Submodule.mem_inf, mem_operatorGraph, mem_conormal]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rwa [h1] at h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rwa [h1]⟩

/-- The image of an isometry of a complete space admits an orthogonal projection. -/
theorem hasOrthogonalProjection_range_isometry [CompleteSpace G] (ι : G →ₗᵢ[ℂ] H) :
    (LinearMap.range ι.toLinearMap).HasOrthogonalProjection := by
  haveI : CompleteSpace (LinearMap.range ι.toLinearMap) :=
    (completeSpace_coe_iff_isComplete (s := (LinearMap.range ι.toLinearMap : Set H))).mpr (by
      rw [LinearMap.coe_range]
      exact ι.isometry.isUniformInducing.isComplete_range)
  infer_instance

/-- **The crossing of the graph of `T` with the conormal of the image of an isometry has the
dimension of the kernel of the compression of `T`.** -/
theorem finrank_operatorGraph_inf_conormal (ι : G →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (S : G →L[ℂ] G)
    (hcomp : ∀ u v : G, ⟪T (ι u), ι v⟫_ℂ = ⟪S u, v⟫_ℂ) :
    finrank ℂ ↥(operatorGraph T ⊓ conormal (LinearMap.range ι.toLinearMap)) =
      finrank ℂ (LinearMap.ker (S : G →ₗ[ℂ] G)) := by
  obtain ⟨f, hf⟩ : ∃ f : G →ₗ[ℂ] H × H,
      f = ι.toLinearMap.prod ((T : H →ₗ[ℂ] H).comp ι.toLinearMap) := ⟨_, rfl⟩
  have hfapp : ∀ u, f u = (ι u, T (ι u)) := fun u => by rw [hf]; rfl
  have hinj : Function.Injective f := fun u v h => by
    rw [hfapp, hfapp] at h
    exact ι.injective (congrArg Prod.fst h)
  have hmap : operatorGraph T ⊓ conormal (LinearMap.range ι.toLinearMap) =
      (LinearMap.ker (S : G →ₗ[ℂ] G)).map f := by
    ext p
    rw [mem_operatorGraph_inf_conormal, Submodule.mem_map]
    constructor
    · rintro ⟨h1, ⟨u, hu⟩, h3⟩
      have hι : ι u = p.1 := hu
      refine ⟨u, ?_, ?_⟩
      · show S u = 0
        refine ext_inner_right ℂ fun v => ?_
        rw [inner_zero_left, ← hcomp, hι]
        exact (Submodule.mem_orthogonal' _ _).mp h3 (ι v) ⟨v, rfl⟩
      · rw [hfapp, hι]
        exact Prod.ext rfl h1.symm
    · rintro ⟨u, hu, rfl⟩
      have hSu : S u = 0 := hu
      rw [hfapp]
      refine ⟨rfl, ⟨u, rfl⟩, ?_⟩
      rw [Submodule.mem_orthogonal']
      rintro _ ⟨v, rfl⟩
      show ⟪T (ι u), ι v⟫_ℂ = 0
      rw [hcomp, hSu, inner_zero_left]
  rw [hmap]
  exact (Submodule.equivMapOfInjective f hinj _).finrank_eq.symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
