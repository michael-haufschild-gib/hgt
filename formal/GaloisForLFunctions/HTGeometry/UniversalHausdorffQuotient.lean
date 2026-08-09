import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Universal Hausdorff reflection of a topological additive quotient

For an additive subgroup `H` of a Hausdorff topological abelian group `G`, the canonical map
`G/H → G/closure(H)` is the Hausdorff reflection.  This file constructs the map as a continuous
additive homomorphism and proves its exact kernel, the closure-of-zero formula, the Hausdorff
criterion, and the universal factorization property.
-/

open Set Topology ContinuousMonoidHom QuotientAddGroup

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

variable {G Y : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

/-- The quotient projection as a bundled continuous additive homomorphism. -/
def quotientAddGroupMk (H : AddSubgroup G) : G →ₜ+ G ⧸ H where
  toAddMonoidHom := QuotientAddGroup.mk' H
  continuous_toFun := QuotientAddGroup.continuous_mk

@[simp]
theorem quotientAddGroupMk_apply (H : AddSubgroup G) (x : G) :
    quotientAddGroupMk H x = QuotientAddGroup.mk' H x := rfl

/-- Canonical map from a quotient to the quotient by the topological closure. -/
def hausdorffReflectionMap (H : AddSubgroup G) :
    (G ⧸ H) →ₜ+ (G ⧸ H.topologicalClosure) where
  toAddMonoidHom := QuotientAddGroup.lift H (QuotientAddGroup.mk' H.topologicalClosure) (by
    simpa only [QuotientAddGroup.ker_mk'] using H.le_topologicalClosure)
  continuous_toFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk H).continuous_iff]
    change Continuous fun x : G => QuotientAddGroup.lift H
      (QuotientAddGroup.mk' H.topologicalClosure) _ (QuotientAddGroup.mk' H x)
    convert QuotientAddGroup.continuous_mk (N := H.topologicalClosure) using 1
    funext x
    exact QuotientAddGroup.lift_mk' _ _ x

@[simp]
theorem hausdorffReflectionMap_mk (H : AddSubgroup G) (x : G) :
    hausdorffReflectionMap H (QuotientAddGroup.mk' H x) =
      QuotientAddGroup.mk' H.topologicalClosure x := rfl

/-- The canonical Hausdorff-reflection map is onto. -/
theorem hausdorffReflectionMap_surjective (H : AddSubgroup G) :
    Function.Surjective (hausdorffReflectionMap H) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H.topologicalClosure y
  exact ⟨QuotientAddGroup.mk' H x, rfl⟩

/-- Exact subgroup `closure(H)/H` inside `G/H`. -/
def closureModuloSubgroup (H : AddSubgroup G) : AddSubgroup (G ⧸ H) :=
  H.topologicalClosure.map (QuotientAddGroup.mk' H)

/-- The kernel of `G/H → G/closure(H)` is literally the image `closure(H)/H`. -/
theorem hausdorffReflectionMap_ker (H : AddSubgroup G) :
    (hausdorffReflectionMap H).ker = closureModuloSubgroup H := by
  let hle : H ≤ (QuotientAddGroup.mk' H.topologicalClosure).ker := by
    simpa only [QuotientAddGroup.ker_mk'] using H.le_topologicalClosure
  change (QuotientAddGroup.lift H (QuotientAddGroup.mk' H.topologicalClosure) hle).ker =
    H.topologicalClosure.map (QuotientAddGroup.mk' H)
  rw [QuotientAddGroup.ker_lift, QuotientAddGroup.ker_mk']

/-- In `G/H`, the closure of the zero subgroup is exactly `closure(H)/H`. -/
theorem topologicalClosure_zero_eq_closureModuloSubgroup (H : AddSubgroup G) :
    (⊥ : AddSubgroup (G ⧸ H)).topologicalClosure = closureModuloSubgroup H := by
  apply SetLike.ext'
  rw [AddSubgroup.coe_topologicalClosure_bot]
  apply (QuotientAddGroup.mk'_surjective H).preimage_injective
  have hpre : (QuotientAddGroup.mk' H) ⁻¹' closure ({0} : Set (G ⧸ H)) =
      closure (H : Set G) := by
    change QuotientAddGroup.mk ⁻¹' closure ({0} : Set (G ⧸ H)) = closure (H : Set G)
    rw [QuotientAddGroup.isOpenMap_coe.preimage_closure_eq_closure_preimage
      QuotientAddGroup.continuous_mk]
    congr 1
    ext x
    exact QuotientAddGroup.eq_zero_iff x
  rw [hpre]
  rw [← AddSubgroup.topologicalClosure_coe]
  rw [closureModuloSubgroup, AddSubgroup.coe_map,
    show (QuotientAddGroup.mk' H : G → G ⧸ H) = QuotientAddGroup.mk from rfl,
    QuotientAddGroup.preimage_image_mk_eq_add]
  rw [← AddSubgroup.add_normal]
  exact
    congrArg ((↑) : AddSubgroup G → Set G) (sup_eq_left.mpr H.le_topologicalClosure).symm

/-- A topological additive quotient is Hausdorff exactly when its subgroup is closed. -/
theorem quotient_t2Space_iff_isClosed [T2Space G] (H : AddSubgroup G) :
    T2Space (G ⧸ H) ↔ IsClosed (H : Set G) := by
  constructor
  · intro h
    letI : T2Space (G ⧸ H) := h
    exact QuotientAddGroup.t1Space_iff.mp inferInstance
  · intro h
    letI : IsClosed (H : Set G) := h
    infer_instance

/-- A continuous homomorphism from `G/H` to a Hausdorff group kills `closure(H)` after pullback. -/
theorem topologicalClosure_le_ker_comp_quotient
    [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] [T2Space Y]
    (H : AddSubgroup G) (f : (G ⧸ H) →ₜ+ Y) :
    H.topologicalClosure ≤ (f.comp (quotientAddGroupMk H)).ker := by
  apply H.topologicalClosure_minimal
  · intro x hx
    change f (QuotientAddGroup.mk' H x) = 0
    have hzero : QuotientAddGroup.mk' H x = 0 := (QuotientAddGroup.eq_zero_iff x).mpr hx
    rw [hzero, map_zero]
  · exact isClosed_singleton.preimage (f.comp (quotientAddGroupMk H)).continuous

/-- Universal factor of a Hausdorff-valued quotient homomorphism through `G/closure(H)`. -/
def hausdorffReflectionLift
    [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] [T2Space Y]
    (H : AddSubgroup G) (f : (G ⧸ H) →ₜ+ Y) :
    (G ⧸ H.topologicalClosure) →ₜ+ Y where
  toAddMonoidHom := QuotientAddGroup.lift H.topologicalClosure
    (f.comp (quotientAddGroupMk H)).toAddMonoidHom
    (topologicalClosure_le_ker_comp_quotient H f)
  continuous_toFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk H.topologicalClosure).continuous_iff]
    change Continuous fun x : G => QuotientAddGroup.lift H.topologicalClosure
      (f.comp (quotientAddGroupMk H)).toAddMonoidHom _
      (QuotientAddGroup.mk' H.topologicalClosure x)
    convert (f.comp (quotientAddGroupMk H)).continuous using 1
    funext x
    exact QuotientAddGroup.lift_mk' _ _ x

@[simp]
theorem hausdorffReflectionLift_mk
    [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] [T2Space Y]
    (H : AddSubgroup G) (f : (G ⧸ H) →ₜ+ Y) (x : G) :
    hausdorffReflectionLift H f (QuotientAddGroup.mk' H.topologicalClosure x) =
      f (QuotientAddGroup.mk' H x) := rfl

/-- The universal lift factors the original map through the canonical reflection map. -/
theorem hausdorffReflectionLift_comp
    [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] [T2Space Y]
    (H : AddSubgroup G) (f : (G ⧸ H) →ₜ+ Y) :
    (hausdorffReflectionLift H f).comp (hausdorffReflectionMap H) = f := by
  ext x
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H x
  rfl

/-- Full universal property: unique continuous additive factorization to every Hausdorff group. -/
theorem hausdorffReflection_universal
    [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] [T2Space Y]
    (H : AddSubgroup G) (f : (G ⧸ H) →ₜ+ Y) :
    ∃! g : (G ⧸ H.topologicalClosure) →ₜ+ Y,
      g.comp (hausdorffReflectionMap H) = f := by
  refine ⟨hausdorffReflectionLift H f, hausdorffReflectionLift_comp H f, ?_⟩
  intro g hg
  ext x
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H.topologicalClosure x
  have h := DFunLike.congr_fun hg (QuotientAddGroup.mk' H x)
  rw [hausdorffReflectionLift_mk]
  exact h

/-- Consolidated Hausdorff-reflection theorem, including exact kernel and identity closure. -/
theorem hausdorffReflectionQuotient_theorem
    [T2Space G] [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] [T2Space Y]
    (H : AddSubgroup G) (f : (G ⧸ H) →ₜ+ Y) :
    Function.Surjective (hausdorffReflectionMap H) ∧
      (hausdorffReflectionMap H).ker = closureModuloSubgroup H ∧
      (⊥ : AddSubgroup (G ⧸ H)).topologicalClosure = closureModuloSubgroup H ∧
      (T2Space (G ⧸ H) ↔ IsClosed (H : Set G)) ∧
      ∃! g : (G ⧸ H.topologicalClosure) →ₜ+ Y,
        g.comp (hausdorffReflectionMap H) = f := by
  exact ⟨hausdorffReflectionMap_surjective H,
    hausdorffReflectionMap_ker H,
    topologicalClosure_zero_eq_closureModuloSubgroup H,
    quotient_t2Space_iff_isClosed H,
    hausdorffReflection_universal H f⟩

section QuotientEquivalences

variable {G₁ G₂ K : Type*}
  [TopologicalSpace G₁] [AddCommGroup G₁] [IsTopologicalAddGroup G₁]
  [TopologicalSpace G₂] [AddCommGroup G₂] [IsTopologicalAddGroup G₂]
  [TopologicalSpace K] [AddCommGroup K] [IsTopologicalAddGroup K]

/-- The algebraic equivalence `(G₁ × G₂)/(A × B) ≃ G₁/A × G₂/B` is a
homeomorphism for the quotient topologies. -/
def quotientProdContinuousAddEquiv (A : AddSubgroup G₁) (B : AddSubgroup G₂) :
    ((G₁ × G₂) ⧸ (A.prod B)) ≃ₜ+ ((G₁ ⧸ A) × (G₂ ⧸ B)) where
  toAddEquiv := QuotientAddGroup.prodAddEquiv A B
  continuous_toFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk (A.prod B)).continuous_iff]
    change Continuous fun x : G₁ × G₂ =>
      (QuotientAddGroup.mk' A x.1, QuotientAddGroup.mk' B x.2)
    exact (QuotientAddGroup.continuous_mk.comp continuous_fst).prodMk
      (QuotientAddGroup.continuous_mk.comp continuous_snd)
  continuous_invFun := by
    let hq := (QuotientAddGroup.isOpenQuotientMap_mk (N := A)).prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N := B))
    rw [hq.isQuotientMap.continuous_iff]
    change Continuous fun x : G₁ × G₂ => QuotientAddGroup.mk' (A.prod B) x
    exact QuotientAddGroup.continuous_mk

@[simp]
theorem quotientProdContinuousAddEquiv_mk
    (A : AddSubgroup G₁) (B : AddSubgroup G₂) (x : G₁ × G₂) :
    quotientProdContinuousAddEquiv A B (QuotientAddGroup.mk' (A.prod B) x) =
      (QuotientAddGroup.mk' A x.1, QuotientAddGroup.mk' B x.2) := rfl

/-- A continuous additive equivalence induces a continuous equivalence of quotient groups when it
maps the source subgroup exactly onto the target subgroup. -/
def quotientContinuousAddEquiv (e : G₁ ≃ₜ+ K)
    (A : AddSubgroup G₁) (B : AddSubgroup K)
    (hAB : A.map e.toAddEquiv.toAddMonoidHom = B) :
    (G₁ ⧸ A) ≃ₜ+ (K ⧸ B) where
  toAddEquiv := QuotientAddGroup.congr A B e.toAddEquiv hAB
  continuous_toFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk A).continuous_iff]
    change Continuous fun x : G₁ => QuotientAddGroup.mk' B (e x)
    exact QuotientAddGroup.continuous_mk.comp e.continuous
  continuous_invFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk B).continuous_iff]
    change Continuous fun x : K => QuotientAddGroup.mk' A (e.symm x)
    exact QuotientAddGroup.continuous_mk.comp e.symm.continuous

@[simp]
theorem quotientContinuousAddEquiv_mk (e : G₁ ≃ₜ+ K)
    (A : AddSubgroup G₁) (B : AddSubgroup K)
    (hAB : A.map e.toAddEquiv.toAddMonoidHom = B) (x : G₁) :
    quotientContinuousAddEquiv e A B hAB (QuotientAddGroup.mk' A x) =
      QuotientAddGroup.mk' B (e x) := rfl

end QuotientEquivalences

end

end HTGeometry
end GaloisForLFunctions
