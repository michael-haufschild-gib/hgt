import GaloisForLFunctions.RHTower.KRealCompactlySupportedLocallyConstant
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-!
# Global translation stabilizers for nonarchimedean test functions

A compactly supported locally constant function on a nonarchimedean additive
group is invariant under one open additive subgroup, globally on its domain.
The proof equips the codomain with the discrete uniformity. Compact support then
upgrades continuity to uniform continuity; the equality entourage pulls back to
a neighborhood of zero, and nonarchimedeanness refines that neighborhood to an
open additive subgroup.

This is the abstract topological mechanism behind periodic rational lattice
weights and locally constant profinite parameters in finite-adèlic Poisson
summation.
-/

noncomputable section

open Filter Set Topology

namespace GaloisForLFunctions
namespace RHTower

/-- **Global nonarchimedean translation-stabilizer law.** -/
theorem compactlySupportedLocallyConstant_exists_openAddSubgroup_stabilizer
    (G Y : Type*) [AddCommGroup G] [TopologicalSpace G]
    [NonarchimedeanAddGroup G] [Zero Y]
    (f : G → Y) (hf : IsLocallyConstant f)
    (hcompact : HasCompactSupport f) :
    ∃ V : OpenAddSubgroup G, ∀ x (v : V), f (x + v.1) = f x := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  letI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace (WithDiscreteTopology Y) := ⊥
  letI : Zero (WithDiscreteTopology Y) :=
    ⟨WithTopology.toTopology ⊥ (0 : Y)⟩
  let fD : G → WithDiscreteTopology Y := fun x =>
    WithTopology.toTopology ⊥ (f x)
  have hfD : IsLocallyConstant fD :=
    hf.comp (WithTopology.toTopology ⊥)
  have hcont : Continuous fD := hfD.continuous
  have hcompact' : HasCompactSupport fD := by
    change IsCompact (closure (Function.support fD))
    rw [show Function.support fD = Function.support f by
      ext x
      change (¬WithTopology.toTopology ⊥ (f x) =
        WithTopology.toTopology ⊥ (0 : Y)) ↔ ¬f x = 0
      rw [WithTopology.toTopology_inj]]
    exact hcompact
  have hUC := hcompact'.uniformContinuous_of_continuous hcont
  have hrel := uniformContinuous_def.mp hUC SetRel.id
    (DiscreteUniformity.relId_mem_uniformity (WithDiscreteTopology Y))
  rw [uniformity_eq_comap_nhds_zero] at hrel
  obtain ⟨U, hU, hsub⟩ := hrel
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  refine ⟨V, fun x v => ?_⟩
  have hp : ((x, x + v.1) : G × G) ∈
      (fun p : G × G => p.2 - p.1) ⁻¹' U := by
    change x + v.1 - x ∈ U
    simpa [add_sub_cancel_left] using hV v.2
  have heq := hsub hp
  change fD x = fD (x + v.1) at heq
  exact (WithTopology.toTopology_injective ⊥ heq).symm

end RHTower
end GaloisForLFunctions
