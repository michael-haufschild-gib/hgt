import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.OpenSubgroup

/-! A character twist preserves the invariant subspaces of a
representation. It preserves smoothness when the character has
open kernel. -/

noncomputable section

namespace Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- Twist the action by a scalar character. -/
def scalarTwist (ρ : Representation ℂ G V) (χ : G →* ℂˣ) : Representation ℂ G V where
  toFun g := (χ g : ℂ) • ρ g
  map_one' := by simp
  map_mul' x y := by
    apply LinearMap.ext
    intro v
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul, mul_comm (χ x : ℂ) (χ y : ℂ)]

@[simp] theorem scalarTwist_apply (ρ : Representation ℂ G V) (χ : G →* ℂˣ) (g : G) (v : V) :
    scalarTwist ρ χ g v = (χ g : ℂ) • ρ g v := rfl

theorem scalarTwist_irreducible (ρ : Representation ℂ G V) [ρ.IsIrreducible] (χ : G →* ℂˣ) :
    (scalarTwist ρ χ).IsIrreducible := by
  let r := scalarTwist ρ χ
  letI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  letI : Nontrivial (Subrepresentation r) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  refine ⟨fun U => ?_⟩
  let S : Subrepresentation ρ :=
    ⟨U.toSubmodule, fun g {v} hv => by
      have he : ρ g v = ((χ g : ℂ)⁻¹) • r g v := by
        change ρ g v = ((χ g : ℂ)⁻¹) • ((χ g : ℂ) • ρ g v)
        rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
      rw [he]
      exact U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule g hv)⟩
  rcases eq_bot_or_eq_top S with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun T : Subrepresentation ρ => T.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun T : Subrepresentation ρ => T.toSubmodule) h

theorem scalarTwist_smooth [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) (hρ : ∀ v : V, IsOpen {g : G | ρ g v = v})
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) (v : V) :
    IsOpen {g : G | scalarTwist ρ χ g v = v} := by
  let r := scalarTwist ρ χ
  let S : Subgroup G :=
    { carrier := {g | r g v = v}
      one_mem' := by simp [r]
      mul_mem' := fun {x y} hx hy => by
        change r (x * y) v = v
        rw [map_mul, Module.End.mul_apply, show r y v = v from hy]
        exact hx
      inv_mem' := fun {x} hx => by
        change r x⁻¹ v = v
        nth_rw 1 [← show r x v = v from hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  apply Subgroup.isOpen_of_mem_nhds S (g := 1)
  have h1 : (1 : G) ∈ (χ.ker : Set G) ∩ {g : G | ρ g v = v} := by simp
  refine Filter.mem_of_superset ((hχ.inter (hρ v)).mem_nhds h1) ?_
  rintro g ⟨hg, hg'⟩
  change (χ g : ℂ) • ρ g v = v
  rw [show χ g = 1 from hg, Units.val_one, one_smul]
  exact hg'

end Representation

#print axioms Representation.scalarTwist_smooth
#print axioms Representation.scalarTwist_irreducible
