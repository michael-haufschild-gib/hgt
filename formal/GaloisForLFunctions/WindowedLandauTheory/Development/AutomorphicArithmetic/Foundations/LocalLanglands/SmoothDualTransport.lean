import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothSubrepresentation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothIrreducibleTwist
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Module.Submodule.Equiv

/-! The smooth contragredient transports representation equivalences
and inverts smooth scalar twists. -/

noncomputable section

open Module

namespace Representation

variable {G V W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

private theorem equiv_apply (e : ρ.Equiv σ) (g : G) (v : V) :
    e.toLinearEquiv (ρ g v) = σ g (e.toLinearEquiv v) :=
  IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v

def Equiv.smoothPart (e : ρ.Equiv σ) : ρ.smoothPart.Equiv σ.smoothPart := by
  have hmem (v : V) : e.toLinearEquiv v ∈ σ.smoothVectors ↔ v ∈ ρ.smoothVectors := by
    rw [mem_smoothVectors, mem_smoothVectors]
    have he : {g | σ g (e.toLinearEquiv v) = e.toLinearEquiv v} = {g | ρ g v = v} :=
      Set.ext fun g => by simp only [Set.mem_setOf_eq, ← equiv_apply e, e.toLinearEquiv.injective.eq_iff]
    rw [he]
  have he : ρ.smoothVectors.map e.toLinearEquiv.toLinearMap = σ.smoothVectors := by
    ext w
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hmem v).mpr hv
    · intro hw
      obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
      exact ⟨v, (hmem v).mp hw, rfl⟩
  refine Equiv.mk (e.toLinearEquiv.ofSubmodules _ _ he) fun g => LinearMap.ext fun v => ?_
  exact Subtype.ext (equiv_apply e g v.val)

private def algebraicDualEquiv (e : ρ.Equiv σ) : ρ.dual.Equiv σ.dual :=
  Equiv.mk e.symm.toLinearEquiv.dualMap fun g => LinearMap.ext fun l => LinearMap.ext fun w => by
    change l (ρ g⁻¹ (e.symm.toLinearEquiv w)) = l (e.symm.toLinearEquiv (σ g⁻¹ w))
    exact congrArg l (equiv_apply e.symm g⁻¹ w).symm

def Equiv.smoothDual (e : ρ.Equiv σ) : ρ.smoothDual.Equiv σ.smoothDual :=
  (algebraicDualEquiv e).smoothPart

private theorem smoothVectors_scalarTwist (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) : (ρ.scalarTwist χ).smoothVectors = ρ.smoothVectors := by
  ext v
  constructor
  · intro hv
    exact ρ.isOpen_vectorStabilizer_of_open_subgroup (H := χ.ker ⊓ (ρ.scalarTwist χ).vectorStabilizer v)
      (hχ.inter hv) fun g hg => by
        have hf := ((ρ.scalarTwist χ).mem_vectorStabilizer v g).mp hg.2
        rwa [scalarTwist_apply, MonoidHom.mem_ker.mp hg.1, Units.val_one, one_smul] at hf
  · intro hv
    exact (ρ.scalarTwist χ).isOpen_vectorStabilizer_of_open_subgroup
      (H := χ.ker ⊓ ρ.vectorStabilizer v) (hχ.inter hv) fun g hg => by
        rw [scalarTwist_apply, MonoidHom.mem_ker.mp hg.1, Units.val_one, one_smul]
        exact (ρ.mem_vectorStabilizer v g).mp hg.2

/-- Taking the smooth part commutes with twisting by a smooth character. -/
def smoothPartScalarTwistEquiv (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) :
    (ρ.scalarTwist χ).smoothPart.Equiv (ρ.smoothPart.scalarTwist χ) :=
  Equiv.mk (LinearEquiv.ofEq _ _ (smoothVectors_scalarTwist ρ χ hχ))
    fun g => LinearMap.ext fun v => Subtype.ext rfl

private theorem scalarTwist_dual (ρ : Representation ℂ G V) (χ : G →* ℂˣ) :
    (ρ.scalarTwist χ).dual = ρ.dual.scalarTwist χ⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro v
  change f ((χ g⁻¹ : ℂ) • ρ g⁻¹ v) = (χ⁻¹ g : ℂˣ) • f (ρ g⁻¹ v)
  rw [map_smul, map_inv]
  rfl

private def smoothPartCongr (r s : Representation ℂ G V) (he : r = s) :
    r.smoothPart.Equiv s.smoothPart := by
  subst s
  exact Equiv.refl _

def smoothDualScalarTwistEquiv (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) :
    (ρ.scalarTwist χ).smoothDual.Equiv (ρ.smoothDual.scalarTwist χ⁻¹) :=
  (smoothPartCongr _ _ (scalarTwist_dual ρ χ)).trans
    (smoothPartScalarTwistEquiv ρ.dual χ⁻¹ (isOpen_ker_inv χ hχ))

end Representation

#print axioms Representation.Equiv.smoothDual
#print axioms Representation.smoothDualScalarTwistEquiv
