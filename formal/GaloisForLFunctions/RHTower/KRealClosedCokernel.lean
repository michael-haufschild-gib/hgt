import GaloisForLFunctions.RHTower.KRealKernelCokernel
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Closed-image cokernels in Deninger's `K_R`

Connes--Consani--Marcolli define their relative cyclic object by quotienting by the closure of
the restriction image.  This file proves the required topological descent: a continuous
conjugate-linear `KRealStructure` preserving a complex submodule also preserves its topological
closure.  The closed-image cokernel therefore inherits the same real or quaternionic square.

The theorem is purely categorical.  It assumes no arithmetic lift, positivity, zero spectrum, or
Riemann-hypothesis statement.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower
namespace KRealStructure

variable {odd : Bool}
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
variable [TopologicalSpace W] [ContinuousSMul ℂ W] [ContinuousAdd W]

/-- A continuous `K_R` structure preserving a submodule also preserves its closure. -/
theorem topologicalClosure_stable
    (KW : KRealStructure odd W) (S : Submodule ℂ W)
    (hσ : Continuous KW.sigma) (hS : KW.StableSubmodule S) :
    KW.StableSubmodule S.topologicalClosure := by
  intro w hw
  have hm : Set.MapsTo KW.sigma (S : Set W) (S : Set W) := by
    intro x hx
    exact hS x hx
  exact hm.closure hσ hw

/-- Quotient by the closure of a stable submodule, with inherited `K_R` structure. -/
def closedQuotient
    (KW : KRealStructure odd W) (S : Submodule ℂ W)
    (hσ : Continuous KW.sigma) (hS : KW.StableSubmodule S) :
    KRealStructure odd (W ⧸ S.topologicalClosure) :=
  KW.quotient S.topologicalClosure (topologicalClosure_stable KW S hσ hS)

/-- Closed-image cokernel of an equivariant map, as used in the CCM relative construction. -/
def closedCokernel
    (KV : KRealStructure odd V) (KW : KRealStructure odd W)
    (f : KRealMorphism KV KW) (hσ : Continuous KW.sigma) :
    KRealStructure odd (W ⧸ (LinearMap.range f.map).topologicalClosure) :=
  closedQuotient KW (LinearMap.range f.map) hσ (range_stable KV KW f)

@[simp]
theorem closedCokernel_sigma_mkQ
    (KV : KRealStructure odd V) (KW : KRealStructure odd W)
    (f : KRealMorphism KV KW) (hσ : Continuous KW.sigma) (w : W) :
    (closedCokernel KV KW f hσ).sigma
        ((LinearMap.range f.map).topologicalClosure.mkQ w) =
      (LinearMap.range f.map).topologicalClosure.mkQ (KW.sigma w) := by
  rfl

end KRealStructure
end RHTower
end GaloisForLFunctions
