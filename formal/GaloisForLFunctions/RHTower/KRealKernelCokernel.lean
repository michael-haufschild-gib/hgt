import Mathlib.Tactic
import Mathlib.Algebra.Module.LinearMap.Star
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Kernel and cokernel descent in Deninger's `K_R`

A parity-`odd` `KRealStructure` is a complex vector space with a conjugate-linear map whose
square is `+1` in even parity and `-1` in odd parity.  This file proves that an intertwining
complex-linear map has stable kernel and range, and that both its kernel and algebraic cokernel
inherit the same `KRealStructure`.

This is the formal categorical quotient step needed by a future `K_R` lift of the CCM
restriction morphism.  CCM's additional topological closure and the arithmetic construction of
the lift are deliberately not assumed here.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Parity action on an additive group: `false` acts by `+1`, `true` by `-1`. -/
def kRealParityAction {V : Type*} [AddCommGroup V] (odd : Bool) (v : V) : V :=
  if odd then -v else v

/-- A single even or odd object of Deninger's `K_R` coefficient category. -/
structure KRealStructure (odd : Bool) (V : Type*)
    [AddCommGroup V] [Module ℂ V] where
  sigma : V →ₗ⋆[ℂ] V
  sq : ∀ v, sigma (sigma v) = kRealParityAction odd v

/-- A complex-linear map intertwining two `KRealStructure`s of the same parity. -/
structure KRealMorphism {odd : Bool}
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (KV : KRealStructure odd V) (KW : KRealStructure odd W) where
  map : V →ₗ[ℂ] W
  commutes : ∀ v, KW.sigma (map v) = map (KV.sigma v)

namespace KRealStructure

variable {odd : Bool}
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- A complex submodule is stable when it is preserved by the conjugate-linear structure. -/
def StableSubmodule (K : KRealStructure odd V) (S : Submodule ℂ V) : Prop :=
  ∀ v ∈ S, K.sigma v ∈ S

/-- Conjugate-linear map induced on the quotient by a stable submodule. -/
def quotientSigma (K : KRealStructure odd V) (S : Submodule ℂ V)
    (hS : K.StableSubmodule S) :
    (V ⧸ S) →ₗ⋆[ℂ] (V ⧸ S) :=
  S.mapQ S K.sigma (by
    intro v hv
    exact hS v hv)

@[simp]
theorem quotientSigma_mkQ (K : KRealStructure odd V) (S : Submodule ℂ V)
    (hS : K.StableSubmodule S) (v : V) :
    K.quotientSigma S hS (S.mkQ v) = S.mkQ (K.sigma v) := by
  rfl

/-- The induced quotient structure has the same parity square. -/
theorem quotientSigma_sq (K : KRealStructure odd V) (S : Submodule ℂ V)
    (hS : K.StableSubmodule S) (x : V ⧸ S) :
    K.quotientSigma S hS (K.quotientSigma S hS x) =
      kRealParityAction odd x := by
  obtain ⟨v, rfl⟩ := S.mkQ_surjective x
  rw [quotientSigma_mkQ, quotientSigma_mkQ, K.sq]
  cases odd <;> simp [kRealParityAction]

/-- A stable quotient inherits its `KRealStructure`. -/
def quotient (K : KRealStructure odd V) (S : Submodule ℂ V)
    (hS : K.StableSubmodule S) :
    KRealStructure odd (V ⧸ S) where
  sigma := K.quotientSigma S hS
  sq := K.quotientSigma_sq S hS

/-- Restriction of the source conjugate-linear structure to an equivariant kernel. -/
def kernelSigma (KV : KRealStructure odd V) (KW : KRealStructure odd W)
    (f : KRealMorphism KV KW) :
    LinearMap.ker f.map →ₗ⋆[ℂ] LinearMap.ker f.map :=
  (KV.sigma.comp (LinearMap.ker f.map).subtype).codRestrict
    (LinearMap.ker f.map) (fun v => by
      change f.map (KV.sigma v) = 0
      rw [← f.commutes v, show f.map v = 0 from v.prop]
      exact map_zero KW.sigma)

/-- The restricted kernel structure has the source parity square. -/
theorem kernelSigma_sq (KV : KRealStructure odd V) (KW : KRealStructure odd W)
    (f : KRealMorphism KV KW) (v : LinearMap.ker f.map) :
    kernelSigma KV KW f (kernelSigma KV KW f v) =
      kRealParityAction odd v := by
  apply Subtype.ext
  change KV.sigma (KV.sigma (v : V)) =
    ((kRealParityAction odd v : LinearMap.ker f.map) : V)
  rw [KV.sq]
  cases odd <;> simp [kRealParityAction]

/-- Kernel of an equivariant map in the fixed parity of `K_R`. -/
def kernel (KV : KRealStructure odd V) (KW : KRealStructure odd W)
    (f : KRealMorphism KV KW) :
    KRealStructure odd (LinearMap.ker f.map) where
  sigma := kernelSigma KV KW f
  sq := kernelSigma_sq KV KW f

/-- The range of an equivariant map is stable under the target structure. -/
theorem range_stable (KV : KRealStructure odd V) (KW : KRealStructure odd W)
    (f : KRealMorphism KV KW) :
    KW.StableSubmodule (LinearMap.range f.map) := by
  intro w hw
  obtain ⟨v, rfl⟩ := hw
  rw [f.commutes]
  exact LinearMap.mem_range_self f.map (KV.sigma v)

/-- Algebraic cokernel of an equivariant map in the fixed parity of `K_R`. -/
def cokernel (KV : KRealStructure odd V) (KW : KRealStructure odd W)
    (f : KRealMorphism KV KW) :
    KRealStructure odd (W ⧸ LinearMap.range f.map) :=
  KW.quotient (LinearMap.range f.map) (range_stable KV KW f)

@[simp]
theorem cokernel_sigma_mkQ (KV : KRealStructure odd V) (KW : KRealStructure odd W)
    (f : KRealMorphism KV KW) (w : W) :
    (cokernel KV KW f).sigma ((LinearMap.range f.map).mkQ w) =
      (LinearMap.range f.map).mkQ (KW.sigma w) := by
  rfl

end KRealStructure

end RHTower
end GaloisForLFunctions
