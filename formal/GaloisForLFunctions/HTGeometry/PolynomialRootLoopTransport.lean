import GaloisForLFunctions.HTGeometry.OrderedPolynomialRootTransport

open Polynomial Set Topology
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- Equal target values identify actual root fibers without changing a root. -/
def rootFiberEquivOfValueEq {n : ℕ} (v : Parameter n) {a b : ℂ} (h : a = b) :
    RootFiber v a ≃ RootFiber v b where
  toFun z := ⟨z.val, z.property.trans h⟩
  invFun z := ⟨z.val, z.property.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Unique continuation around a target loop as a permutation of its actual polynomial fiber. -/
def rootLoopTransport {n : ℕ} (v : Parameter n) {b : ℂ} (γ : Path b b)
    (havoid : ∀ t j, γ t ≠ valuesWithConstant v j) : Equiv.Perm (RootFiber v b) :=
  let e₀ : RootFiber v b ≃ RootFiber v (γ 0) := rootFiberEquivOfValueEq v γ.source.symm
  let e₁ : RootFiber v (γ 1) ≃ RootFiber v b := rootFiberEquivOfValueEq v γ.target
  e₀.trans ((rootTransportEquiv (ContinuousMap.const _ v) γ.toContinuousMap havoid 0 1).trans e₁)

/-- An explicit continuous polynomial root lift computes the actual loop permutation. -/
theorem rootLoopTransport_val_eq_of_section {n : ℕ} (v : Parameter n) {b : ℂ}
    (γ : Path b b) (havoid : ∀ t j, γ t ≠ valuesWithConstant v j)
    (z : RootFiber v b) (u : C(I, ℂ)) (hu₀ : u 0 = z)
    (hu : ∀ t, (additivePolynomial v).eval (u t) = γ t) :
    (rootLoopTransport v γ havoid z).val = u 1 := by
  change (rootTransport (ContinuousMap.const _ v) γ.toContinuousMap havoid 0 1
    ⟨z.val, z.property.trans γ.source.symm⟩).val = u 1
  exact rootTransport_val_eq_of_section (ContinuousMap.const I v) γ.toContinuousMap
    havoid 0 1 ⟨z.val, z.property.trans γ.source.symm⟩ u hu₀ hu

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
