import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Tensor products of linear maps with equal kernels

Over a field, replacing one tensor factor map by another map with the same kernel does not change
the kernel of the resulting tensor-product map.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- The kernel of a tensor-product map depends on a factor map only through that factor's kernel. -/
theorem tensorProduct_map_ker_eq_of_right_ker_eq
    {k L M P N Q : Type*} [Field k]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup P]
    [AddCommGroup N] [AddCommGroup Q]
    [Module k L] [Module k M] [Module k P] [Module k N] [Module k Q]
    (f : L →ₗ[k] P) (g : M →ₗ[k] N) (h : M →ₗ[k] Q)
    (hker : LinearMap.ker g = LinearMap.ker h) :
    LinearMap.ker (TensorProduct.map f g) =
      LinearMap.ker (TensorProduct.map f h) := by
  let Kf := LinearMap.ker f
  let K := LinearMap.ker g
  let qf : L →ₗ[k] L ⧸ Kf := Kf.mkQ
  let q : M →ₗ[k] M ⧸ K := K.mkQ
  let fbar : L ⧸ Kf →ₗ[k] P := Kf.liftQ f (fun x hx => hx)
  let gbar : M ⧸ K →ₗ[k] N := K.liftQ g (fun x hx => hx)
  let hbar : M ⧸ K →ₗ[k] Q := K.liftQ h (fun x hx => by
    change x ∈ LinearMap.ker h
    rw [← hker]
    exact hx)
  have hfbar : Function.Injective fbar := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' Kf f rfl)
  have hgbar : Function.Injective gbar := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' K g rfl)
  have hhbar : Function.Injective hbar := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' K h hker)
  have hfg : Function.Injective (TensorProduct.map fbar gbar) :=
    TensorProduct.map_injective_of_flat_flat _ _ hfbar hgbar
  have hfh : Function.Injective (TensorProduct.map fbar hbar) :=
    TensorProduct.map_injective_of_flat_flat _ _ hfbar hhbar
  have hfactorG (z : L ⊗[k] M) :
      TensorProduct.map f g z =
        TensorProduct.map fbar gbar (TensorProduct.map qf q z) := by
    rw [TensorProduct.map_map]
    rfl
  have hfactorH (z : L ⊗[k] M) :
      TensorProduct.map f h z =
        TensorProduct.map fbar hbar (TensorProduct.map qf q z) := by
    rw [TensorProduct.map_map]
    rfl
  ext z
  simp only [LinearMap.mem_ker]
  rw [hfactorG, hfactorH]
  constructor
  · intro hz
    have hzero : TensorProduct.map qf q z = 0 := by
      apply hfg
      simpa using hz
    rw [hzero, map_zero]
  · intro hz
    have hzero : TensorProduct.map qf q z = 0 := by
      apply hfh
      simpa using hz
    rw [hzero, map_zero]

end GaloisForLFunctions.HTGeometry
