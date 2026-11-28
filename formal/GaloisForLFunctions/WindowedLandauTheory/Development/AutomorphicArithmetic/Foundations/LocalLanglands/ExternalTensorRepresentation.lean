import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-! The direct product of the groups acts on the tensor product
by applying the corresponding representation in each factor. -/

noncomputable section

open scoped TensorProduct

namespace Representation

variable {ι : Type*} {G V : ι → Type*} [∀ i, Group (G i)]
  [∀ i, AddCommMonoid (V i)] [∀ i, Module ℂ (V i)]

def externalTensor (ρ : ∀ i, Representation ℂ (G i) (V i)) :
    Representation ℂ (∀ i, G i) (⨂[ℂ] i, V i) where
  toFun g := PiTensorProduct.map (fun i => ρ i (g i))
  map_one' := by
    have he : (fun i => ρ i ((1 : ∀ i, G i) i)) = fun i => (LinearMap.id : V i →ₗ[ℂ] V i) :=
      funext fun i => map_one (ρ i)
    rw [he, PiTensorProduct.map_id]
    rfl
  map_mul' g t := by
    have he : (fun i => ρ i ((g * t) i)) = fun i => (ρ i (g i)).comp (ρ i (t i)) :=
      funext fun i => map_mul (ρ i) (g i) (t i)
    rw [he, PiTensorProduct.map_comp]
    rfl

@[simp] theorem externalTensor_apply_tprod (ρ : ∀ i, Representation ℂ (G i) (V i))
    (g : ∀ i, G i) (u : ∀ i, V i) :
    externalTensor ρ g (PiTensorProduct.tprod ℂ u) = PiTensorProduct.tprod ℂ (fun i => ρ i (g i) (u i)) :=
  PiTensorProduct.map_tprod _ _

theorem externalTensor_apply_scalar [Fintype ι] (ρ : ∀ i, Representation ℂ (G i) (V i))
    (g : ∀ i, G i) (c : ι → ℂ) (h : ∀ i v, ρ i (g i) v = c i • v)
    (w : ⨂[ℂ] i, V i) : externalTensor ρ g w = (∏ i, c i) • w := by
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | smul_tprod a x =>
    rw [map_smul, externalTensor_apply_tprod, smul_comm]
    congr 1
    simp only [h]
    exact MultilinearMap.map_smul_univ (PiTensorProduct.tprod ℂ) c x

end Representation

#print axioms Representation.externalTensor
