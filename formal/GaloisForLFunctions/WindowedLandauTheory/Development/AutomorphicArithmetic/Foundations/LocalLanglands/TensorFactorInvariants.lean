import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.ExternalTensorRepresentation
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Fixing an external tensor under a subgroup in one factor
forces a fixed vector in that factor. Split off the factor and
take a nonzero basis coefficient in the complementary tensor. -/

noncomputable section

open TensorProduct

namespace Representation

variable {ι : Type*} [DecidableEq ι] {G V : ι → Type*} [∀ i, Group (G i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem exists_fixed_of_externalTensor
    (ρ : ∀ i, Representation ℂ (G i) (V i)) (a : ι) (H : Subgroup (G a))
    {w : ⨂[ℂ] i, V i} (hw₀ : w ≠ 0)
    (hw : ∀ g : H, externalTensor ρ (Pi.mulSingle a g.val) w = w) :
    ∃ v : V a, v ≠ 0 ∧ ∀ g : H, ρ a g.val v = v := by
  let U := ⨂[ℂ] (j : ({a}ᶜ : Set ι)), V j
  let e := PiTensorProduct.equivPiTensorComplSingletonTensor ℂ V a
  let z : U ⊗[ℂ] V a := e w
  have hz : z ≠ 0 := fun h => hw₀ (e.injective (h.trans (map_zero e).symm))
  let b := Module.Free.chooseBasis ℂ U
  let c := Module.Free.chooseBasis ℂ (V a)
  let B := b.tensorProduct c
  obtain ⟨⟨i, j⟩, hij⟩ : ∃ p, B.repr z p ≠ 0 := by
    by_contra! h
    exact hz (B.repr.injective (by ext p; simp [h p]))
  let f : U ⊗[ℂ] V a →ₗ[ℂ] V a :=
    (_root_.TensorProduct.lid ℂ (V a)).toLinearMap.comp (TensorProduct.map (b.coord i) LinearMap.id)
  have hf (x : U) (y : V a) : f (x ⊗ₜ[ℂ] y) = b.coord i x • y := by
    simp only [f, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearEquiv.coe_coe, _root_.TensorProduct.lid_tmul]
  have hcoef : (c.coord j).comp f = B.coord (i, j) := by
    apply TensorProduct.ext'
    intro x y
    rw [LinearMap.comp_apply, hf, map_smul]
    simp only [B, Module.Basis.coord_apply, Module.Basis.tensorProduct_repr_tmul_apply,
      smul_eq_mul, mul_comm]
  refine ⟨f z, fun h => hij ?_, fun g => ?_⟩
  · have hzero := LinearMap.congr_fun hcoef z
    simpa only [LinearMap.comp_apply, h, map_zero, Module.Basis.coord_apply] using hzero.symm
  · let S : U ⊗[ℂ] V a →ₗ[ℂ] U ⊗[ℂ] V a := TensorProduct.map LinearMap.id (ρ a g.val)
    have hE : e.toLinearMap.comp (externalTensor ρ (Pi.mulSingle a g.val)) =
        S.comp e.toLinearMap := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      change e (externalTensor ρ (Pi.mulSingle a g.val) (PiTensorProduct.tprod ℂ x)) =
        S (e (PiTensorProduct.tprod ℂ x))
      have he : (fun j : ({a}ᶜ : Set ι) => ρ j.val ((Pi.mulSingle a g.val) j.val) (x j.val)) =
          fun j : ({a}ᶜ : Set ι) => x j.val := by
        funext j
        rw [Pi.mulSingle_eq_of_ne (show j.val ≠ a from j.prop), map_one, Module.End.one_apply]
      simp only [e, S, externalTensor_apply_tprod, PiTensorProduct.equivPiTensorComplSingletonTensor_tprod,
        TensorProduct.map_tmul, LinearMap.id_apply, Pi.mulSingle_eq_same]
      exact congrArg (fun y : ∀ j : ({a}ᶜ : Set ι), V j =>
        PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] ρ a g.val (x a)) he
    have hS : S z = z := by
      have he := LinearMap.congr_fun hE w
      change e (externalTensor ρ (Pi.mulSingle a g.val) w) = S z at he
      rw [hw g] at he
      exact he.symm
    have he : f.comp S = (ρ a g.val).comp f := by
      apply TensorProduct.ext'
      intro x y
      simp only [S, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, hf, map_smul]
    exact (LinearMap.congr_fun he z).symm.trans (congrArg f hS)

end Representation

#print axioms Representation.exists_fixed_of_externalTensor
