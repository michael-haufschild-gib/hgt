import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.ExternalTensorRepresentation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothRepresentationScalarTwist
import Mathlib.Algebra.Group.Pi.Lemmas

/-! Factor equivalences give an equivalence of external tensor
representations. The scalar characters twist through the tensor
as their product on the acting product group. -/

noncomputable section

open scoped TensorProduct

namespace Representation

variable {ι : Type*} {G V W : ι → Type*} [∀ i, Group (G i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {ρ : ∀ i, Representation ℂ (G i) (V i)} {σ : ∀ i, Representation ℂ (G i) (W i)}

def Equiv.externalTensor (e : ∀ i, (ρ i).Equiv (σ i)) :
    (Representation.externalTensor ρ).Equiv (Representation.externalTensor σ) := by
  let E := PiTensorProduct.congr fun i => (e i).toLinearEquiv
  refine Equiv.mk E fun g => ?_
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change E (Representation.externalTensor ρ g (PiTensorProduct.tprod ℂ x)) =
    Representation.externalTensor σ g (E (PiTensorProduct.tprod ℂ x))
  simp only [E, externalTensor_apply_tprod, PiTensorProduct.congr_tprod]
  apply congrArg (PiTensorProduct.tprod ℂ)
  funext i
  exact IntertwiningMap.isIntertwining (ρ i) (σ i) (e i).toIntertwiningMap (g i) (x i)

theorem externalTensor_scalarTwist [Fintype ι] (χ : ∀ i, G i →* ℂˣ) :
    externalTensor (fun i => (ρ i).scalarTwist (χ i)) =
      (externalTensor ρ).scalarTwist (∏ i, (χ i).comp (Pi.evalMonoidHom G i)) := by
  apply MonoidHom.ext
  intro g
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change externalTensor (fun i => (ρ i).scalarTwist (χ i)) g (PiTensorProduct.tprod ℂ x) =
    (externalTensor ρ).scalarTwist (∏ i, (χ i).comp (Pi.evalMonoidHom G i)) g (PiTensorProduct.tprod ℂ x)
  simp only [externalTensor_apply_tprod, scalarTwist_apply, MonoidHom.finsetProd_apply,
    MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Units.coe_prod]
  exact MultilinearMap.map_smul_univ (PiTensorProduct.tprod ℂ) (fun i => (χ i (g i) : ℂ))
    (fun i => ρ i (g i) (x i))

end Representation

#print axioms Representation.Equiv.externalTensor
#print axioms Representation.externalTensor_scalarTwist
