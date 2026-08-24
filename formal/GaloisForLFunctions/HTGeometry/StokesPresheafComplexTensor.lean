import GaloisForLFunctions.HTGeometry.StokesPresheafDerivedTensor
import Mathlib.Algebra.Homology.Monoidal

/-!
# Chain-complex tensor for module presheaves

The pointwise tensor of module presheaves totalizes to a coherent tensor on nonnegative chain
complexes. This is chain-level infrastructure only: no K-flat replacement or derived-category
tensor is asserted.
-/

open CategoryTheory Limits
open MonoidalCategory

universe u

namespace GaloisForLFunctions.IrregularStokes.PresheafComplexTensor

variable {C : Type u} [SmallCategory C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

/-- Module presheaves over the underlying ring presheaf of `A`. -/
abbrev ModulePresheaf :=
  PresheafOfModules.{u} (A.comp (forget₂ CommRingCat RingCat))

/-- Nonnegative chain complexes of module presheaves. -/
abbrev ModulePresheafChainComplex := ChainComplex (ModulePresheaf A) ℕ

/-- Curried module-presheaf tensor is additive in its first variable. Additivity after
evaluation at `Z` is exactly additivity of right tensoring by `Z`. -/
noncomputable instance curriedTensorAdditive :
    (curriedTensor (ModulePresheaf A)).Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext Z
    letI := PresheafDerivedTensor.tensorRightAdditive A Z
    change (f + g) ▷ Z = f ▷ Z + g ▷ Z
    exact (MonoidalCategory.tensorRight Z).map_add (f := f) (g := g)

/-- Standard total-tensor monoidal structure on nonnegative chain complexes of module
presheaves. Degree `n` is the coproduct of `Kᵢ ⊗ Lⱼ` over `i + j = n`. -/
@[instance_reducible]
noncomputable def chainComplexMonoidalCategory :
    MonoidalCategory (ModulePresheafChainComplex A) :=
  HomologicalComplex.monoidalCategory _ _

/-- Total tensor bifunctor on nonnegative chain complexes of module presheaves. -/
noncomputable def chainTensorFunctor :
    ModulePresheafChainComplex A × ModulePresheafChainComplex A ⥤
      ModulePresheafChainComplex A := by
  letI chainMonoidal : MonoidalCategory (ModulePresheafChainComplex A) :=
    chainComplexMonoidalCategory A
  exact @MonoidalCategory.tensor _ _ chainMonoidal

/-- Tensor unit: the monoidal unit module presheaf concentrated in degree zero. -/
noncomputable def chainTensorUnit : ModulePresheafChainComplex A := by
  letI chainMonoidal : MonoidalCategory (ModulePresheafChainComplex A) :=
    chainComplexMonoidalCategory A
  exact 𝟙_ _

/-- Associator of total tensor on module-presheaf chain complexes. -/
noncomputable def chainTensorAssociator
    (K L M : ModulePresheafChainComplex A) :
    (chainTensorFunctor A).obj ((chainTensorFunctor A).obj (K, L), M) ≅
      (chainTensorFunctor A).obj (K, (chainTensorFunctor A).obj (L, M)) := by
  letI chainMonoidal : MonoidalCategory (ModulePresheafChainComplex A) :=
    chainComplexMonoidalCategory A
  exact α_ K L M

/-- Left unitor of total tensor on module-presheaf chain complexes. -/
noncomputable def chainTensorLeftUnitor (K : ModulePresheafChainComplex A) :
    (chainTensorFunctor A).obj (chainTensorUnit A, K) ≅ K := by
  letI chainMonoidal : MonoidalCategory (ModulePresheafChainComplex A) :=
    chainComplexMonoidalCategory A
  exact λ_ K

/-- Right unitor of total tensor on module-presheaf chain complexes. -/
noncomputable def chainTensorRightUnitor (K : ModulePresheafChainComplex A) :
    (chainTensorFunctor A).obj (K, chainTensorUnit A) ≅ K := by
  letI chainMonoidal : MonoidalCategory (ModulePresheafChainComplex A) :=
    chainComplexMonoidalCategory A
  exact ρ_ K

end GaloisForLFunctions.IrregularStokes.PresheafComplexTensor
