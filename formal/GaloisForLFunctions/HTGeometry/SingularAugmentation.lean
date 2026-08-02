import GaloisForLFunctions.HTGeometry.SingularChainFreeModel

/-!
# The augmentation of the singular chain complex

The augmentation of a chain space presented as a coproduct of copies of the coefficient object sends
every summand to the coefficient object by the identity.  It is therefore natural in the index set:
a map of index sets commutes with it, so a group acting on the simplices fixes the augmentation even
when no equivariant contraction is available.  Composed with the differential it vanishes, because
the differential in the bottom degree is the difference of the two face maps and the augmentation
does not see which face was taken.

This is the augmented chain cosheaf: the complex together with its augmentation, and the
equivariance that lets compact descent be applied to it.

* `sigmaAugmentation` : **the augmentation of a coproduct of copies of the coefficient object.**
* `sigmaAugmentation_naturality`, `sigmaAugmentation_equivariant` : **it is natural in the index
  set, hence equivariant.**
* `sSetAugmentation_comp_d` : **the augmentation kills boundaries.**
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Simplicial Opposite

noncomputable section

namespace GaloisForLFunctions

section Augmentation

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{0} C] (R : C)

/-- **The augmentation**: the map out of a coproduct of copies of the coefficient object which is
the identity on every summand. -/
def sigmaAugmentation (α : Type) : (∐ fun _ : α => R) ⟶ R :=
  Sigma.desc fun _ => 𝟙 R

omit [Preadditive C] in
@[simp]
theorem ι_sigmaAugmentation {α : Type} (a : α) :
    Sigma.ι (fun _ : α => R) a ≫ sigmaAugmentation R α = 𝟙 R :=
  Sigma.ι_desc _ a

omit [Preadditive C] in
/-- **The augmentation is natural in the index set.** -/
theorem sigmaAugmentation_naturality {α β : Type} (f : α → β) :
    (Sigma.map' f fun _ => 𝟙 R) ≫ sigmaAugmentation R β = sigmaAugmentation R α := by
  refine Sigma.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, Sigma.ι_comp_map', Category.assoc, ι_sigmaAugmentation,
    ι_sigmaAugmentation, Category.comp_id]

omit [Preadditive C] in
/-- **The augmentation is equivariant**: a group acting on the index set by maps of sets acts on the
coproduct fixing the augmentation, whether or not the action admits an equivariant contraction. -/
theorem sigmaAugmentation_equivariant {α : Type} (g : α → α) :
    (Sigma.map' g fun _ => 𝟙 R) ≫ sigmaAugmentation R α = sigmaAugmentation R α :=
  sigmaAugmentation_naturality R g

end Augmentation

section SSetAugmentation

variable (𝕜 : Type) [NormedField 𝕜]

/-- The augmentation of the simplicial chain complex with coefficients in the base field. -/
abbrev sSetAugmentation (S : SSet.{0}) :
    sSetFreeChainSpace 𝕜 S 0 ⟶ ModuleCat.of 𝕜 𝕜 :=
  sigmaAugmentation (ModuleCat.of 𝕜 𝕜) (S.obj (op ⦋0⦌))

/-- **The augmentation kills boundaries**, so the augmented chain complex is a complex: the
differential in the bottom degree is the difference of the two face maps, and the augmentation does
not distinguish them. -/
theorem sSetAugmentation_comp_d (S : SSet.{0}) :
    sSetFreeChainD 𝕜 S 0 ≫ sSetAugmentation 𝕜 S = 0 := by
  rw [sSetChain_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, sigmaAugmentation_naturality]
  rw [Fin.sum_univ_two]
  simp

end SSetAugmentation

end GaloisForLFunctions

end
