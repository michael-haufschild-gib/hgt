import GaloisForLFunctions.HTGeometry.CoproductMayerVietorisFamily

/-!
# Hasse decompositions from split Mayer--Vietoris sequences

The existing split Mayer--Vietoris sequences canonically decompose paired local data into overlap
correction plus global data.  This is recorded for a two-piece cover, two arbitrary subsets over
their union, and a base with an arbitrary family of pieces.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [HasCoproducts.{w} C]

variable {T : Type w} (R : C)

/-- Paired local coproduct data over a two-piece cover decompose into overlap correction and global
data. -/
noncomputable def mvHasseIso (S₁ S₂ : Set T) (hcover : S₁ ∪ S₂ = Set.univ) :
    subCoproduct R S₁ ⊞ subCoproduct R S₂ ≅
      subCoproduct R (S₁ ∩ S₂) ⊞ (∐ fun _ : T => R) :=
  (mvSplitting R S₁ S₂ hcover).isoBinaryBiproduct

omit [HasZeroObject C] in
@[simp] theorem mvHasseIso_hom (S₁ S₂ : Set T) (hcover : S₁ ∪ S₂ = Set.univ) :
    (mvHasseIso R S₁ S₂ hcover).hom =
      biprod.lift (mvRetraction R S₁ S₂) (mvSnd R S₁ S₂) := rfl

omit [HasZeroObject C] in
@[simp] theorem mvHasseIso_inv (S₁ S₂ : Set T) (hcover : S₁ ∪ S₂ = Set.univ) :
    (mvHasseIso R S₁ S₂ hcover).inv =
      biprod.desc (mvFst R S₁ S₂) (mvSection R S₁ S₂) := rfl

/-- Without a covering hypothesis, paired local data decompose over their actual union. -/
noncomputable def mvSupHasseIso (S₁ S₂ : Set T) :
    subCoproduct R S₁ ⊞ subCoproduct R S₂ ≅
      subCoproduct R (S₁ ∩ S₂) ⊞ subCoproduct R (S₁ ∪ S₂) :=
  (mvSupSplitting R S₁ S₂).isoBinaryBiproduct

omit [HasZeroObject C] in
@[simp] theorem mvSupHasseIso_hom (S₁ S₂ : Set T) :
    (mvSupHasseIso R S₁ S₂).hom =
      biprod.lift (mvRetraction R S₁ S₂) (mvSupSnd R S₁ S₂) := rfl

omit [HasZeroObject C] in
@[simp] theorem mvSupHasseIso_inv (S₁ S₂ : Set T) :
    (mvSupHasseIso R S₁ S₂).inv =
      biprod.desc (mvFst R S₁ S₂) (mvSupSection R S₁ S₂) := rfl

variable {ι : Type w} (S₀ : Set T) (S : ι → Set T)

/-- Local data on a base and arbitrary family decompose into all overlap corrections plus global
data, provided different pieces meet only inside the base. -/
noncomputable def mvFamilyHasseIso
    (W : Set T) (idx : T → ι)
    (hidx : ∀ x : (W : Set T), (x : T) ∉ S₀ → (x : T) ∈ S (idx x))
    (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W)
    (hdisj : ∀ a b : ι, a ≠ b → S a ∩ S b ⊆ S₀) :
    subCoproduct R S₀ ⊞ famCoproduct R S ≅
      famInterCoproduct R S₀ S ⊞ subCoproduct R W :=
  (famSplitting R S₀ S W idx hidx hbase hpiece hdisj).isoBinaryBiproduct

omit [HasZeroObject C] in
@[simp] theorem mvFamilyHasseIso_hom
    (W : Set T) (idx : T → ι)
    (hidx : ∀ x : (W : Set T), (x : T) ∉ S₀ → (x : T) ∈ S (idx x))
    (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W)
    (hdisj : ∀ a b : ι, a ≠ b → S a ∩ S b ⊆ S₀) :
    (mvFamilyHasseIso R S₀ S W idx hidx hbase hpiece hdisj).hom =
      biprod.lift (famRetraction R S₀ S) (famSnd R S₀ S W hbase hpiece) := rfl

omit [HasZeroObject C] in
@[simp] theorem mvFamilyHasseIso_inv
    (W : Set T) (idx : T → ι)
    (hidx : ∀ x : (W : Set T), (x : T) ∉ S₀ → (x : T) ∈ S (idx x))
    (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W)
    (hdisj : ∀ a b : ι, a ≠ b → S a ∩ S b ⊆ S₀) :
    (mvFamilyHasseIso R S₀ S W idx hidx hbase hpiece hdisj).inv =
      biprod.desc (famFst R S₀ S) (famSection R S₀ S W idx hidx) := rfl

end GaloisForLFunctions.HTGeometry
