import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteIdelicArtinRestriction

/-! Restriction of finite Artin maps in an algebra tower. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [IsAbelianGalois K E] [IsAbelianGalois K L]

local notation "G" => Gal(L/K)
local notation "H" => Gal(E/K)

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : CommGroup H :=
  { (inferInstance : Group H) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : Fintype G := Fintype.ofFinite _

local instance : Fintype H := Fintype.ofFinite _

theorem finiteIdelicArtin_restrict_eq
    (f : IdeleGroup K →* G) (g : IdeleGroup K →* H)
    (hf : IsFiniteIdelicArtin f) (hg : IsFiniteIdelicArtin g)
    (hfd : ∀ a : Kˣ, f (diagonal K a) = 1) (hgd : ∀ a : Kˣ, g (diagonal K a) = 1) :
    (AlgEquiv.restrictNormalHom E).comp f = g := by
  have hr : IsGaloisGroup.restrictHom G H K E L =
      (AlgEquiv.restrictNormalHom E : G →* H) := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E L).injective
    exact (IsGaloisGroup.algebraMap_restrictHom_smul G H K E L σ x).trans
      (σ.restrictNormal_commutes E x).symm
  obtain ⟨m, hu, hm⟩ := hf
  obtain ⟨n, hv, hn⟩ := hg
  rw [← hr]
  exact finite_idelic_artin_restrict K E L H G n m g f hgd hfd
    (fun v h => not_not.mp fun hram => h ((hv v).mpr hram))
    (fun v h => not_not.mp fun hram => h ((hu v).mpr hram)) hn hm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_restrict_eq
