import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveRatios
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsPullback

/-! Dividing by a homogeneous form is linear, and ratios compose on chart overlaps. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ}

theorem homogeneousRatio_mul {u v w : A} (hu : u ∈ 𝒜 d) (hv : v ∈ 𝒜 d) (hw : w ∈ 𝒜 d) :
    let W := Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v
    (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : W ≤ Proj.basicOpen 𝒜 u)).op
        (homogeneousRatio hu hv) *
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_right : W ≤ Proj.basicOpen 𝒜 v)).op
        (homogeneousRatio hv hw) =
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : W ≤ Proj.basicOpen 𝒜 u)).op
        (homogeneousRatio hu hw) := by
  dsimp only
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change ((homogeneousRatio hu hv).1 ⟨x.1, x.2.1⟩ *
    (homogeneousRatio hv hw).1 ⟨x.1, x.2.2⟩).val =
    ((homogeneousRatio hu hw).1 ⟨x.1, x.2.1⟩).val
  rw [HomogeneousLocalization.val_mul]
  erw [homogeneousRatio_val, homogeneousRatio_val, homogeneousRatio_val]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]; ring⟩

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [CommRing K] {N : ℕ} {X : Scheme.{u}}
  {s : X ⟶ Spec (CommRingCat.of K)}

private abbrev Grade := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

/-- Dividing on the inverse image of a projective chart is linear in the numerator. -/
def projectiveRatioLinear (i : X ⟶ PSpace K N) (hi : i ≫ PSpace.str K N = s)
    {u : MvPolynomial (Fin (N + 1)) K} (hu : u ∈ Grade (K := K) (N := N) d) (hd : 0 < d) :
    Grade (K := K) (N := N) d →ₗ[K]
      SectionRing s (i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) u) :=
  (sectionPullback hi _).toLinearMap.comp (pspaceRatioLinear hu hd)

theorem projectiveRatioLinear_apply (i : X ⟶ PSpace K N) (hi : i ≫ PSpace.str K N = s)
    {u : MvPolynomial (Fin (N + 1)) K} (hu : u ∈ Grade (K := K) (N := N) d) (hd : 0 < d)
    (v : Grade (K := K) (N := N) d) :
    projectiveRatioLinear i hi hu hd v = projectiveRatio i hu v.2 :=
  rfl

theorem projectiveRatio_self (i : X ⟶ PSpace K N)
    {u : MvPolynomial (Fin (N + 1)) K} (hu : u ∈ Grade (K := K) (N := N) d) :
    projectiveRatio i hu hu = 1 := by
  unfold projectiveRatio
  rw [homogeneousRatio_self, map_one]

theorem projectiveRatio_mul (i : X ⟶ PSpace K N)
    {u v w : MvPolynomial (Fin (N + 1)) K}
    (hu : u ∈ Grade (K := K) (N := N) d)
    (hv : v ∈ Grade (K := K) (N := N) d)
    (hw : w ∈ Grade (K := K) (N := N) d) :
    let U := i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) u
    let V := i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) v
    X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (projectiveRatio i hu hv) *
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (projectiveRatio i hv hw) =
      X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (projectiveRatio i hu hw) := by
  let U := Proj.basicOpen (Grade (K := K) (N := N)) u
  let V := Proj.basicOpen (Grade (K := K) (N := N)) v
  let l : U ⊓ V ⟶ U := homOfLE inf_le_left
  let r : U ⊓ V ⟶ V := homOfLE inf_le_right
  have hn {T : (PSpace K N).Opens} (m : U ⊓ V ⟶ T) (a : Γ(PSpace K N, T)) :
      X.presheaf.map ((Opens.map i.base).map m).op ((i.app T).hom a) =
        (i.app (U ⊓ V)).hom ((PSpace K N).presheaf.map m.op a) :=
    (ConcreteCategory.congr_hom (i.naturality m.op) a).symm
  change X.presheaf.map ((Opens.map i.base).map l).op ((i.app U).hom (homogeneousRatio hu hv)) *
    X.presheaf.map ((Opens.map i.base).map r).op ((i.app V).hom (homogeneousRatio hv hw)) =
    X.presheaf.map ((Opens.map i.base).map l).op ((i.app U).hom (homogeneousRatio hu hw))
  simp only [hn, ← map_mul]
  exact congrArg (i.app (U ⊓ V)).hom (homogeneousRatio_mul hu hv hw)

end GlobalTheory.SchemeCohomology
