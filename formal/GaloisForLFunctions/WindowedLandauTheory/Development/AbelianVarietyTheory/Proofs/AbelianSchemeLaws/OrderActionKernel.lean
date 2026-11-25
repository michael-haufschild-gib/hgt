import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.OrderActionIsogeny
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FiniteEtaleGeometricCardinality

/-! The kernel of a nonzero coefficient action is counted by its finite étale rank. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT

open ReciprocityTheory.ChartRestriction.G.Semi

/-- Over a rational base the geometric kernel of a nonzero order element has cardinality
equal to the rank of the corresponding isogeny at the identity. -/
theorem OActN.card_geometric_kernel_eq_finrank {S : Scheme.{0}} {A : Over S} [GrpObj A]
    {R F k : Type} [CommRing R] [Algebra ℚ R] [Field F] [NumberField F]
    [Field k] [IsAlgClosed k] (s : S ⟶ Spec (CommRingCat.of R))
    (a : OActN (𝓞 F) A) (hA : IsAbelianScheme A) {c : 𝓞 F} (hc : c ≠ 0)
    (x : Spec (CommRingCat.of k) ⟶ S) (z : Spec (CommRingCat.of k)) :
    Finite {y : Over.mk x ⟶ A // y ≫ a.act c = 1} ∧
      Nat.card {y : Over.mk x ⟶ A // y ≫ a.act c = 1} =
        (a.act c).left.finrank ((1 : Over.mk x ⟶ A).left z) := by
  let f := a.act c
  let e : Over.mk x ⟶ A := 1
  obtain ⟨hfinite, hetale, _⟩ := a.finiteEtaleSurjective_of_ne_zero s hA hc
  let u : Spec (CommRingCat.of k) ⟶ A.left := e.left
  obtain ⟨hfin, hcard⟩ := @GlobalTheory.FinEt.card_points_eq_finrank A.left A.left
    f.left hfinite hetale k _ _ u z
  let E : {y : Over.mk x ⟶ A // y ≫ f = e} ≃
      {y : Spec (CommRingCat.of k) ⟶ A.left // y ≫ f.left = u} :=
    { toFun := fun y => ⟨y.1.left, congrArg (fun g : Over.mk x ⟶ A => g.left) y.2⟩
      invFun := fun y =>
        have hw : y.1 ≫ A.hom = x := by
          have he : u ≫ A.hom = x := Over.w e
          rw [← Over.w f, ← Category.assoc, y.2, he]
        ⟨Over.homMk y.1 hw, Over.OverMorphism.ext y.2⟩
      left_inv := fun y => Subtype.ext (Over.OverMorphism.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  letI := hfin
  exact ⟨Finite.of_equiv _ E.symm, (Nat.card_congr E).trans hcard⟩

end GlobalTheory.UPel.HT
