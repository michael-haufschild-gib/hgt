import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AbelianMultiplicationFinite
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FiniteAbelianEndOverField
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FiniteMorphismGeometricFlatness
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGroupPullbacks

/-! Positive multiplication on a polarized abelian scheme over a locally Noetherian
base is finite, flat and surjective. Invertibility of the multiplier gives étaleness. -/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.MulFinite

open GrpTangent

attribute [local instance] Over.cartesianMonoidalCategory

/-- Positive multiplication is a finite flat surjection, and is étale when the
multiplier is a unit on the base. -/
theorem finite_flat_surjective_mulN_of_rigidified_symmetric {S : Scheme.{0}}
    [IsLocallyNoetherian S] {A : Over S} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (LB.LinComb L (K := Fin 2)
      ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (n : ℕ) (hn : n ≠ 0) :
    let f := mulN A n
    IsFinite f.left ∧ Flat f.left ∧ Surjective f.left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale f.left) := by
  letI := hA.comm
  letI := hA.smooth
  let f := mulN A n
  haveI : IsMonHom f := isMonHom_mulN A n
  have hf : IsFinite f.left := isFinite_mul_of_rigidified_symmetric hA hL hAmp hrig hsym n hn
  have hgeo (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) :
      Flat ((Over.pullback t).map f).left ∧ Surjective ((Over.pullback t).map f).left := by
    letI : IsFinite ((Over.pullback t).map f).left :=
      MorphismProperty.of_isPullback (isPullback_baseChange t f) hf
    exact FiniteEndFlat.flat_surjective_of_finite_abelian_end (hA.pullback t) ((Over.pullback t).map f)
  exact ⟨hf, FiniteFibreFlat.flat_of_isFinite_of_flat_geometric_fibres A A f inferInstance hf
    (fun K _ _ t => (hgeo K t).1), surjective_of_geomFibres f (fun K _ _ t => (hgeo K t).2),
    etale_mulN A⟩

end GlobalTheory.MulFinite
