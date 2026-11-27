import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.LocalNormalizedTwistBasis
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalProductSectionBaseChange

/-! The normalized twist has a basis compatible with pullback of each chart coordinate. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LineBundleSections
open scoped CategoryTheory.Obj

namespace GlobalTheory.PrincipalSections

attribute [local instance] Over.cartesianMonoidalCategory

/-- The chart sections of the normalized twist give a basis after any affine
base change, by pulling back the coordinates in the four-factor presentation. -/
theorem exists_normalized_twist_chart_basis {R : Type} [CommRing R] [IsLocalRing R]
    {A : Over (Spec (.of R))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : Spec (.of R), ∃ U : (Spec (.of R)).Opens, s ∈ U ∧
      ∃ t : (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    (x : 𝟙_ (Over (Spec (.of R))) ⟶ A) (j : ℕ) (hj : 1 ≤ j) :
    let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
    let a : Fin 4 → (A.left ⟶ A.left) := ![𝟙 A.left, τ.left, A.hom ≫ x.left, A.hom ≫ η[A].left]
    let e : Fin 4 → ℤ := ![(j : ℤ) - 1, 1, -1, 1]
    ∃ b : Fin (j ^ d) → (LB.LinComb L a e).Sec,
      ∀ (S : Type) [CommRing S] (α : R →+* S) {Y : Scheme.{0}} {π : Y ⟶ A.left}
        {g : Y ⟶ Spec (.of S)}, IsPullback π g A.hom (Spec.map (CommRingCat.ofHom α)) →
        let H := LB.LinComb L (fun i => π ≫ a i) e
        letI := sectionBaseModule g (toMod H) ⊤
        ∃ F : (Fin (j ^ d) → S) ≃ₗ[S] Γ(toMod H, ⊤),
          ∀ k i, (globalCoordinates (F (Pi.single k 1))).f i = (pullSec (b k) π).f i := by
  let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
  let a : Fin 4 → (A.left ⟶ A.left) := ![𝟙 A.left, τ.left, A.hom ≫ x.left, A.hom ≫ η[A].left]
  let e : Fin 4 → ℤ := ![(j : ℤ) - 1, 1, -1, 1]
  obtain ⟨b, hb⟩ := exists_normalized_local_twist_basis hA hL hAmp hK hrig hsym d x j hj
  refine ⟨fun k => globalCoordinates (b k), fun S _ α Y π g W => ?_⟩
  obtain ⟨F, hF⟩ := hb S α W
  let G := formalProductPullEquiv L a e π g
  refine ⟨F.trans G, fun k i => ?_⟩
  change (globalCoordinates (G (F (Pi.single k 1)))).f i = _
  rw [hF]
  exact formalProductPullEquiv_coord L a e π g (b k) i

end GlobalTheory.PrincipalSections
