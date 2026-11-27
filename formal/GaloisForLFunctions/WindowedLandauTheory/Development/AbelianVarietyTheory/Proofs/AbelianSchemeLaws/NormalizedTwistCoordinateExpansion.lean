import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.NormalizedTwistChartBasis
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalBasisChartCoordinates

/-! Base-changed sections of a normalized twist have unique coefficients
simultaneously in all bundle charts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology
open scoped CategoryTheory.Obj

namespace GlobalTheory.PrincipalSections

attribute [local instance] Over.cartesianMonoidalCategory

/-- A single family of chart sections spans the normalized twist after every
scalar extension, with unique coefficients over the new base ring. -/
theorem exists_normalized_twist_unique_expansion {R : Type} [CommRing R] [IsLocalRing R]
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
        let N := LB.LinComb L (fun i => π ≫ a i) e
        ∀ s : N.Sec, ∃! r : Fin (j ^ d) → S, ∀ i : N.ι,
          letI := sectionAlgebra g (N.U i)
          s.f i = ∑ k, algebraMap S Γ(Y, N.U i) (r k) * (pullSec (b k) π).f i := by
  obtain ⟨b, hb⟩ := exists_normalized_twist_chart_basis hA hL hAmp hK hrig hsym d x j hj
  refine ⟨b, fun S _ α Y π g H s => ?_⟩
  obtain ⟨E, hE⟩ := hb S α H
  exact (existsUnique_congr fun r => by simp only [hE]).mp (existsUnique_chart_coefficients g E s)

end GlobalTheory.PrincipalSections
