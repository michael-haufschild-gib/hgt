import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.OpenRestrictionCech

/-! Isomorphisms of schemes identify the affine Čech complexes on corresponding covers. -/

noncomputable section

open AlgebraicGeometry CategoryTheory HTGeometry
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

/-- Pullback along an isomorphism preserves the Čech complex of sections. -/
def cechPullbackIso_of_isIso {R : Type} [CommRing R] {X Y : Scheme.{0}}
    (f : X ⟶ Spec (.of R)) {L : LB X} (hL : L.IsLB) (π : Y ⟶ X) [IsIso π]
    {ι : Type} [LinearOrder ι] (U : ι → X.Opens)
    (ha : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ U I)) :
    cech f (toMod L) U ≅ cech (π ≫ f) (toMod (L.pull π)) (fun i => π ⁻¹ᵁ U i) := by
  have hπ : π.opensRange = ⊤ := Scheme.Hom.opensRange_of_isIso π
  have h : cech f (toMod L) U = cechOverOpen f (toMod L) π.opensRange U := by
    rw [hπ]
    rfl
  exact eqToIso h ≪≫ openCechPullbackIso f U π hL fun I hI => by
    rw [hπ]
    exact ha I hI

end GlobalTheory.LineBundleSections
