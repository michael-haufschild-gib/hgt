import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELObjectMaps
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleTrivialization

/-! Restriction of a trivialized polarization slice along a map of test schemes. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KerBy

/-- The triviality of a slice of the polarization persists after restriction. -/
theorem gen_comp {S : Scheme.{0}} {A : Over S} {P : LB (A ⊗ A).left} (hP : P.IsLB)
    {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ A)
    (H : ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) :
    ∃ t : (P.pull (lift (snd A T' ≫ a ≫ x) (fst A T')).left).Gen, t.IsGen := by
  let i : A ⊗ T' ⟶ A ⊗ T := lift (fst A T') (snd A T' ≫ a)
  let f : A ⊗ T ⟶ A ⊗ A := lift (snd A T ≫ x) (fst A T)
  let g : A ⊗ T' ⟶ A ⊗ A := lift (snd A T' ≫ a ≫ x) (fst A T')
  have e : i ≫ f = g := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [i, f, g, Category.assoc, lift_fst, lift_snd_assoc]
    · simp only [i, f, g, Category.assoc, lift_snd, lift_fst]
  have e' : i.left ≫ f.left = g.left := congrArg Over.Hom.left e
  obtain ⟨t, ht⟩ := H
  obtain ⟨u, hu⟩ := (ChartPull.pull (P.pull f.left) i.left).exists_gen ht
  obtain ⟨w, hw⟩ := LBIso.pull_comp hP i.left f.left
  exact e' ▸ hu.exists_gen_of_iso hw ((hP.pull f.left).pull i.left) (hP.pull (i.left ≫ f.left))

end GlobalTheory.KerBy
