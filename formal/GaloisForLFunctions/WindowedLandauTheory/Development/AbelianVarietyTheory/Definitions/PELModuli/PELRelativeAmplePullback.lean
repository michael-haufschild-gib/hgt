import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELRelativeAmpleLocal
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELPolarizationPullback

/-! Relative ampleness is preserved by base change and line-bundle isomorphism. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PolPull

/-- Pull back on affine neighbourhoods of the base image and glue the ample powers. -/
theorem relAmple_baseChange {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
    {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    (e : LBIso L' (L.pull φ)) (hqc : QuasiCompact A'.hom) (hqs : QuasiSeparated A'.hom)
    (ample : RelAmple A L) : RelAmple A' L' := by
  refine AmpleLocal.relAmple_of_locally S' A' L' hL' hqc hqs fun s => ?_
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f s) trivial
  let V := f ⁻¹ᵁ U
  let j := (A'.hom ⁻¹ᵁ V).ι
  have H : IsPullback (j ≫ φ) (A'.hom ∣_ V) A.hom (V.ι ≫ f) :=
    (isPullback_morphismRestrict A'.hom V).flip.paste_horiz h
  have he : LBIso (L'.pull j) (L.pull (j ≫ φ)) :=
    LBIso.trans (hL'.pull j) ((hL.pull φ).pull j) (hL.pull (j ≫ φ))
      (e.pull j) (LBIso.pull_comp hL j φ)
  obtain ⟨w, hw⟩ := he
  exact ⟨V, hs, relAmple_pull (A' := Over.mk (A'.hom ∣_ V)) H hL (hL'.pull j)
    hw U hU (fun y => y.2) ample⟩

end GlobalTheory.PolPull
