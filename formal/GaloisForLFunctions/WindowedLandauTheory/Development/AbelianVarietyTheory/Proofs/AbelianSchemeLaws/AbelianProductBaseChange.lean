import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGroupPullbacks
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleTrivialization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback

/-! The fibre square and its group axes commute with base change. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S)

/-- The comparison from the base-changed fibre square is cartesian over the base. -/
theorem pφ₂_isPullback :
    IsPullback (pφ₂ φ A) (((Over.pullback φ).obj A) ⊗ ((Over.pullback φ).obj A)).hom
      (A ⊗ A).hom φ := by
  let μ := Functor.LaxMonoidal.μ (Over.pullback φ) A A
  haveI : IsIso μ.left := (Over.forget S').map_isIso μ
  have h := IsPullback.of_hasPullback (A ⊗ A).hom φ
  change IsPullback (μ.left ≫ pullback.fst (A ⊗ A).hom φ) _ _ _
  rw [← Over.w μ]
  let e := asIso μ.left
  refine h.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change pullback.fst (A ⊗ A).hom φ ≫ 𝟙 _ =
      e.inv ≫ e.hom ≫ pullback.fst (A ⊗ A).hom φ
    rw [e.inv_hom_id_assoc, Category.comp_id]
  · change pullback.snd (A ⊗ A).hom φ ≫ 𝟙 _ =
      e.inv ≫ e.hom ≫ pullback.snd (A ⊗ A).hom φ
    rw [e.inv_hom_id_assoc, Category.comp_id]

/-- Pairing two endomorphisms commutes with the cartesian comparison. -/
theorem lift_pφ₂ (a b : A ⟶ A) :
    (lift ((Over.pullback φ).map a) ((Over.pullback φ).map b)).left ≫ pφ₂ φ A =
      pφ φ A ≫ (lift a b).left := by
  rw [pφ₂, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.lift_μ]
  exact pullback_map_left_fst' φ (lift a b)

end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

namespace GlobalTheory.LineBundleSections

/-- A generator for pullback along a composite gives one for the iterated pullback. -/
theorem exists_gen_nested_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (f : Y ⟶ X) (g : Z ⟶ Y)
    {t : (L.pull (g ≫ f)).Gen} (ht : t.IsGen) : ∃ s : ((L.pull f).pull g).Gen, s.IsGen := by
  let P := (ChartPull.pull (L.pull f) g).comp (ChartPull.pull L f)
  let Q := ChartPull.pull L (g ≫ f)
  obtain ⟨i, hi⟩ := ChartPull.iso_of_common Q P hL
  exact ht.exists_gen_of_iso hi (hL.pull (g ≫ f)) ((hL.pull f).pull g)

end GlobalTheory.LineBundleSections
