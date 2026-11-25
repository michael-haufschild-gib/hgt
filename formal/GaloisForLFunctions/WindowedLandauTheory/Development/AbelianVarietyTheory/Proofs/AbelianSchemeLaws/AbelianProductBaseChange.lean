import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGroupPullbacks
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
  exact h.of_iso (asIso μ.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- Pairing two endomorphisms commutes with the cartesian comparison. -/
theorem lift_pφ₂ (a b : A ⟶ A) :
    (lift ((Over.pullback φ).map a) ((Over.pullback φ).map b)).left ≫ pφ₂ φ A =
      pφ φ A ≫ (lift a b).left := by
  rw [pφ₂, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.lift_μ]
  exact pullback_map_left_fst' φ (lift a b)

end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

namespace GlobalTheory.LineBundleSections

/-- A generator for pullback along a composite gives one for the iterated pullback. -/
theorem exists_gen_nested_pull {X Y Z : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (g : Z ⟶ Y)
    {t : (L.pull (g ≫ f)).Gen} (ht : t.IsGen) : ∃ s : ((L.pull f).pull g).Gen, s.IsGen := by
  let P := (ChartPull.pull (L.pull f) g).comp (ChartPull.pull L f)
  let Q := ChartPull.pull L (g ≫ f)
  let M := (L.pull f).pull g
  let j (i : M.ι) : (L.pull (g ≫ f)).ι := fun _ => P.idx i
  have hle (i : M.ι) : M.U i ≤ (L.pull (g ≫ f)).U (j i) :=
    (P.le i).trans (pull_chart L (g ≫ f) (P.idx i)).ge
  let C : ChartPull M (L.pull (g ≫ f)) (𝟙 Z) :=
    { idx := j
      le := hle
      g := fun i k => by
        rw [pullLE_id]
        exact (P.g i k).trans (Q.restrict_g (hle i) (hle k)).symm }
  exact C.exists_gen ht

end GlobalTheory.LineBundleSections
