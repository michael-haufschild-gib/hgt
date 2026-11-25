import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleComposition
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleChartPullback

/-! A nowhere-vanishing section is an isomorphism from the trivial line bundle. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.Semi.LB

universe u

variable {X : Scheme.{u}} {L M : LB X}

def trivial (X : Scheme.{u}) : LB X where
  ι := PUnit
  U _ := ⊤
  g _ _ := 1

theorem isLB_trivial (X : Scheme.{u}) : (trivial X).IsLB where
  cover := by simp [trivial]
  g_self _ := map_one _
  cocycle _ _ _ := by
    let h : (⊤ : X.Opens) ⊓ ⊤ ⊓ ⊤ ≤ ⊤ ⊓ ⊤ := inf_le_left
    change res h 1 * res h 1 = res h 1
    have e := map_one (res h)
    exact (congrArg₂ (· * ·) e e).trans ((_root_.mul_one _).trans e.symm)

private def chart_to_trivial (L : LB X) : ChartPull (L.div (trivial X)) L (𝟙 X) where
  idx i := i.1
  le _ := inf_le_left
  g _ _ := by
    simp only [div, trivial, map_one, inv_one, mul_one]
    exact (pullLE_id _ _).symm

private def chart_from_trivial (L : LB X) : ChartPull L (L.div (trivial X)) (𝟙 X) where
  idx i := (i, PUnit.unit)
  le _ := le_inf le_rfl le_top
  g i j := by
    let U := L.U i ⊓ L.U j
    let V := (L.U i ⊓ ⊤) ⊓ (L.U j ⊓ ⊤)
    let h : U ≤ V := le_inf (le_inf inf_le_left le_top) (le_inf inf_le_right le_top)
    let e : V ≤ U := le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    simp only [div, trivial, map_one, inv_one, mul_one]
    change L.g i j = pullLE (𝟙 X) h (res e (L.g i j))
    exact ((res_res e h _).trans (res_refl _)).symm.trans (pullLE_id _ _).symm

/-- A generator is equivalent to a trivialization. -/
theorem exists_gen_iff_exists_iso_trivial :
    (∃ t : L.Gen, t.IsGen) ↔ ∃ t : Iso (trivial X) L, t.IsGen := by
  constructor
  · rintro ⟨t, ht⟩
    exact (chart_to_trivial L).exists_gen ht
  · rintro ⟨t, ht⟩
    exact (chart_from_trivial L).exists_gen ht

/-- A line-bundle isomorphism carries a global generator to a global generator. -/
theorem Gen.IsGen.exists_gen_of_iso {s : L.Gen} (hs : s.IsGen)
    {t : Iso L M} (ht : t.IsGen) (hL : L.IsLB) (hM : M.IsLB) : ∃ r : M.Gen, r.IsGen := by
  obtain ⟨q, hq⟩ := exists_gen_iff_exists_iso_trivial.mp ⟨s, hs⟩
  exact exists_gen_iff_exists_iso_trivial.mpr (hq.comp ht (isLB_trivial X) hL hM)

/-- A generator pulls across a commutative square of the base maps. -/
theorem exists_gen_of_pullbackSquare {Y Z W : Scheme.{u}} (hL : L.IsLB)
    {f : Y ⟶ X} {g : Z ⟶ X} {a : W ⟶ Y} {b : W ⟶ Z} (h : a ≫ f = b ≫ g)
    {s : (L.pull f).Gen} (hs : s.IsGen) : ∃ t : ((L.pull g).pull b).Gen, t.IsGen := by
  obtain ⟨s', hs'⟩ := (ChartPull.pull (L.pull f) a).exists_gen hs
  let P : ChartPull ((L.pull f).pull a) L (a ≫ f) :=
    (ChartPull.pull (L.pull f) a).comp (ChartPull.pull L f)
  let Q : ChartPull ((L.pull g).pull b) L (a ≫ f) :=
    h.symm ▸ (ChartPull.pull (L.pull g) b).comp (ChartPull.pull L g)
  obtain ⟨t, ht⟩ := P.iso_of_common Q hL
  exact hs'.exists_gen_of_iso ht ((hL.pull f).pull a) ((hL.pull g).pull b)

end ReciprocityTheory.ChartRestriction.G.Semi.LB
