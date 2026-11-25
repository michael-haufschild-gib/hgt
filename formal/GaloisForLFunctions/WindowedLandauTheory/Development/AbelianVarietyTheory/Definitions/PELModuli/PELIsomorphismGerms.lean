import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.StructureSheafUnitGerms
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.StructureSheafUnits

/-! Germ formulas for transition units and for a change of line-bundle trivialization. -/

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem gm_div {Z : Scheme.{0}} (A B : LB Y) (r : Z ⟶ Y) (z : Z) (p q : B.ι × A.ι)
    (hm : r z ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) :
    gm r z (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) ((LB.div B A).g p q) =
      gm r z _ (B.g p.1 q.1) * (gm r z _ (A.g p.2 q.2))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hm _))))

theorem gm_linComb {Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (j j' : K → L.ι) (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j') =
      ∏ k, gm (r ≫ φ k) z (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ (show r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' from ⟨hj, hj'⟩) _).trans
    (gm_pull r (φ k) z (L.U (j k) ⊓ L.U (j' k)) ⟨Set.mem_iInter.1 hj k, Set.mem_iInter.1 hj' k⟩ _)

theorem gm_pull_g {Z : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (r : Z ⟶ X') (z : Z) (J J' : PUnit → L.ι)
    (hj : r z ∈ (L.pull F).U J) (hj' : r z ∈ (L.pull F).U J') :
    gm r z ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (r ≫ F) z _ (L.g (J PUnit.unit) (J' PUnit.unit)) :=
  (gm_linComb L (fun _ : PUnit => F) (fun _ => 1) r z J J' hj hj').trans (by rw [Fintype.prod_subsingleton, zpow_one])

theorem mem_pull {x : X'} {J : PUnit → L.ι} : x ∈ (L.pull F).U J ↔ F x ∈ L.U (J PUnit.unit) := by
  exact ⟨fun h => Set.mem_iInter.mp h PUnit.unit,
    fun h => Set.mem_iInter.mpr fun j => Subsingleton.elim PUnit.unit j ▸ h⟩

def gw (w : LB.Iso L' (L.pull F)) (f : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w.s (fun _ => j, k))

def PGen (w : LB.Iso L' (L.pull F)) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X') (y : Y) (j j' : L.ι) (k k' : L'.ι), F (f y) ∈ L.U j → F (f y) ∈ L.U j' → f y ∈ L'.U k →
    f y ∈ L'.U k' → gw w f y j k = gm (f ≫ F) y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gw w f y j' k'

theorem pGen_of_isGen {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) : PGen w := by
  intro Y f y j j' k k' hj hj' hk hk'
  let p : (L.pull F).ι × L'.ι := (fun _ => j, k)
  let q : (L.pull F).ι × L'.ι := (fun _ => j', k')
  let U := (L.pull F).U p.1 ⊓ L'.U p.2
  let V := (L.pull F).U q.1 ⊓ L'.U q.2
  have hp : f y ∈ U := ⟨mem_pull.mpr hj, hk⟩
  have hq : f y ∈ V := ⟨mem_pull.mpr hj', hk'⟩
  have hm : f y ∈ U ⊓ V := ⟨hp, hq⟩
  have e := congrArg (gm f y (U ⊓ V)) (hw p q)
  calc
    _ = gm f y (U ⊓ V) (res (inf_le_left : U ⊓ V ≤ U) (w.s p)) :=
      (gm_res f y inf_le_left hm _).symm
    _ = _ := e
    _ = _ := (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_div L' (L.pull F) f y p q hm).trans
        (congrArg (· * (gm f y _ (L'.g k k'))⁻¹) (gm_pull_g L F f y p.1 q.1 hp.1 hq.1)))
      (gm_res f y inf_le_right hm _))

variable {K : Type} [Fintype K]

def trF (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (j j' : K → L.ι) : (Z.presheaf.stalk z)ˣ :=
  ∏ k, gm (r ≫ φ k) z (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)) ^ ε k

theorem gen_trans {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    {j j' : K → L.ι} (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gm r z (LB.wchart L φ j) (t.s j) = trF φ ε r z j j' * gm r z (LB.wchart L φ j') (t.s j') := by
  have hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := ⟨hj, hj'⟩
  have e := congrArg (gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j')) (ht j j')
  have e1 : gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j') = trF φ ε r z j j' :=
    gm_linComb L φ ε r z j j' hj hj'
  exact (gm_res r z inf_le_left hm _).symm.trans
    (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) e1 (gm_res r z inf_le_right hm _))))

theorem isGen_of_gm {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (h : ∀ (y : Y) j j', y ∈ LB.wchart L φ j → y ∈ LB.wchart L φ j' →
      gm (𝟙 Y) y _ (t.s j) = trF φ ε (𝟙 Y) y j j' * gm (𝟙 Y) y _ (t.s j')) :
    t.IsGen := by
  intro j j'
  apply unit_ext
  intro y hy
  refine (gm_res (𝟙 Y) y inf_le_left hy _).trans ((h y j j' hy.1 hy.2).trans ?_)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) (gm_res (𝟙 Y) y inf_le_right hy _))).symm

/-- Unit sections with the same germs on chart overlaps glue uniquely. -/
theorem glue_unit {ι : Type} (U : Y.Opens) (V : ι → Y.Opens) (hV : ∀ i, V i ≤ U)
    (hcov : U ≤ ⨆ i, V i) (a : ∀ i, Γ(Y, V i)ˣ)
    (h : ∀ i j, ∀ y ∈ V i ⊓ V j, gm (𝟙 Y) y (V i) (a i) = gm (𝟙 Y) y (V j) (a j)) :
    ∃ s : Γ(Y, U)ˣ, ∀ i, res (hV i) s = a i := by
  apply ExistsUnique.exists
  refine existsUnique_glueUnits V hV hcov a fun i j => unit_ext fun y hy => ?_
  exact (gm_res (𝟙 Y) y inf_le_left hy _).trans ((h i j y hy).trans
    (gm_res (𝟙 Y) y inf_le_right hy _).symm)

def PMaps (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι), (∀ k, F (φ' k (r z)) ∈ L.U (p k)) →
    (∀ k, φ' k (r z) ∈ L'.U (q k)) →
    gm (r ≫ h) z (LB.wchart L φ p) (t.s p) =
      (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ' q) (a.s q)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
