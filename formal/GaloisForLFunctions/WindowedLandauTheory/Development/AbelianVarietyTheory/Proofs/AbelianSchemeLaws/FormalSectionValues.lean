import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalPullbackGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.StructureSheafSectionGerms

/-! Germs of sections of formal products of line bundles. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

/-- A section coefficient in the charts assigned to the pulled-back factors. -/
def sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    Z.presheaf.stalk z := gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (s.f (fun k => J (r ≫ φ k)))

/-- Section coefficients transform by the product of the factor transitions. -/
theorem sec_trans {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {j j' : K → L.ι} (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gs r z (LB.wchart L φ j) (s.f j) = (trF φ ε r z j j').val * gs r z (LB.wchart L φ j') (s.f j') := by
  have hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := ⟨hj, hj'⟩
  have e := congrArg (gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j')) (s.compat j j')
  have e1 := (gs_unit r z _ hm ((LB.LinComb L φ ε).g j j')).trans
    (congrArg Units.val (gm_linComb L φ ε r z j j' hj hj'))
  exact (gs_res r z inf_le_left hm _).symm.trans
    (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) e1 (gs_res r z inf_le_right hm _))))

/-- Germs in compatible chart assignments determine every section coefficient. -/
theorem sec_ext_val (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = sval s' (𝟙 Y) y J) (j : K → L.ι) : s.f j = s'.f j := by
  apply fn_ext
  intro y hy
  choose J hchart using fun f : Y ⟶ X => exists_chart hL (f y)
  have hJ : Good L y J := hchart
  exact (sec_trans s (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))).trans
    ((congrArg ((trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * ·) (h y J hJ)).trans
      (sec_trans s' (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))).symm)

/-- Glue a section in a new formal presentation with the same factors and exponents. -/
theorem exists_sec_of_formEq (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s' : LB.Sec (LB.LinComb L φ' ε'),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s' r z J = sval s r z J := by
  have glue : ∀ j : K' → L.ι, ∃ a : Γ(Y, LB.wchart L φ' j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Y ⟶ X) → L.ι),
      r z ∈ LB.wchart L φ' j → r z ∈ LB.wchart L φ' (fun k => I (φ' k)) → r z ∈ LB.wchart L φ (fun k => I (φ k)) →
      gs r z _ a = (trF φ' ε' r z j (fun k => I (φ' k))).val * gs r z (LB.wchart L φ (fun k => I (φ k))) (s.f (fun k => I (φ k))) := by
    intro j
    let W : ((Y ⟶ X) → L.ι) → Y.Opens := fun I =>
      LB.wchart L φ' j ⊓ LB.wchart L φ' (fun k => I (φ' k)) ⊓ LB.wchart L φ (fun k => I (φ k))
    obtain ⟨u, hu⟩ : ∃ u : ∀ I, Γ(Y, W I), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) I, r z ∈ W I →
        gs r z (W I) (u I) = (trF φ' ε' r z j (fun k => I (φ' k))).val * gs r z (LB.wchart L φ (fun k => I (φ k))) (s.f (fun k => I (φ k))) :=
      ⟨fun I => (Y.presheaf.map (homOfLE (inf_le_left : W I ≤ LB.wchart L φ' j ⊓ LB.wchart L φ' (fun k => I (φ' k)))).op).hom
          ((LB.LinComb L φ' ε').g j (fun k => I (φ' k))).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W I ≤ LB.wchart L φ (fun k => I (φ k)))).op).hom (s.f (fun k => I (φ k))), fun Z r z I hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans ((gs_unit r z _ hz.1 _).trans
          (congrArg Units.val (gm_linComb L φ' ε' r z _ _ hz.1.1 hz.1.2)))) (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L φ' j)
      (fun I => homOfLE (inf_le_left.trans inf_le_left)) (fun y hy => by
        choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
        exact Opens.mem_iSup.2 ⟨I, ⟨hy, Set.mem_iInter.2 fun k => hI _⟩, Set.mem_iInter.2 fun k => hI _⟩) u
      (fun I I' => fn_ext (V := W I ⊓ W I') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y I hy.1, hu _ _ y I' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2]
        let a := trF φ' ε' (𝟙 Y) y j (I ∘ φ')
        let b := trF φ ε (𝟙 Y) y (I ∘ φ) (I' ∘ φ)
        let c := trF φ' ε' (𝟙 Y) y (I ∘ φ') (I' ∘ φ')
        let d := trF φ' ε' (𝟙 Y) y j (I' ∘ φ')
        let v := gs (𝟙 Y) y (LB.wchart L φ (I' ∘ φ)) (s.f (I' ∘ φ))
        change a.val * (b.val * v) = d.val * v
        have he : a * b = d := (congrArg (a * ·) (h.trF (𝟙 Y) y I I')).trans
          (show a * c = d from trF_trans hL φ' ε' (𝟙 Y) y hy.1.1.1 hy.1.1.2 hy.2.1.2)
        exact (mul_assoc _ _ _).symm.trans (congrArg (fun u : (Y.presheaf.stalk y)ˣ => u.val * v) he))
    refine ⟨a, fun Z r z I h₁ h₂ h₃ => ?_⟩
    have hz : r z ∈ W I := ⟨⟨h₁, h₂⟩, h₃⟩
    exact (gs_res r z (inf_le_left.trans inf_le_left) hz a).symm.trans ((congrArg (gs r z (W I)) (ha I)).trans
      (hu Z r z I hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => ?_⟩
  · choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (fun k => I (φ' k)) := Set.mem_iInter.2 fun k => hI _
    have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ (fun k => I (φ k)) := Set.mem_iInter.2 fun k => hI _
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ' ε' (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (ha j _ (𝟙 Y) y I hy.1 m₁ m₂).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y I hy.2 m₁ m₂)).symm)
    rw [← trF_trans hL φ' ε' (𝟙 Y) y hy.1 hy.2 m₁, Units.val_mul, mul_assoc]; rfl
  · have m := hJ.mem φ' r
    refine (ha _ Z r z (fun χ => J (r ≫ χ)) m m (hJ.mem φ r)).trans ?_
    rw [mul_eq_left.1 (trF_trans hL φ' ε' r z m m m), Units.val_one, one_mul]; rfl

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
