import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalProductPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionOperations
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalLineBundleCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionScalarChange

/-! Pulling back a product and composing its factors give the same section
coordinates, with the same action of base scalars. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {X Y Z : Scheme.{0}} {I : Type} [Fintype I]
  (L : LB X) (f : I → (Y ⟶ X)) (a : I → ℤ) (π : Z ⟶ Y)

private theorem composed_chart (i : I → L.ι) :
    (LB.LinComb L (fun k => π ≫ f k) a).U i = π ⁻¹ᵁ (LB.LinComb L f a).U i :=
  le_antisymm ((ChartPull.linComb L f a π).le i)
    (fun _ h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k)

private def toComposedChart :
    ChartPull (LB.LinComb L (fun k => π ≫ f k) a) ((LB.LinComb L f a).pull π) (𝟙 Z) where
  idx i := fun _ => i
  le i := ((ChartPull.linComb L f a π).le i).trans (pull_chart (LB.LinComb L f a) π i).ge
  g i j := by
    rw [pullLE_id]
    exact ((ChartPull.linComb L f a π).g i j).trans
      ((ChartPull.pull (LB.LinComb L f a) π).restrict_g
        (inf_le_left.trans (le_trans ((ChartPull.linComb L f a π).le i)
          (pull_chart (LB.LinComb L f a) π i).ge))
        (inf_le_right.trans (le_trans ((ChartPull.linComb L f a π).le j)
          (pull_chart (LB.LinComb L f a) π j).ge))).symm

private def fromComposedChart :
    ChartPull ((LB.LinComb L f a).pull π) (LB.LinComb L (fun k => π ≫ f k) a) (𝟙 Z) where
  idx i := i PUnit.unit
  le i := ((ChartPull.pull (LB.LinComb L f a) π).le i).trans (composed_chart L f a π _).ge
  g i j := by
    rw [pullLE_id]
    exact ((ChartPull.pull (LB.LinComb L f a) π).g i j).trans
      ((ChartPull.linComb L f a π).restrict_g
        (inf_le_left.trans (le_trans ((ChartPull.pull (LB.LinComb L f a) π).le i)
          (composed_chart L f a π _).ge))
        (inf_le_right.trans (le_trans ((ChartPull.pull (LB.LinComb L f a) π).le j)
          (composed_chart L f a π _).ge))).symm

private theorem id_appLE_apply {U V : Z.Opens} (h : V ≤ U) (s : Γ(Z, U)) :
    (𝟙 Z : Z ⟶ Z).appLE U V h s = resG Z h s := by
  let r : Γ(Z, U) ⟶ Γ(Z, V) := Z.presheaf.map (homOfLE h).op
  exact ConcreteCategory.congr_hom
    ((congrArg (· ≫ r) (Scheme.Hom.id_app U)).trans (Category.id_comp r)) s

private theorem coord_pull_id {M N : LB Z} (P : ChartPull M N (𝟙 Z))
    (s : Γ(toMod N, ⊤)) (i : M.ι) :
    coord (pullSection P (U := ⊤) (V := ⊤) le_rfl s) i =
      resG Z (le_inf inf_le_left (inf_le_right.trans (P.le i))) (coord s (P.idx i)) :=
  (coord_pullSection P le_rfl s i).trans (id_appLE_apply _ _)

/-- Reindex the charts on the base-changed product without changing its sections. -/
def formalProductPullEquiv {S : Type} [CommRing S] (g : Z ⟶ Spec (.of S)) :
    let M := LB.LinComb L f a
    let N := LB.LinComb L (fun k => π ≫ f k) a
    letI := sectionBaseModule g (toMod (M.pull π)) ⊤
    letI := sectionBaseModule g (toMod N) ⊤
    Γ(toMod (M.pull π), ⊤) ≃ₗ[S] Γ(toMod N, ⊤) := by
  let M := LB.LinComb L f a
  let N := LB.LinComb L (fun k => π ≫ f k) a
  letI := sectionAlgebra g (⊤ : Z.Opens)
  letI := sectionBaseModule g (toMod (M.pull π)) ⊤
  letI := sectionBaseModule g (toMod N) ⊤
  let P := toComposedChart L f a π
  let Q := fromComposedChart L f a π
  let F := pullSection P (U := ⊤) (V := ⊤) le_rfl
  let G := pullSection Q (U := ⊤) (V := ⊤) le_rfl
  have hleft : Function.LeftInverse G F := by
    intro s
    apply sec_ext
    intro J
    obtain ⟨i, rfl⟩ : ∃ i : I → L.ι, (fun _ => i) = J :=
      ⟨J PUnit.unit, funext fun u => by
        cases u
        rfl⟩
    let J : (M.pull π).ι := fun _ => i
    let h : (⊤ : Z.Opens) ⊓ (M.pull π).U J ≤ ⊤ ⊓ N.U i :=
      le_inf inf_le_left (inf_le_right.trans (Q.le J))
    let h' : (⊤ : Z.Opens) ⊓ N.U i ≤ ⊤ ⊓ (M.pull π).U J :=
      le_inf inf_le_left (inf_le_right.trans (P.le i))
    change coord (G (F s)) J = coord s J
    refine (coord_pull_id Q (F s) J).trans ?_
    refine (congrArg (resG Z h) (coord_pull_id P s i)).trans ?_
    exact (resG_resG h' h _).trans (resG_self _ _)
  have hright : Function.RightInverse G F := by
    intro s
    apply sec_ext
    intro i
    let J : (M.pull π).ι := fun _ => i
    let h : (⊤ : Z.Opens) ⊓ (M.pull π).U J ≤ ⊤ ⊓ N.U i :=
      le_inf inf_le_left (inf_le_right.trans (Q.le J))
    let h' : (⊤ : Z.Opens) ⊓ N.U i ≤ ⊤ ⊓ (M.pull π).U J :=
      le_inf inf_le_left (inf_le_right.trans (P.le i))
    change coord (F (G s)) i = coord s i
    refine (coord_pull_id P (G s) i).trans ?_
    refine (congrArg (resG Z h') (coord_pull_id Q s J)).trans ?_
    exact (resG_resG h h' _).trans (resG_self _ _)
  refine { F with invFun := G, left_inv := hleft, right_inv := hright, map_smul' := ?_ }
  intro r s
  change F (algebraMap S Γ(Z, ⊤) r • s) = algebraMap S Γ(Z, ⊤) r • F s
  exact (pullSection_smul P le_rfl _ _).trans
    (congrArg (fun a : Γ(Z, ⊤) => a • F s) ((id_appLE_apply le_rfl _).trans (resG_self _ _)))

/-- The section reindexing identifies ordinary pullback with pullback in
the coordinates of the composed factors. -/
theorem formalProductPullEquiv_coord {S : Type} [CommRing S] (g : Z ⟶ Spec (.of S))
    (s : Γ(toMod (LB.LinComb L f a), ⊤)) (i : I → L.ι) :
    (globalCoordinates (formalProductPullEquiv L f a π g
      (pullSection (ChartPull.pull (LB.LinComb L f a) π) (U := ⊤) (V := ⊤) (by simp) s))).f i =
      (pullSec (globalCoordinates s) π).f i := by
  let M := LB.LinComb L f a
  let N := LB.LinComb L (fun k => π ≫ f k) a
  let P := toComposedChart L f a π
  let Q := ChartPull.pull M π
  let t := pullSection Q (U := ⊤) (V := ⊤) (by simp) s
  let J : (M.pull π).ι := fun _ => i
  let U := M.U i
  let W := N.U i
  let h : W ≤ π ⁻¹ᵁ U := (ChartPull.linComb L f a π).le i
  let k : W ≤ (⊤ : Z.Opens) ⊓ (M.pull π).U J := le_inf le_top (P.le i)
  let l : W ≤ (⊤ : Z.Opens) ⊓ N.U i := le_inf le_top le_rfl
  let a₀ := coord s i
  change (globalCoordinates (pullSection P le_rfl t)).f i =
    resG Z h (π.app U (resG Y (le_inf le_top le_rfl) a₀))
  calc
    _ = resG Z k (coord t J) :=
      (globalCoordinates_apply (pullSection P le_rfl t) i).trans
        ((congrArg (resG Z l) (coord_pull_id P t i)).trans (resG_resG _ l _))
    _ = π.appLE (⊤ ⊓ U) W (le_inf le_top h) a₀ :=
      (congrArg (resG Z k) (coord_pullSection Q (by simp) s J)).trans (resG_appLE _ k _)
    _ = π.appLE U W h (resG Y (le_inf le_top le_rfl) a₀) :=
      (appLE_resG h (le_inf le_top le_rfl) a₀).symm
    _ = _ := (resG_appLE le_rfl h _).symm.trans
      (congrArg (resG Z h) (ConcreteCategory.congr_hom (Scheme.Hom.app_eq_appLE π).symm _))

end GlobalTheory.LineBundleSections
