import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.KernelAverageSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback

/-! The normalized trace on coefficients extends to sections of a pulled-back
line bundle, since the transition functions are pulled back from downstairs. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open GlobalTheory.LineBundleSections
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.FlatDescent

variable {Y : Scheme.{0}} {G : Type} [Group G] [Fintype G]
  {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (hτ : ∀ g, τ g ≫ q = q)
  (hmul : ∀ a b, τ a ≫ τ b = τ (a * b)) (hD : Descends q τ) (u : Γ(Y, ⊤)ˣ)
  {L : LB Y}

private theorem preimage_chart {U W : Y.Opens} {i : L.ι} (h : W ≤ U) (hi : W ≤ L.U i) :
    q ⁻¹ᵁ W ≤ (q ⁻¹ᵁ U) ⊓ (L.pull q).U (fun _ => i) :=
  le_inf (q.preimage_mono h) ((q.preimage_mono hi).trans (pull_chart L q i).ge)

private theorem app_resG {U V : Y.Opens} (i : V ≤ U) (a : Γ(Y, U)) :
    q.app V (resG Y i a) = resG Y (q.preimage_mono i) (q.app U a) :=
  ConcreteCategory.congr_hom (q.naturality (homOfLE i).op) a

private theorem average_mul {W : Y.Opens} (a : Γ(Y, W)) (b : Γ(Y, q ⁻¹ᵁ W)) :
    averageSections hτ hmul hD u W (q.app W a * b) =
      a * averageSections hτ hmul hD u W b := by
  letI : Module Γ(Y, W) Γ(Y, q ⁻¹ᵁ W) := Module.compHom _ (q.app W).hom
  exact (averageSections hτ hmul hD u W).map_smul a b

private def traceCoord {U : Y.Opens} (s : Γ(toMod (L.pull q), q ⁻¹ᵁ U)) (i : L.ι) : Γ(Y, U ⊓ L.U i) :=
  averageSections hτ hmul hD u _ (resG Y (preimage_chart inf_le_left inf_le_right) (coord s (fun _ => i)))

private theorem traceCoord_res {U W : Y.Opens} (s : Γ(toMod (L.pull q), q ⁻¹ᵁ U))
    (i : L.ι) (h : W ≤ U) (hi : W ≤ L.U i) :
    resG Y (le_inf h hi) (traceCoord hτ hmul hD u s i) =
      averageSections hτ hmul hD u W (resG Y (preimage_chart h hi) (coord s (fun _ => i))) := by
  simp only [traceCoord, averageSections_res, resG_resG]

private theorem traceCoord_compat {U : Y.Opens} (s : Γ(toMod (L.pull q), q ⁻¹ᵁ U)) (i j : L.ι) :
    let W := U ⊓ L.U i ⊓ L.U j
    resG Y (inf_le_left : W ≤ U ⊓ L.U i) (traceCoord hτ hmul hD u s i) =
      resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W ≤ L.U i ⊓ L.U j)
        (L.g i j : Γ(Y, L.U i ⊓ L.U j)) *
      resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W ≤ U ⊓ L.U j)
        (traceCoord hτ hmul hD u s j) := by
  let W := U ⊓ L.U i ⊓ L.U j
  have h : W ≤ U := inf_le_left.trans inf_le_left
  have hi : W ≤ L.U i := inf_le_left.trans inf_le_right
  have hj : W ≤ L.U j := inf_le_right
  let a := resG Y (le_inf hi hj) (L.g i j : Γ(Y, L.U i ⊓ L.U j))
  let avg := averageSections hτ hmul hD u W
  have ri : q ⁻¹ᵁ W ≤ (L.pull q).U (fun _ => i) := (preimage_chart (q := q) h hi).trans inf_le_right
  have rj : q ⁻¹ᵁ W ≤ (L.pull q).U (fun _ => j) := (preimage_chart (q := q) h hj).trans inf_le_right
  have hg := congrArg Units.val ((ChartPull.pull L q).restrict_g ri rj)
  change resG Y (le_inf ri rj) ((L.pull q).g (fun _ => i) (fun _ => j) : Γ(Y, _)) =
    q.appLE (L.U i ⊓ L.U j) (q ⁻¹ᵁ W) (q.preimage_mono (le_inf hi hj)) (L.g i j).val at hg
  have hg' := hg.trans ((appLE_resG (π := q) (le_rfl : q ⁻¹ᵁ W ≤ q ⁻¹ᵁ W)
    (le_inf hi hj) (L.g i j).val).symm)
  have hq : q.appLE W (q ⁻¹ᵁ W) le_rfl = q.app W := q.app_eq_appLE.symm
  have hrel := coord_rel s (fun _ => i) (fun _ => j)
    (preimage_chart h hi) (preimage_chart h hj) (le_inf ri rj)
  let b := resG Y (preimage_chart h hj) (coord s (fun _ => j))
  have htransition := hg'.trans (congrArg (fun r : Γ(Y, W) ⟶ Γ(Y, q ⁻¹ᵁ W) => r a) hq)
  have hprod := hrel.trans (congrArg (· * b) htransition)
  exact (traceCoord_res hτ hmul hD u s i h hi).trans
    ((congrArg avg hprod).trans ((average_mul hτ hmul hD u a b).trans
      (congrArg (a * ·) (traceCoord_res hτ hmul hD u s j h hj).symm)))

/-- The normalized coefficient trace descends sections of a pulled-back line bundle. -/
def averageLineBundle {U : Y.Opens} :
    Γ(toMod (L.pull q), q ⁻¹ᵁ U) →+ Γ(toMod L, U) where
  toFun s := mkSec (traceCoord hτ hmul hD u s) (traceCoord_compat hτ hmul hD u s)
  map_zero' := sec_ext fun i => by simp only [coord_mkSec, traceCoord, coord_zero, map_zero]
  map_add' s t := sec_ext fun i => by simp only [coord_mkSec, traceCoord, coord_add, map_add]

theorem averageLineBundle_smul {U : Y.Opens} (a : Γ(Y, U))
    (s : Γ(toMod (L.pull q), q ⁻¹ᵁ U)) :
    averageLineBundle hτ hmul hD u (q.app U a • s) = a • averageLineBundle hτ hmul hD u s := by
  apply sec_ext
  intro i
  let W := U ⊓ L.U i
  change traceCoord hτ hmul hD u (q.app U a • s) i =
    resG Y (inf_le_left : W ≤ U) a * traceCoord hτ hmul hD u s i
  simp only [traceCoord, coord_smul, map_mul, resG_resG]
  exact (congrArg (fun b => averageSections hτ hmul hD u W
    (b * resG Y (preimage_chart inf_le_left inf_le_right) (coord s (fun _ => i))))
    (app_resG inf_le_left a).symm).trans (average_mul hτ hmul hD u _ _)

theorem averageLineBundle_res {U V : Y.Opens} (i : V ≤ U) (s : Γ(toMod (L.pull q), q ⁻¹ᵁ U)) :
    (toMod L).presheaf.map (homOfLE i).op (averageLineBundle hτ hmul hD u s) =
      averageLineBundle hτ hmul hD u ((toMod (L.pull q)).presheaf.map (homOfLE (q.preimage_mono i)).op s) := by
  apply sec_ext
  intro j
  simp only [coord_map, averageLineBundle, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coord_mkSec,
    traceCoord, averageSections_res, resG_resG]

theorem averageLineBundle_pull {U : Y.Opens} (hu : u.val = (Fintype.card G : Γ(Y, ⊤)))
    (s : Γ(toMod L, U)) :
    averageLineBundle hτ hmul hD u (pullSection (ChartPull.pull L q)
      (le_rfl : q ⁻¹ᵁ U ≤ q ⁻¹ᵁ U) s) = s := by
  apply sec_ext
  intro i
  change traceCoord hτ hmul hD u _ i = _
  unfold traceCoord
  rw [coord_pullSection, resG_appLE]
  let W := U ⊓ L.U i
  have hq : q.appLE W (q ⁻¹ᵁ W) le_rfl = q.app W := q.app_eq_appLE.symm
  change averageSections hτ hmul hD u W (q.appLE W (q ⁻¹ᵁ W) le_rfl (coord s i)) = coord s i
  exact (congrArg (fun r : Γ(Y, W) ⟶ Γ(Y, q ⁻¹ᵁ W) =>
    averageSections hτ hmul hD u W (r (coord s i))) hq).trans
    (averageSections_pull hτ hmul hD u hu _ (coord s i))

end GlobalTheory.FlatDescent
