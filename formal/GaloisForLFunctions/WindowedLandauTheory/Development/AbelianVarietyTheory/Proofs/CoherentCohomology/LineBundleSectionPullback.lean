import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleChartPullback

/-! Pullback of line-bundle sections in compatible trivializations. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X Y : Scheme.{0}} {π : Y ⟶ X}
  {L : LB X} {M : LB Y}

theorem resG_appLE {U : X.Opens} {V W : Y.Opens} (h : V ≤ π ⁻¹ᵁ U) (i : W ≤ V)
    (a : Γ(X, U)) :
    resG Y i (π.appLE U V h a) = π.appLE U W (i.trans h) a :=
  congrArg (fun f : Γ(X, U) ⟶ Γ(Y, W) => f a) (π.appLE_map h (homOfLE i).op)

theorem appLE_resG {U U' : X.Opens} {V : Y.Opens} (h : V ≤ π ⁻¹ᵁ U') (i : U' ≤ U)
    (a : Γ(X, U)) :
    π.appLE U' V h (resG X i a) = π.appLE U V (h.trans (π.preimage_mono i)) a :=
  congrArg (fun f : Γ(X, U) ⟶ Γ(Y, V) => f a) (π.map_appLE h (homOfLE i).op)

private theorem chartPull_coord_rel (P : ChartPull M L π) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ π ⁻¹ᵁ U) (s : Γ(toMod L, U)) (i j : M.ι) :
    let a (i : M.ι) : Γ(Y, V ⊓ M.U i) :=
      π.appLE (U ⊓ L.U (P.idx i)) (V ⊓ M.U i)
        (le_inf (inf_le_left.trans h) (inf_le_right.trans (P.le i))) (coord s (P.idx i))
    resG Y (inf_le_left : V ⊓ M.U i ⊓ M.U j ≤ V ⊓ M.U i) (a i) =
      resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        V ⊓ M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j) (M.g i j : Γ(Y, M.U i ⊓ M.U j)) *
      resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        V ⊓ M.U i ⊓ M.U j ≤ V ⊓ M.U j) (a j) := by
  dsimp only
  let W := V ⊓ M.U i ⊓ M.U j
  let W₀ := U ⊓ L.U (P.idx i) ⊓ L.U (P.idx j)
  have hi : W ≤ M.U i := inf_le_left.trans inf_le_right
  have hj : W ≤ M.U j := inf_le_right
  have e : W ≤ π ⁻¹ᵁ W₀ :=
    le_inf (le_inf (inf_le_left.trans (inf_le_left.trans h)) (hi.trans (P.le i)))
      (hj.trans (P.le j))
  have hg := congrArg Units.val (P.restrict_g hi hj)
  change resG Y (le_inf hi hj) (M.g i j : Γ(Y, M.U i ⊓ M.U j)) =
    π.appLE (L.U (P.idx i) ⊓ L.U (P.idx j)) W
      (le_inf (hi.trans (P.le i)) (hj.trans (P.le j)))
      (L.g (P.idx i) (P.idx j) : Γ(X, L.U (P.idx i) ⊓ L.U (P.idx j))) at hg
  have hr := congrArg (fun a : Γ(X, W₀) => π.appLE W₀ W e a)
    (coord_rel s (P.idx i) (P.idx j) (W := W₀) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
  simp only [map_mul, appLE_resG] at hr
  rw [resG_appLE, resG_appLE, hg]
  exact hr

/-- Pull back each section coordinate through the chart refinement. -/
def pullSection (P : ChartPull M L π) {U : X.Opens} {V : Y.Opens} (h : V ≤ π ⁻¹ᵁ U) :
    Γ(toMod L, U) →+ Γ(toMod M, V) :=
  let app (i : M.ι) := (π.appLE (U ⊓ L.U (P.idx i)) (V ⊓ M.U i)
    (le_inf (inf_le_left.trans h) (inf_le_right.trans (P.le i)))).hom
  { toFun := fun s => mkSec (fun i => app i (coord s (P.idx i))) (chartPull_coord_rel P h s)
    map_zero' := sec_ext fun i => (app i).map_zero
    map_add' := fun s t => sec_ext fun i => (app i).map_add (coord s (P.idx i)) (coord t (P.idx i)) }

@[simp] theorem coord_pullSection (P : ChartPull M L π) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ π ⁻¹ᵁ U) (s : Γ(toMod L, U)) (i : M.ι) :
    coord (pullSection P h s) i =
      π.appLE (U ⊓ L.U (P.idx i)) (V ⊓ M.U i)
        (le_inf (inf_le_left.trans h) (inf_le_right.trans (P.le i))) (coord s (P.idx i)) := rfl

theorem pullSection_smul (P : ChartPull M L π) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ π ⁻¹ᵁ U) (r : Γ(X, U)) (s : Γ(toMod L, U)) :
    pullSection P h (r • s) = π.appLE U V h r • pullSection P h s := by
  apply sec_ext
  intro i
  simp only [coord_pullSection, coord_smul, map_mul, appLE_resG, resG_appLE]

theorem pullSection_restrict (P : ChartPull M L π) {U U' : X.Opens} {V V' : Y.Opens}
    (h : V ≤ π ⁻¹ᵁ U) (h' : V' ≤ π ⁻¹ᵁ U') (i : U' ≤ U) (j : V' ≤ V)
    (s : Γ(toMod L, U)) :
    pullSection P h' ((toMod L).presheaf.map (homOfLE i).op s) =
      (toMod M).presheaf.map (homOfLE j).op (pullSection P h s) := by
  apply sec_ext
  intro k
  simp only [coord_pullSection, coord_map, appLE_resG, resG_appLE]

theorem chartEquiv_pullSection (P : ChartPull M L π) (hL : L.IsLB) (hM : M.IsLB)
    {U : X.Opens} {V : Y.Opens} (h : V ≤ π ⁻¹ᵁ U) {i : M.ι}
    (hi : U ≤ L.U (P.idx i)) (hj : V ≤ M.U i) (s : Γ(toMod L, U)) :
    chartEquiv hM i hj (pullSection P h s) = π.appLE U V h (chartEquiv hL (P.idx i) hi s) := by
  simp only [chartEquiv_apply, coord_pullSection, appLE_resG, resG_appLE]

theorem pull_chart (L : LB X) (π : Y ⟶ X) (i : L.ι) :
    (L.pull π).U (fun _ => i) = π ⁻¹ᵁ L.U i :=
  le_antisymm ((ChartPull.pull L π).le _) (fun _ hy => Set.mem_iInter.mpr fun _ => hy)

end GlobalTheory.LineBundleSections
