import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleComposition

/-! A generator of the quotient line bundle acts by multiplication on local
sections. The resulting linear isomorphisms commute with restriction. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M N : LB X} {V W : X.Opens}

private abbrev restrict (L : LB X) (h : W ≤ V) :=
  (toMod L).presheaf.map (homOfLE h).op

private theorem restrict_comp (L : LB X) {U : X.Opens} (e : U ≤ W) (h : W ≤ V)
    (x : Γ(toMod L, V)) : restrict L e (restrict L h x) = restrict L (e.trans h) x := by
  unfold restrict
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private def chartIso (hM : M.IsLB) (hN : N.IsLB) (w : LB.Iso M N)
    (p : N.ι × M.ι) (hp : V ≤ (N.div M).U p) :
    Γ(toMod M, V) ≃ₗ[Γ(X, V)] Γ(toMod N, V) :=
  let u := res hp (w.s p)
  (chartEquiv hM p.2 (hp.trans inf_le_right)).trans
    ((LinearEquiv.smulOfUnit (M := Γ(X, V)) u).trans
      (chartEquiv hN p.1 (hp.trans inf_le_left)).symm)

private theorem chartIso_coord (hM : M.IsLB) (hN : N.IsLB) (w : LB.Iso M N)
    (p : N.ι × M.ι) (hp : V ≤ (N.div M).U p) (x : Γ(toMod M, V)) :
    chartEquiv hN p.1 (hp.trans inf_le_left) (chartIso hM hN w p hp x) =
      (res hp (w.s p)).val * chartEquiv hM p.2 (hp.trans inf_le_right) x := by
  exact LinearEquiv.apply_symm_apply _ _

private theorem chartIso_restrict (hM : M.IsLB) (hN : N.IsLB) (w : LB.Iso M N)
    (p : N.ι × M.ι) (hp : V ≤ (N.div M).U p) (h : W ≤ V) (x : Γ(toMod M, V)) :
    chartIso hM hN w p (h.trans hp) (restrict M h x) =
      restrict N h (chartIso hM hN w p hp x) := by
  apply (chartEquiv hN p.1 ((h.trans hp).trans inf_le_left)).injective
  rw [chartIso_coord, chartEquiv_map hM p.2 (hp.trans inf_le_right) h x,
    chartEquiv_map hN p.1 (hp.trans inf_le_left) h (chartIso hM hN w p hp x),
    chartIso_coord, map_mul]
  exact congrArg (fun u : Γ(X, W) => u * resG X h (chartEquiv hM p.2 (hp.trans inf_le_right) x))
    (congrArg Units.val (res_res hp h (w.s p))).symm

private theorem chartIso_overlap (hM : M.IsLB) (hN : N.IsLB) {w : LB.Iso M N} (hw : w.IsGen)
    (p q : N.ι × M.ι) (hp : V ≤ (N.div M).U p) (hq : V ≤ (N.div M).U q)
    (x : Γ(toMod M, V)) : chartIso hM hN w p hp x = chartIso hM hN w q hq x := by
  let a := res (le_inf (hp.trans inf_le_left) (hq.trans inf_le_left)) (N.g p.1 q.1)
  let b := res (le_inf (hp.trans inf_le_right) (hq.trans inf_le_right)) (M.g p.2 q.2)
  have hu : res hp (w.s p) * b = a * res hq (w.s q) := by
    have e := hw.restrict hp hq
    rw [LB.res_div_g M N hp hq] at e
    change res hp (w.s p) = (a * b⁻¹) * res hq (w.s q) at e
    rw [e, mul_right_comm _ _ b, inv_mul_cancel_right]
  apply (chartEquiv hN p.1 (hp.trans inf_le_left)).injective
  rw [chartIso_coord,
    chartEquiv_change hN p.1 q.1 (hp.trans inf_le_left) (hq.trans inf_le_left),
    chartIso_coord,
    chartEquiv_change hM p.2 q.2 (hp.trans inf_le_right) (hq.trans inf_le_right)]
  rw [← mul_assoc, ← mul_assoc]
  exact congrArg (· * chartEquiv hM q.2 (hq.trans inf_le_right) x) (congrArg Units.val hu)

private def refineOpen (V : X.Opens) (p : N.ι × M.ι) : X.Opens := V ⊓ (N.div M).U p

private theorem refineOpen_covers (hM : M.IsLB) (hN : N.IsLB) (V : X.Opens) :
    V ≤ ⨆ p, refineOpen (M := M) (N := N) V p := by
  have hc : (⨆ p : N.ι × M.ι, (N.div M).U p) = ⊤ := by
    change (⨆ p : N.ι × M.ι, N.U p.1 ⊓ M.U p.2) = ⊤
    rw [iSup_prod]
    simp only [← inf_iSup_eq, hM.cover, inf_top_eq, hN.cover]
  simp only [refineOpen, ← inf_iSup_eq, hc, inf_top_eq, le_rfl]

private theorem section_ext_on_refine (hM : M.IsLB) (hN : N.IsLB) (L : LB X)
    {x y : Γ(toMod L, V)}
    (h : ∀ p, restrict L (inf_le_left : refineOpen (M := M) (N := N) V p ≤ V) x =
      restrict L inf_le_left y) : x = y := by
  let F : TopCat.Sheaf AddCommGrpCat.{0} X :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (toMod L)
  exact F.eq_of_locally_eq' (refineOpen (M := M) (N := N) V) V
    (fun _ => homOfLE inf_le_left) (refineOpen_covers hM hN V) x y h

private theorem exists_sectionIso (hM : M.IsLB) (hN : N.IsLB) {w : LB.Iso M N} (hw : w.IsGen)
    (x : Γ(toMod M, V)) :
    ∃ y : Γ(toMod N, V), ∀ p, restrict N (inf_le_left : refineOpen (M := M) (N := N) V p ≤ V) y =
      chartIso hM hN w p inf_le_right (restrict M inf_le_left x) := by
  let U := refineOpen (M := M) (N := N) V
  let F : TopCat.Sheaf AddCommGrpCat.{0} X :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (toMod N)
  refine (F.existsUnique_gluing' U V (fun _ => homOfLE inf_le_left)
    (refineOpen_covers hM hN V)
    (fun p => chartIso hM hN w p inf_le_right (restrict M (inf_le_left : U p ≤ V) x))
    (fun p q => ?_)).exists
  change restrict N (inf_le_left : U p ⊓ U q ≤ U p)
      (chartIso hM hN w p inf_le_right (restrict M (inf_le_left : U p ≤ V) x)) =
    restrict N (inf_le_right : U p ⊓ U q ≤ U q)
      (chartIso hM hN w q inf_le_right (restrict M (inf_le_left : U q ≤ V) x))
  let i : U p ⊓ U q ≤ U p := inf_le_left
  let j : U p ⊓ U q ≤ U q := inf_le_right
  let ip : U p ≤ (N.div M).U p := inf_le_right
  let jq : U q ≤ (N.div M).U q := inf_le_right
  calc
    _ = chartIso hM hN w p (i.trans ip) (restrict M i (restrict M inf_le_left x)) :=
      (chartIso_restrict hM hN w p ip i _).symm
    _ = chartIso hM hN w p (i.trans ip) (restrict M j (restrict M inf_le_left x)) :=
      congrArg (chartIso hM hN w p (i.trans ip))
        ((restrict_comp M i inf_le_left x).trans (restrict_comp M j inf_le_left x).symm)
    _ = chartIso hM hN w q (j.trans jq) (restrict M j (restrict M inf_le_left x)) :=
      chartIso_overlap hM hN hw p q _ _ _
    _ = _ := chartIso_restrict hM hN w q jq j _

private def sectionIsoMap (hM : M.IsLB) (hN : N.IsLB) {w : LB.Iso M N} (hw : w.IsGen)
    (x : Γ(toMod M, V)) : Γ(toMod N, V) := (exists_sectionIso hM hN hw x).choose

private theorem restrict_sectionIsoMap (hM : M.IsLB) (hN : N.IsLB) {w : LB.Iso M N}
    (hw : w.IsGen) (x : Γ(toMod M, V)) (p : N.ι × M.ι) :
    restrict N (inf_le_left : refineOpen (M := M) (N := N) V p ≤ V)
      (sectionIsoMap hM hN hw x) =
      chartIso hM hN w p inf_le_right (restrict M inf_le_left x) :=
  (exists_sectionIso hM hN hw x).choose_spec p

private theorem sectionIsoMap_bijective (hM : M.IsLB) (hN : N.IsLB) {w : LB.Iso M N}
    (hw : w.IsGen) : Function.Bijective (sectionIsoMap (V := V) hM hN hw) := by
  constructor
  · intro x y e
    refine section_ext_on_refine hM hN M fun p => (chartIso hM hN w p inf_le_right).injective ?_
    rw [← restrict_sectionIsoMap hM hN hw, ← restrict_sectionIsoMap hM hN hw, e]
  · intro y
    let U := refineOpen (M := M) (N := N) V
    let F : TopCat.Sheaf AddCommGrpCat.{0} X :=
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (toMod M)
    let a (p : N.ι × M.ι) : Γ(toMod M, U p) :=
      (chartIso hM hN w p inf_le_right).symm (restrict N inf_le_left y)
    have ha (p : N.ι × M.ι) : chartIso hM hN w p inf_le_right (a p) = restrict N inf_le_left y :=
      LinearEquiv.apply_symm_apply _ _
    have hc (p q : N.ι × M.ι) : restrict M (inf_le_left : U p ⊓ U q ≤ U p) (a p) =
        restrict M (inf_le_right : U p ⊓ U q ≤ U q) (a q) := by
      let hp : U p ⊓ U q ≤ (N.div M).U p := inf_le_left.trans inf_le_right
      let hq : U p ⊓ U q ≤ (N.div M).U q := inf_le_right.trans inf_le_right
      apply (chartIso hM hN w p hp).injective
      calc
        _ = restrict N (inf_le_left : U p ⊓ U q ≤ U p)
            (chartIso hM hN w p inf_le_right (a p)) := chartIso_restrict hM hN w p _ _ _
        _ = restrict N (inf_le_left : U p ⊓ U q ≤ U p)
            (restrict N (inf_le_left : U p ≤ V) y) := congrArg (restrict N _) (ha p)
        _ = restrict N (inf_le_right : U p ⊓ U q ≤ U q)
            (restrict N (inf_le_left : U q ≤ V) y) :=
          (restrict_comp N _ _ _).trans (restrict_comp N _ _ _).symm
        _ = restrict N (inf_le_right : U p ⊓ U q ≤ U q)
            (chartIso hM hN w q inf_le_right (a q)) := congrArg (restrict N _) (ha q).symm
        _ = chartIso hM hN w q hq (restrict M inf_le_right (a q)) :=
          (chartIso_restrict hM hN w q _ _ _).symm
        _ = _ := (chartIso_overlap hM hN hw p q hp hq _).symm
    obtain ⟨x, hx, -⟩ := F.existsUnique_gluing' U V (fun _ => homOfLE inf_le_left)
      (refineOpen_covers hM hN V) a hc
    refine ⟨x, section_ext_on_refine hM hN N fun p => ?_⟩
    rw [restrict_sectionIsoMap, show restrict M (inf_le_left : U p ≤ V) x = a p from hx p, ha]

/-- Multiplication by the local units of a line-bundle isomorphism transports sections. -/
def sectionIsoEquiv (hM : M.IsLB) (hN : N.IsLB) {w : LB.Iso M N} (hw : w.IsGen) :
    Γ(toMod M, V) ≃ₗ[Γ(X, V)] Γ(toMod N, V) :=
  LinearEquiv.ofBijective
    { toFun := sectionIsoMap hM hN hw
      map_add' := fun x y => section_ext_on_refine hM hN N fun p => by
        simp only [map_add, restrict_sectionIsoMap]
      map_smul' := fun r x => section_ext_on_refine hM hN N fun p => by
        let h : refineOpen (M := M) (N := N) V p ≤ V := inf_le_left
        have resM : restrict M h (r • x) = resG X h r • restrict M h x :=
          secRes_smul M h r x
        have resN : restrict N h (r • sectionIsoMap hM hN hw x) =
            resG X h r • restrict N h (sectionIsoMap hM hN hw x) := secRes_smul N h r _
        let E := chartIso hM hN w p (V := refineOpen V p) inf_le_right
        calc
          _ = E (restrict M h (r • x)) := restrict_sectionIsoMap hM hN hw _ p
          _ = E (resG X h r • restrict M h x) := congrArg E resM
          _ = resG X h r • E (restrict M h x) := E.map_smul _ _
          _ = resG X h r • restrict N h (sectionIsoMap hM hN hw x) :=
            congrArg (fun t : Γ(toMod N, refineOpen V p) => resG X h r • t)
              (restrict_sectionIsoMap hM hN hw x p).symm
          _ = _ := resN.symm }
    (sectionIsoMap_bijective hM hN hw)

theorem sectionIsoEquiv_restrict (hM : M.IsLB) (hN : N.IsLB) {w : LB.Iso M N}
    (hw : w.IsGen) (h : W ≤ V) (x : Γ(toMod M, V)) :
    sectionIsoEquiv hM hN hw (restrict M h x) =
      restrict N h (sectionIsoEquiv hM hN hw x) := by
  refine section_ext_on_refine hM hN N fun p => ?_
  let i : refineOpen (M := M) (N := N) W p ≤ refineOpen (M := M) (N := N) V p :=
    inf_le_inf_right _ h
  change restrict N inf_le_left (sectionIsoMap hM hN hw (restrict M h x)) =
    restrict N inf_le_left (restrict N h (sectionIsoMap hM hN hw x))
  let hW : refineOpen (M := M) (N := N) W p ≤ W := inf_le_left
  let hV : refineOpen (M := M) (N := N) V p ≤ V := inf_le_left
  calc
    _ = chartIso hM hN w p inf_le_right (restrict M hW (restrict M h x)) :=
      restrict_sectionIsoMap hM hN hw _ p
    _ = chartIso hM hN w p inf_le_right (restrict M i (restrict M hV x)) :=
      congrArg (chartIso hM hN w p inf_le_right)
        ((restrict_comp M hW h x).trans (restrict_comp M i hV x).symm)
    _ = restrict N i (chartIso hM hN w p inf_le_right (restrict M hV x)) :=
      chartIso_restrict hM hN w p inf_le_right i _
    _ = restrict N i (restrict N hV (sectionIsoMap hM hN hw x)) :=
      congrArg (restrict N i) (restrict_sectionIsoMap hM hN hw x p).symm
    _ = _ := (restrict_comp N i hV _).trans (restrict_comp N hW h _).symm

end GlobalTheory.LineBundleSections
