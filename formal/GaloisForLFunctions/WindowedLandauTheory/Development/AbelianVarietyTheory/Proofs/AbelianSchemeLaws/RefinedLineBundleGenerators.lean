import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalLineBundleCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback

/-! Compatible local generators glue on a refinement of the line-bundle charts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {L : LB X}

/-- A generator of the pullback obeys the pulled-back transition on each overlap. -/
theorem pulledGenerator_compat {Y : Scheme.{0}} {π : Y ⟶ X} {t : (L.pull π).Gen}
    (ht : t.IsGen) {i j : L.ι} {V : Y.Opens} (hi : V ≤ π ⁻¹ᵁ L.U i) (hj : V ≤ π ⁻¹ᵁ L.U j) :
    resG Y (hi.trans (pull_chart L π i).ge) (t.s (fun _ => i)).val =
      π.appLE (L.U i ⊓ L.U j) V (le_inf hi hj) (L.g i j).val *
        resG Y (hj.trans (pull_chart L π j).ge) (t.s (fun _ => j)).val := by
  let P := ChartPull.pull L π
  have ei := hi.trans (pull_chart L π i).ge
  have ej := hj.trans (pull_chart L π j).ge
  have e := congrArg (resG Y (le_inf ei ej))
    (congrArg Units.val (ht (fun _ => i) (fun _ => j)))
  change resG Y _ (resG Y inf_le_left (t.s (fun _ => i)).val) =
    resG Y _ (((L.pull π).g (fun _ => i) (fun _ => j)).val *
      resG Y inf_le_right (t.s (fun _ => j)).val) at e
  simp only [map_mul, resG_resG] at e
  have hg := congrArg Units.val (P.restrict_g ei ej)
  change resG Y _ ((L.pull π).g (fun _ => i) (fun _ => j)).val =
    π.appLE (L.U i ⊓ L.U j) V (le_inf hi hj) (L.g i j).val at hg
  rwa [hg] at e

theorem cocycle_on (hL : L.IsLB) {a b c : L.ι} {V : X.Opens}
    (ha : V ≤ L.U a) (hb : V ≤ L.U b) (hc : V ≤ L.U c) :
    resG X (le_inf ha hb) (L.g a b).val * resG X (le_inf hb hc) (L.g b c).val =
      resG X (le_inf ha hc) (L.g a c).val := by
  have e := congrArg (fun u => resG X (le_inf (le_inf ha hb) hc) (Units.val u)) (hL.cocycle a b c)
  change resG X _ (resG X inf_le_left (L.g a b).val *
      resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (L.g b c).val) =
    resG X _ (resG X (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (L.g a c).val) at e
  simpa only [map_mul, resG_resG] using e

private theorem diag_on (hL : L.IsLB) {a : L.ι} {V : X.Opens} (h : V ≤ L.U a) :
    resG X (le_inf h h) (L.g a a).val = 1 := by
  have e := cocycle_on hL h h h
  exact ((L.g a a).isUnit.map (resG X (le_inf h h))).mul_left_cancel (e.trans (mul_one _).symm)

/-- The unit coordinates on an open refinement determine a global generator. -/
theorem exists_gen_of_refinement (hL : L.IsLB) {I : Type} (W : I → X.Opens)
    (hc : ⨆ i, W i = ⊤) (c : I → L.ι) (hle : ∀ i, W i ≤ L.U (c i))
    (u : ∀ i, Γ(X, W i)) (hu : ∀ i, IsUnit (u i))
    (h : ∀ i j, resG X inf_le_left (u i) =
      resG X (inf_le_inf (hle i) (hle j)) (L.g (c i) (c j)).val * resG X inf_le_right (u j)) :
    ∃ t : L.Gen, t.IsGen := by
  let V (a : L.ι) (i : I) := L.U a ⊓ W i
  let q (a : L.ι) (i : I) : Γ(X, V a i) :=
    resG X (le_inf inf_le_left (inf_le_right.trans (hle i))) (L.g a (c i)).val *
      resG X inf_le_right (u i)
  have hcover (D : X.Opens) : (⨆ i, D ⊓ W i) = D := by rw [← inf_iSup_eq, hc, inf_top_eq]
  have hglue (a : L.ι) : ∃ z : Γ(X, L.U a), ∀ i, resG X (inf_le_left : V a i ≤ L.U a) z =
      q a i := by
    apply exists_fun_of_cover (V a) (fun _ => inf_le_left) (hcover (L.U a)).ge (q a)
    intro i j
    let T := V a i ⊓ V a j
    have ha : T ≤ L.U a := inf_le_left.trans inf_le_left
    have hi : T ≤ W i := inf_le_left.trans inf_le_right
    have hj : T ≤ W j := inf_le_right.trans inf_le_right
    have e := congrArg (resG X (le_inf hi hj)) (h i j)
    simp only [map_mul, resG_resG] at e
    change resG X inf_le_left (q a i) = resG X inf_le_right (q a j)
    dsimp only [q]
    simp only [map_mul, resG_resG]
    rw [e, ← mul_assoc, cocycle_on hL ha (hi.trans (hle i)) (hj.trans (hle j))]
  choose z hz using hglue
  have hcoord (a : L.ι) (i : I) {T : X.Opens} (ha : T ≤ L.U a) (hi : T ≤ W i) :
      resG X ha (z a) = resG X (le_inf ha (hi.trans (hle i))) (L.g a (c i)).val *
        resG X hi (u i) := by
    have e := congrArg (resG X (le_inf ha hi)) (hz a i)
    simpa only [q, map_mul, resG_resG] using e
  have hcomp (a b : L.ι) : resG X inf_le_left (z a) =
      (L.g a b).val * resG X inf_le_right (z b) := by
    refine fun_ext_of_cover (fun i => (L.U a ⊓ L.U b) ⊓ W i)
      (fun _ => inf_le_left) (hcover (L.U a ⊓ L.U b)).ge fun i => ?_
    change resG X inf_le_left (resG X inf_le_left (z a)) =
      resG X inf_le_left ((L.g a b).val * resG X inf_le_right (z b))
    simp only [map_mul, resG_resG]
    have ha : (L.U a ⊓ L.U b) ⊓ W i ≤ L.U a := inf_le_left.trans inf_le_left
    have hb : (L.U a ⊓ L.U b) ⊓ W i ≤ L.U b := inf_le_left.trans inf_le_right
    have hi : (L.U a ⊓ L.U b) ⊓ W i ≤ W i := inf_le_right
    rw [hcoord a i ha hi, hcoord b i hb hi, ← mul_assoc,
      cocycle_on hL ha hb (hi.trans (hle i))]
  let s : L.Sec := ⟨z, hcomp⟩
  refine exists_gen_of_nonvanishing_coordinates (globalCoordinates.symm s) W c hle fun x => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hc.ge (Set.mem_univ x))
  refine ⟨i, ?_⟩
  rw [Equiv.apply_symm_apply]
  change x ∈ X.basicOpen (resG X (hle i) (z (c i)))
  rwa [hcoord (c i) i (hle i) le_rfl, diag_on hL (hle i), one_mul, resG_self,
    X.basicOpen_of_isUnit (hu i)]

end GlobalTheory.LineBundleSections
