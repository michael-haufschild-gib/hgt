import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwists

/-! At degree zero, the twist merely refines the original line-bundle cover. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M H : LB X} {V W : X.Opens}

private def zeroTwistRefine (M H : LB X) (V : X.Opens) :
    Γ(toMod M, V) →ₗ[Γ(X, V)] Γ(toMod (twist M H 0), V) where
  toFun s := mkTwistSection 0
    (fun p => resG X (inf_le_inf_left V inf_le_left) (coord s p.1))
    (fun p q _ hp hq => by
      rw [resG_resG, resG_resG, zpow_zero, mul_one]
      exact coord_rel s p.1 q.1 _ _ _)
  map_add' s t := sec_ext fun _ => map_add _ _ _
  map_smul' r s := sec_ext fun p => by
    let T := V ⊓ (M.U p.1 ⊓ H.U p.2)
    let h₁ : T ≤ V ⊓ M.U p.1 := inf_le_inf_left V inf_le_left
    let h₂ : T ≤ V := inf_le_left
    change resG X h₁ (resG X (inf_le_left : V ⊓ M.U p.1 ≤ V) r * coord s p.1) =
      resG X h₂ r * resG X h₁ (coord s p.1)
    rw [map_mul, resG_resG]

private theorem zeroTwistRefine_bijective (hM : M.IsLB) (hH : H.IsLB) :
    Function.Bijective (zeroTwistRefine M H V) := by
  have cover (U : X.Opens) : (⨆ i, U ⊓ H.U i) = U := by rw [← inf_iSup_eq, hH.cover, inf_top_eq]
  constructor
  · intro a b e
    refine sec_ext fun p => fun_ext_of_cover (fun i => V ⊓ M.U p ⊓ H.U i)
      (fun _ => inf_le_left) (cover (V ⊓ M.U p)).ge fun i => ?_
    let h : V ⊓ M.U p ⊓ H.U i ≤ V ⊓ (M.U p ⊓ H.U i) :=
      le_inf (inf_le_left.trans inf_le_left) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    have eq := congrArg (fun s : Γ(toMod (twist M H 0), V) => resG X h (twistCoord s (p, i))) e
    let h' : V ⊓ (M.U p ⊓ H.U i) ≤ V ⊓ M.U p := inf_le_inf_left V inf_le_left
    change resG X h (resG X h' (coord a p)) = resG X h (resG X h' (coord b p)) at eq
    simpa only [resG_resG] using eq
  · intro a
    let W (p : M.ι) (i : H.ι) := V ⊓ M.U p ⊓ H.U i
    let h (p : M.ι) (i : H.ι) : W p i ≤ V ⊓ (M.U p ⊓ H.U i) :=
      le_inf (inf_le_left.trans inf_le_left) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    have lift (p : M.ι) : ∃ z : Γ(X, V ⊓ M.U p), ∀ i,
        resG X (inf_le_left : W p i ≤ V ⊓ M.U p) z = resG X (h p i) (twistCoord a (p, i)) := by
      refine exists_fun_of_cover (W p) (fun _ => inf_le_left) (cover (V ⊓ M.U p)).ge _ fun i j => ?_
      rw [resG_resG, resG_resG]
      have ep := twistCoord_rel a (p, i) (p, j) (inf_le_left.trans (h p i)) (inf_le_right.trans (h p j))
      have e := congrArg (res (inf_le_left.trans (inf_le_left.trans inf_le_right) :
        W p i ⊓ W p j ≤ M.U p)) (hM.g_self p)
      rw [map_one, res_res] at e
      rw [zpow_zero, mul_one, e, Units.val_one, one_mul] at ep
      exact ep
    choose z hz using lift
    have chart_eq (p : M.ι) (i : H.ι) {U : X.Opens}
        (hp : U ≤ V ⊓ M.U p) (hi : U ≤ H.U i) :
        resG X hp (z p) =
          resG X (le_inf (hp.trans inf_le_left) (le_inf (hp.trans inf_le_right) hi))
            (twistCoord a (p, i)) := by
      have e := congrArg (resG X (le_inf hp hi)) (hz p i)
      simpa only [resG_resG] using e
    let b := mkSec (L := M) z fun p q => by
      let U := V ⊓ M.U p ⊓ M.U q
      refine fun_ext_of_cover (fun i : H.ι => U ⊓ H.U i) (fun _ => inf_le_left) (cover U).ge fun i => ?_
      let hp : U ⊓ H.U i ≤ V ⊓ M.U p := inf_le_left.trans inf_le_left
      let hq : U ⊓ H.U i ≤ V ⊓ M.U q := le_inf
        (inf_le_left.trans (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)
      rw [map_mul, resG_resG, resG_resG, resG_resG, chart_eq p i hp inf_le_right,
        chart_eq q i hq inf_le_right]
      have e := twistCoord_rel a (p, i) (q, i)
        (le_inf (hp.trans inf_le_left) (le_inf (hp.trans inf_le_right) inf_le_right))
        (le_inf (hq.trans inf_le_left) (le_inf (hq.trans inf_le_right) inf_le_right))
      rw [zpow_zero, mul_one] at e
      exact e
    refine ⟨b, sec_ext fun p => ?_⟩
    change resG X (inf_le_inf_left V inf_le_left) (z p.1) = twistCoord a p
    exact (chart_eq p.1 p.2 (inf_le_inf_left V inf_le_left) (inf_le_right.trans inf_le_right)).trans
      (resG_self _ _)

def zeroTwistEquiv (hM : M.IsLB) (hH : H.IsLB) :
    Γ(toMod M, V) ≃ₗ[Γ(X, V)] Γ(toMod (twist M H 0), V) :=
  LinearEquiv.ofBijective _ (zeroTwistRefine_bijective hM hH)

theorem zeroTwistEquiv_restrict (hM : M.IsLB) (hH : H.IsLB) (h : W ≤ V)
    (a : Γ(toMod M, V)) :
    zeroTwistEquiv hM hH ((toMod M).presheaf.map (homOfLE h).op a) =
      (toMod (twist M H 0)).presheaf.map (homOfLE h).op (zeroTwistEquiv hM hH a) := by
  refine sec_ext fun p => ?_
  change resG X (inf_le_inf_left W inf_le_left)
      (resG X (inf_le_inf_right (M.U p.1) h) (coord a p.1)) =
    resG X (inf_le_inf_right (M.U p.1 ⊓ H.U p.2) h)
      (resG X (inf_le_inf_left V inf_le_left) (coord a p.1))
  rw [resG_resG, resG_resG]

end GlobalTheory.LineBundleSections
