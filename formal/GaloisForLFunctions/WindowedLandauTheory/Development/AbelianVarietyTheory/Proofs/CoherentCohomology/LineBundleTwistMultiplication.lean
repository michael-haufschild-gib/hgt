import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwists

/-! Multiplying by a section of `H` raises the degree of sections of `M ⊗ H^t`. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M H : LB X} {V W : X.Opens} {t : ℤ}

theorem globalSec_rel (s : H.Sec) (i j : H.ι) (hi : W ≤ H.U i) (hj : W ≤ H.U j) :
    resG X hi (s.f i) =
      (res (le_inf hi hj) (H.g i j)).val * resG X hj (s.f j) := by
  have h := congrArg (resG X (le_inf hi hj)) (s.compat i j)
  have e : resG X hi (s.f i) =
      resG X (le_inf hi hj) (H.g i j).val * resG X hj (s.f j) := by
    simpa only [map_mul, resG_resG] using h
  exact e

/-- Multiply in the common refinement of the two bundles' covers. -/
def mulTwistSection (M : LB X) (t : ℤ) (s : H.Sec) (V : X.Opens) :
    Γ(toMod (twist M H t), V) →ₗ[Γ(X, V)] Γ(toMod (twist M H (t + 1)), V) where
  toFun x := mkTwistSection (t + 1)
    (fun p => resG X (inf_le_right.trans inf_le_right) (s.f p.2) * twistCoord x p)
    (fun p q _ hp hq => by
      rw [map_mul, map_mul, resG_resG, resG_resG, twistCoord_rel x p q hp hq,
        globalSec_rel s p.2 q.2 ((hp.trans inf_le_right).trans inf_le_right)
          ((hq.trans inf_le_right).trans inf_le_right), zpow_add_one]
      simp only [Units.val_mul]
      ring)
  map_add' x y := sec_ext fun p => by
    change _ * (twistCoord x p + twistCoord y p) =
      _ * twistCoord x p + _ * twistCoord y p
    exact mul_add _ _ _
  map_smul' a x := sec_ext fun p => by
    simp only [RingHom.id_apply, twistCoord_mkTwistSection, coord_smul]
    exact mul_left_comm _ _ _

@[simp]
theorem twistCoord_mulTwistSection (s : H.Sec) (x : Γ(toMod (twist M H t), V))
    (p : M.ι × H.ι) :
    twistCoord (mulTwistSection M t s V x) p =
      resG X (inf_le_right.trans inf_le_right) (s.f p.2) * twistCoord x p := rfl

theorem mulTwistSection_restrict (s : H.Sec) (h : W ≤ V) (x : Γ(toMod (twist M H t), V)) :
    mulTwistSection M t s W ((toMod (twist M H t)).presheaf.map (homOfLE h).op x) =
      (toMod (twist M H (t + 1))).presheaf.map (homOfLE h).op (mulTwistSection M t s V x) := by
  apply sec_ext
  intro p
  let P := M.U p.1 ⊓ H.U p.2
  change resG X (inf_le_right.trans inf_le_right : W ⊓ P ≤ H.U p.2) (s.f p.2) *
      resG X (inf_le_inf_right P h) (twistCoord x p) =
    resG X (inf_le_inf_right P h)
      (resG X (inf_le_right.trans inf_le_right : V ⊓ P ≤ H.U p.2) (s.f p.2) * twistCoord x p)
  rw [map_mul, resG_resG]

theorem mulTwistSection_comm (s r : H.Sec) (x : Γ(toMod (twist M H t), V)) :
    mulTwistSection M (t + 1) s V (mulTwistSection M t r V x) =
      mulTwistSection M (t + 1) r V (mulTwistSection M t s V x) :=
  sec_ext fun _ => mul_left_comm _ _ _

theorem mulTwistSection_eq_smul (s r : H.Sec) (a : Γ(X, V))
    (ha : ∀ k, resG X (inf_le_right : V ⊓ H.U k ≤ H.U k) (r.f k) =
      resG X inf_le_left a * resG X inf_le_right (s.f k))
    (x : Γ(toMod (twist M H t), V)) :
    mulTwistSection M t r V x = a • mulTwistSection M t s V x := by
  apply sec_ext
  intro p
  have e := congrArg (resG X (inf_le_inf_left V inf_le_right :
    V ⊓ (M.U p.1 ⊓ H.U p.2) ≤ V ⊓ H.U p.2)) (ha p.2)
  simp only [map_mul, resG_resG] at e
  change twistCoord (mulTwistSection M t r V x) p = coord (a • mulTwistSection M t s V x) p
  rw [coord_smul, twistCoord_mulTwistSection]
  change _ = _ * twistCoord (mulTwistSection M t s V x) p
  rw [twistCoord_mulTwistSection, e, mul_assoc]
  rfl

end GlobalTheory.LineBundleSections
