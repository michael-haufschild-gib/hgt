import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwistPowers
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwistDivision

/-! Multiplication by a power of a nonvanishing section is a linear equivalence. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M H : LB X} {V : X.Opens} {t d : ℤ}

theorem mulTwistPower_bijective (s : (transitionPower H d).Sec) (h : V ≤ nonzeroLocus s) (k : ℕ) :
    Function.Bijective (mulTwistPower M s k t V) := by
  let U (p : M.ι × H.ι) := V ⊓ (M.U p.1 ⊓ H.U p.2)
  let u (p : M.ι × H.ι) : Γ(X, U p)ˣ :=
    coordUnit s p.2 (inf_le_right.trans inf_le_right) (inf_le_left.trans h)
  have hu (p : M.ι × H.ι) : (u p ^ k).val =
      resG X (inf_le_right.trans inf_le_right : U p ≤ H.U p.2) (powerCoord s p.2) ^ k := by
    simp only [u, Units.val_pow_eq_pow_val, coordUnit_val, powerCoord]
    rfl
  constructor
  · intro a b he
    refine sec_ext fun p => (Units.isUnit (u p ^ k)).mul_left_cancel ?_
    have e := congrArg (fun x : Γ(toMod (twist M H (t + k * d)), V) =>
      (twistCoord x p : Γ(X, U p))) he
    rw [twistCoord_mulTwistPower, twistCoord_mulTwistPower] at e
    change (u p ^ k).val * (twistCoord a p : Γ(X, U p)) =
      (u p ^ k).val * (twistCoord b p : Γ(X, U p))
    rw [hu]
    exact e
  · intro a
    let z (p : M.ι × H.ι) : Γ(X, U p) := ((u p ^ k)⁻¹).val * (twistCoord a p : Γ(X, U p))
    have hz (p : M.ι × H.ι) :
        resG X (inf_le_right.trans inf_le_right : U p ≤ H.U p.2) (powerCoord s p.2) ^ k * z p = twistCoord a p := by
      rw [← hu]
      change (u p ^ k).val * (((u p ^ k)⁻¹).val * (twistCoord a p : Γ(X, U p))) = _
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    have hres (p : M.ι × H.ι) {W : X.Opens} (hW : W ≤ U p) :
        resG X hW (twistCoord a p) =
          resG X (hW.trans (inf_le_right.trans inf_le_right)) (powerCoord s p.2) ^ k *
            resG X hW (z p) := by
      let vp : Γ(X, U p) :=
        resG X (inf_le_right.trans inf_le_right : U p ≤ H.U p.2) (powerCoord s p.2)
      calc
        resG X hW (twistCoord a p) = resG X hW (vp ^ k * z p) :=
          congrArg (resG X hW) (hz p).symm
        _ = resG X hW vp ^ k * resG X hW (z p) := by rw [map_mul, map_pow]
        _ = _ := by
          dsimp only [vp]
          rw [resG_resG]
    have hcompat (p q : M.ι × H.ι) {W : X.Opens} (hp : W ≤ U p) (hq : W ≤ U q) :
        resG X hp (z p) =
          (res (le_inf ((hp.trans inf_le_right).trans inf_le_left)
              ((hq.trans inf_le_right).trans inf_le_left)) (M.g p.1 q.1) *
            res (le_inf ((hp.trans inf_le_right).trans inf_le_right)
              ((hq.trans inf_le_right).trans inf_le_right)) (H.g p.2 q.2) ^ t).val *
            resG X hq (z q) := by
      let hp' : W ≤ H.U p.2 := (hp.trans inf_le_right).trans inf_le_right
      let hq' : W ≤ H.U q.2 := (hq.trans inf_le_right).trans inf_le_right
      let c : Γ(X, W)ˣ := res
        (le_inf ((hp.trans inf_le_right).trans inf_le_left) ((hq.trans inf_le_right).trans inf_le_left))
        (M.g p.1 q.1)
      let g : Γ(X, W)ˣ := res (le_inf hp' hq') (H.g p.2 q.2)
      let vp : Γ(X, W) := resG X hp' (powerCoord s p.2)
      let vq : Γ(X, W) := resG X hq' (powerCoord s q.2)
      have hshift : (c * g ^ (t + k * d)).val * vq ^ k = vp ^ k * (c * g ^ t).val :=
        twist_shift_transition c g t d k (powerSec_rel s p.2 q.2 hp' hq')
      have e := twistCoord_rel a p q hp hq
      rw [hres p hp, hres q hq] at e
      apply ((isUnit_coord_of_le_nonzeroLocus s p.2 hp' (hp.trans (inf_le_left.trans h))).pow k).mul_left_cancel
      exact e.trans ((mul_assoc (c * g ^ (t + k * d)).val (vq ^ k) (resG X hq (z q))).symm.trans
        ((congrArg (fun b : Γ(X, W) => b * resG X hq (z q)) hshift).trans (mul_assoc _ _ _)))
    refine ⟨mkTwistSection t z hcompat, sec_ext fun p => ?_⟩
    change twistCoord (mulTwistPower M s k t V (mkTwistSection t z hcompat)) p = twistCoord a p
    rw [twistCoord_mulTwistPower, twistCoord_mkTwistSection]
    exact hz p

end GlobalTheory.LineBundleSections
