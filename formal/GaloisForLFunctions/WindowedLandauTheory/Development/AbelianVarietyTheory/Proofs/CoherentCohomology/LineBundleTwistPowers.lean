import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundlePowerProducts

/-! Multiplication by powers of a section of `H^d` shifts the twist by multiples of `d`. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M H : LB X} {V W : X.Opens} {d : ℤ}

/-- The local coefficient of a power section in a chart of the underlying bundle. -/
def powerCoord (s : (transitionPower H d).Sec) (i : H.ι) : Γ(X, H.U i) :=
  s.f i

theorem twist_shift_transition {A : Type*} [CommRing A] (c g : Aˣ) (t d : ℤ) (k : ℕ)
    {u v : A} (h : u = (g ^ d).val * v) :
    (c * g ^ (t + k * d)).val * v ^ k = u ^ k * (c * g ^ t).val := by
  rw [h, zpow_add, mul_comm (k : ℤ) d, zpow_mul, zpow_natCast]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow]
  ring

def mulTwistPower (M : LB X) (s : (transitionPower H d).Sec) (k : ℕ) (t : ℤ) (V : X.Opens) :
    Γ(toMod (twist M H t), V) →ₗ[Γ(X, V)] Γ(toMod (twist M H (t + k * d)), V) where
  toFun x := mkTwistSection (t + k * d)
    (fun p => resG X (inf_le_right.trans inf_le_right) (powerCoord s p.2) ^ k * twistCoord x p)
    (fun p q _ hp hq => by
      rw [map_mul, map_mul, map_pow, map_pow, resG_resG, resG_resG, twistCoord_rel x p q hp hq,
        ← mul_assoc, ← mul_assoc]
      exact congrArg (· * resG X hq (twistCoord x q)) (twist_shift_transition _ _ t d k
        (powerSec_rel s p.2 q.2 ((hp.trans inf_le_right).trans inf_le_right)
          ((hq.trans inf_le_right).trans inf_le_right))).symm)
  map_add' x y := sec_ext fun p => by
    change _ * (twistCoord x p + twistCoord y p) =
      _ * twistCoord x p + _ * twistCoord y p
    exact mul_add _ _ _
  map_smul' a x := sec_ext fun p => by
    simp only [RingHom.id_apply, twistCoord_mkTwistSection, coord_smul]
    exact mul_left_comm _ _ _

@[simp]
theorem twistCoord_mulTwistPower (s : (transitionPower H d).Sec) (k : ℕ) (t : ℤ)
    (x : Γ(toMod (twist M H t), V)) (p : M.ι × H.ι) :
    twistCoord (mulTwistPower M s k t V x) p =
      resG X (inf_le_right.trans inf_le_right) (powerCoord s p.2) ^ k * twistCoord x p := rfl

theorem chartEquiv_mulTwistPower (hM : M.IsLB) (hH : H.IsLB)
    (s : (transitionPower H d).Sec) (k : ℕ) (t : ℤ) (p : M.ι × H.ι)
    (hp : V ≤ M.U p.1 ⊓ H.U p.2) (x : Γ(toMod (twist M H t), V)) :
    chartEquiv (twist_isLB hM hH (t + k * d)) p hp (mulTwistPower M s k t V x) =
      resG X (hp.trans inf_le_right) (powerCoord s p.2) ^ k *
        chartEquiv (twist_isLB hM hH t) p hp x := by
  change resG X (le_inf le_rfl hp) (twistCoord (mulTwistPower M s k t V x) p) =
    resG X (hp.trans inf_le_right) (powerCoord s p.2) ^ k * resG X (le_inf le_rfl hp) (twistCoord x p)
  rw [twistCoord_mulTwistPower, map_mul, map_pow, resG_resG]

theorem mulTwistPower_restrict (s : (transitionPower H d).Sec) (k : ℕ) (t : ℤ)
    (h : W ≤ V) (x : Γ(toMod (twist M H t), V)) :
    mulTwistPower M s k t W ((toMod (twist M H t)).presheaf.map (homOfLE h).op x) =
      (toMod (twist M H (t + k * d))).presheaf.map (homOfLE h).op (mulTwistPower M s k t V x) := by
  apply sec_ext
  intro p
  let P := M.U p.1 ⊓ H.U p.2
  change resG X (inf_le_right.trans inf_le_right : W ⊓ P ≤ H.U p.2) (powerCoord s p.2) ^ k *
      resG X (inf_le_inf_right P h) (twistCoord x p) =
    resG X (inf_le_inf_right P h)
      (resG X (inf_le_right.trans inf_le_right : V ⊓ P ≤ H.U p.2) (powerCoord s p.2) ^ k * twistCoord x p)
  rw [map_mul, map_pow, resG_resG]

end GlobalTheory.LineBundleSections
