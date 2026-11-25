import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionCharts

/-! Integral twists of a line bundle, on the common refinement of its two covers. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M H : LB X}

/-- The integer power of a line bundle on its original cover. -/
def transitionPower (H : LB X) (t : ℤ) : LB X :=
  ⟨H.ι, H.U, fun i j => H.g i j ^ t⟩

/-- The bundle `M ⊗ H^t` in local trivializations. -/
def twist (M H : LB X) (t : ℤ) : LB X :=
  M.div (transitionPower H (-t))

theorem res_twist_g (t : ℤ) (p q : M.ι × H.ι) {W : X.Opens}
    (hp : W ≤ M.U p.1 ⊓ H.U p.2) (hq : W ≤ M.U q.1 ⊓ H.U q.2) :
    res (le_inf hp hq) ((twist M H t).g p q) =
      res (le_inf (hp.trans inf_le_left) (hq.trans inf_le_left)) (M.g p.1 q.1) *
        res (le_inf (hp.trans inf_le_right) (hq.trans inf_le_right)) (H.g p.2 q.2) ^ t := by
  refine (LB.res_div_g (transitionPower H (-t)) M (i := p) (j := q) hp hq).trans ?_
  change res (le_inf (hp.trans inf_le_left) (hq.trans inf_le_left)) (M.g p.1 q.1) *
      (res (le_inf (hp.trans inf_le_right) (hq.trans inf_le_right)) (H.g p.2 q.2 ^ (-t)))⁻¹ = _
  rw [map_zpow, zpow_neg, inv_inv]

private theorem unit_cocycle {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (hi : W ≤ L.U i) (hj : W ≤ L.U j) (hk : W ≤ L.U k) :
    res (le_inf hi hj) (L.g i j) * res (le_inf hj hk) (L.g j k) =
      res (le_inf hi hk) (L.g i k) := by
  have h := congrArg (res (le_inf (le_inf hi hj) hk)) (hL.cocycle i j k)
  simpa only [map_mul, res_res] using h

private theorem unit_self {L : LB X} (hL : L.IsLB) (i : L.ι) {W : X.Opens}
    (hi : W ≤ L.U i) : res (le_inf hi hi) (L.g i i) = 1 :=
  (res_res _ hi _).symm.trans ((congrArg (res hi) (hL.g_self i)).trans (map_one _))

theorem twist_isLB (hM : M.IsLB) (hH : H.IsLB) (t : ℤ) : (twist M H t).IsLB where
  cover := by
    change (⨆ p : M.ι × H.ι, M.U p.1 ⊓ H.U p.2) = ⊤
    rw [iSup_prod]
    simp only [← inf_iSup_eq, hH.cover, inf_top_eq, hM.cover]
  g_self p := by
    let W := M.U p.1 ⊓ H.U p.2
    change res (le_inf (le_rfl : W ≤ W) le_rfl) ((twist M H t).g p p) = (1 : Γ(X, W)ˣ)
    have h := res_twist_g (M := M) (H := H) t p p (W := W) le_rfl le_rfl
    have hm := unit_self hM p.1 (inf_le_left : W ≤ M.U p.1)
    have hh := unit_self hH p.2 (inf_le_right : W ≤ H.U p.2)
    have h₁ : (1 : Γ(X, W)ˣ) * 1 ^ t = 1 := by rw [one_zpow, mul_one]
    exact h.trans ((congrArg₂ (fun a b : Γ(X, W)ˣ => a * b) hm
      (congrArg (fun a : Γ(X, W)ˣ => a ^ t) hh)).trans h₁)
  cocycle p q r := by
    let V := (twist M H t).U p ⊓ (twist M H t).U q ⊓ (twist M H t).U r
    have hp : V ≤ M.U p.1 ⊓ H.U p.2 := inf_le_left.trans inf_le_left
    have hq : V ≤ M.U q.1 ⊓ H.U q.2 := inf_le_left.trans inf_le_right
    have hr : V ≤ M.U r.1 ⊓ H.U r.2 := inf_le_right
    have e₁ := res_twist_g (M := M) (H := H) t p q hp hq
    have e₂ := res_twist_g (M := M) (H := H) t q r hq hr
    have e₃ := res_twist_g (M := M) (H := H) t p r hp hr
    refine (congrArg₂ (· * ·) e₁ e₂).trans (Eq.trans ?_ e₃.symm)
    rw [mul_mul_mul_comm, ← mul_zpow]
    exact congrArg₂ (· * ·)
      (unit_cocycle hM p.1 q.1 r.1 (hp.trans inf_le_left) (hq.trans inf_le_left) (hr.trans inf_le_left))
      (congrArg (· ^ t) (unit_cocycle hH p.2 q.2 r.2
        (hp.trans inf_le_right) (hq.trans inf_le_right) (hr.trans inf_le_right)))

variable {V : X.Opens} {t : ℤ}

abbrev twistCoord (s : Γ(toMod (twist M H t), V)) (p : M.ι × H.ι) :
    Γ(X, V ⊓ (M.U p.1 ⊓ H.U p.2)) := coord s p

theorem twistCoord_rel (s : Γ(toMod (twist M H t), V)) (p q : M.ι × H.ι) {W : X.Opens}
    (hp : W ≤ V ⊓ (M.U p.1 ⊓ H.U p.2)) (hq : W ≤ V ⊓ (M.U q.1 ⊓ H.U q.2)) :
    resG X hp (twistCoord s p) =
      (res (le_inf ((hp.trans inf_le_right).trans inf_le_left)
          ((hq.trans inf_le_right).trans inf_le_left)) (M.g p.1 q.1) *
        res (le_inf ((hp.trans inf_le_right).trans inf_le_right)
          ((hq.trans inf_le_right).trans inf_le_right)) (H.g p.2 q.2) ^ t).val *
        resG X hq (twistCoord s q) :=
  (coord_rel s p q hp hq (le_inf (hp.trans inf_le_right) (hq.trans inf_le_right))).trans
    (congrArg (fun u : Γ(X, W)ˣ => u.val * resG X hq (twistCoord s q))
      (res_twist_g (M := M) (H := H) t p q (hp.trans inf_le_right) (hq.trans inf_le_right)))

def mkTwistSection (t : ℤ)
    (a : ∀ p : M.ι × H.ι, Γ(X, V ⊓ (M.U p.1 ⊓ H.U p.2)))
    (ha : ∀ (p q : M.ι × H.ι) {W : X.Opens}
      (hp : W ≤ V ⊓ (M.U p.1 ⊓ H.U p.2)) (hq : W ≤ V ⊓ (M.U q.1 ⊓ H.U q.2)),
      resG X hp (a p) =
        (res (le_inf ((hp.trans inf_le_right).trans inf_le_left)
            ((hq.trans inf_le_right).trans inf_le_left)) (M.g p.1 q.1) *
          res (le_inf ((hp.trans inf_le_right).trans inf_le_right)
            ((hq.trans inf_le_right).trans inf_le_right)) (H.g p.2 q.2) ^ t).val *
          resG X hq (a q)) : Γ(toMod (twist M H t), V) :=
  mkSec (L := twist M H t) a fun p q =>
    (ha p q inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).trans
      (congrArg (fun u => u.val * resG X
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (a q))
        (res_twist_g (M := M) (H := H) t p q (inf_le_left.trans inf_le_right) inf_le_right).symm)

@[simp]
theorem twistCoord_mkTwistSection (a : ∀ p : M.ι × H.ι, Γ(X, V ⊓ (M.U p.1 ⊓ H.U p.2)))
    (ha) (p : M.ι × H.ι) : twistCoord (mkTwistSection t a ha) p = a p := rfl

end GlobalTheory.LineBundleSections
