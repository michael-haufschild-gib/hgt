import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwistPowers

/-! On an affine trivializing chart, a twisted section extends after clearing one denominator. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M H : LB X} {t d : ℤ}

private theorem exists_regular_lift {W V : X.Opens} (hW : IsAffineOpen W) (u : Γ(X, W))
    (hV : X.basicOpen u = V) (hw : V ≤ W) (a : Γ(X, V)) :
    ∃ (n : ℕ) (c : Γ(X, W)), resG X hw c = resG X hw u ^ n * a := by
  subst V
  exact exists_eq_pow_mul_of_isAffineOpen X W hW u a

theorem exists_affine_lift_mulTwistPower (hM : M.IsLB) (hH : H.IsLB)
    (s : (transitionPower H d).Sec) {W : X.Opens}
    (hW : IsAffineOpen W) (p : M.ι × H.ι) (hp : W ≤ M.U p.1 ⊓ H.U p.2)
    (a : Γ(toMod (twist M H t), nonzeroLocus s ⊓ W)) :
    ∃ n : ℕ, ∀ k ≥ n, ∃ y : Γ(toMod (twist M H (t + k * d)), W),
      (toMod (twist M H (t + k * d))).presheaf.map (homOfLE inf_le_right).op y =
        mulTwistPower M s k t (nonzeroLocus s ⊓ W) a := by
  let V := nonzeroLocus s ⊓ W
  let u : Γ(X, W) := resG X (hp.trans inf_le_right) (powerCoord s p.2)
  let hV : V ≤ W := inf_le_right
  let z := chartEquiv (twist_isLB hM hH t) p (hV.trans hp) a
  have hb : X.basicOpen u = V := basicOpen_coord_restrict s _ _
  obtain ⟨n, c, hc⟩ := exists_regular_lift hW u hb hV z
  refine ⟨n, fun k hk => ?_⟩
  let hL := twist_isLB hM hH (t + k * d)
  refine ⟨(chartEquiv hL p hp).symm (u ^ (k - n) * c), (chartEquiv hL p (hV.trans hp)).injective ?_⟩
  rw [chartEquiv_map hL p hp hV, LinearEquiv.apply_symm_apply,
    chartEquiv_mulTwistPower hM hH s k t p (hV.trans hp)]
  change resG X hV (u ^ (k - n) * c) =
    resG X ((hV.trans hp).trans inf_le_right) (powerCoord s p.2) ^ k * z
  rw [map_mul, map_pow, hc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  dsimp only [u]
  rw [resG_resG]

end GlobalTheory.LineBundleSections
