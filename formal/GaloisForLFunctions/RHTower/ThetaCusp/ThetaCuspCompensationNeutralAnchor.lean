import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspModularBarrierGain
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterCompensationSign
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleCompensationBounds

/-!
# Source-neutral center: sharp location and transverse crossing

The literal complete theta compensation source has a unique neutral center.
Its first-atom scale lies strictly between `5` and `45/8`. The crossing is
quantitatively transverse, using strict log-concavity of the complete source.
These are source-side boundary facts; they do not sign the rank-eight odd Schur
coordinate.
-/

open Set
namespace RHTower
noncomputable section

private theorem q_quarter_lt_fortyFiveEighths :
    thetaCuspSingleAtomReflectionScale 1 (1/4 : ℝ) < 45/8 := by
  have hpi : Real.pi < 63/20 := by linarith only [Real.pi_lt_d2]
  have he : Real.exp (1/2 : ℝ) ^ (2 : ℕ) = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have he1 : Real.exp (1 : ℝ) < 3 := Real.exp_one_lt_three
  have he2 : Real.exp (1/2 : ℝ) < 7/4 := by
    have hepos := Real.exp_pos (1/2 : ℝ)
    nlinarith only [he, he1, hepos]
  have hmul := mul_lt_mul_of_pos_right hpi (Real.exp_pos (1/2 : ℝ))
  dsimp [thetaCuspSingleAtomReflectionScale]
  norm_num
  nlinarith only [hmul, he2, Real.pi_pos]

private theorem quarter_lt_of_fortyFiveEighths_le {x : ℝ}
    (hq : 45/8 ≤ thetaCuspSingleAtomReflectionScale 1 x) : (1/4 : ℝ) < x := by
  by_contra h
  have hx : x ≤ 1/4 := le_of_not_gt h
  have he := Real.exp_le_exp.mpr (show 2*x ≤ (1/2 : ℝ) by linarith)
  have hp := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hq4 := q_quarter_lt_fortyFiveEighths
  dsimp [thetaCuspSingleAtomReflectionScale] at hq hq4
  norm_num at hp hq hq4
  nlinarith only [hp, hq, hq4]

theorem thetaCuspCenterCompensationSource_neg_of_fortyFiveEighths_le {x : ℝ}
    (hq : 45/8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspCenterCompensationSource x < 0 := by
  have hx := quarter_lt_of_fortyFiveEighths_le hq
  have hF := thetaCuspFullSource_pos_all x
  have hder :=
    ThetaCuspModularRatio.thetaCuspFullSource_slope_le_neg_six_of_fortyFiveEighths_le hq
  have hm := mul_le_mul_of_nonneg_left hder
    (show 0 ≤ 2*x*thetaCuspFullSource x by positivity)
  have hreserve : 0 < (12*x-3)*thetaCuspFullSource x^(2 : ℕ) := by
    have hc : 0 < 12*x-3 := by linarith only [hx]
    positivity
  unfold thetaCuspCenterCompensationSource
  nlinarith only [hm, hreserve]

private def xFive : ℝ := Real.log (5/Real.pi)/2

private theorem xFive_pos : 0 < xFive := by
  have hp := Real.pi_pos
  have hpi := Real.pi_lt_four
  have hratio : 1 < (5 : ℝ)/Real.pi := (one_lt_div hp).mpr (by linarith only [hpi])
  dsimp [xFive]
  have hlog := Real.log_pos hratio
  linarith only [hlog]

private theorem q_xFive : thetaCuspSingleAtomReflectionScale 1 xFive = 5 := by
  have hp := Real.pi_pos
  have hratio : 0 < (5 : ℝ)/Real.pi := by positivity
  dsimp [thetaCuspSingleAtomReflectionScale, xFive]
  rw [show 2 * (Real.log (5 / Real.pi) / 2) = Real.log (5 / Real.pi) by ring,
    Real.exp_log hratio]
  norm_num
  field_simp [hp.ne']

theorem exists_thetaCuspCompensationNeutralAnchor :
    ∃ τ : ℝ, 0 < τ ∧
      5 < thetaCuspSingleAtomReflectionScale 1 τ ∧
      thetaCuspSingleAtomReflectionScale 1 τ < 45/8 ∧
      (∀ x : ℝ, 0 ≤ x →
        (0 < thetaCuspCenterCompensationSource x ↔ x < τ) ∧
        (thetaCuspCenterCompensationSource x = 0 ↔ x = τ) ∧
        (thetaCuspCenterCompensationSource x < 0 ↔ τ < x)) := by
  obtain ⟨τ, hτ, hs⟩ := exists_thetaCuspCenterCompensationSource_transition
  have hs5 : 0 < thetaCuspCenterCompensationSource xFive := by
    apply thetaCuspCenterCompensationSource_pos_on_scale_five
    · rw [q_xFive]; norm_num
    · rw [q_xFive]
  have hτ5 : xFive < τ := (hs xFive xFive_pos.le).1.mp hs5
  have hq5 : 5 < thetaCuspSingleAtomReflectionScale 1 τ := by
    rw [← q_xFive]
    dsimp [thetaCuspSingleAtomReflectionScale]
    have he := Real.exp_lt_exp.mpr (show 2*xFive < 2*τ by linarith only [hτ5])
    simpa using mul_lt_mul_of_pos_left he Real.pi_pos
  have hqUpper : thetaCuspSingleAtomReflectionScale 1 τ < 45/8 := by
    by_contra h
    have hneg := thetaCuspCenterCompensationSource_neg_of_fortyFiveEighths_le (x := τ) (le_of_not_gt h)
    have hz := (hs τ hτ.le).2.1.mpr rfl
    linarith
  exact ⟨τ, hτ, hq5, hqUpper, hs⟩


theorem thetaCuspCenterCompensationSource_zero_transverse {x : ℝ} (hx : 0 < x)
    (hz : thetaCuspCenterCompensationSource x = 0) :
    x * deriv thetaCuspCenterCompensationSource x <
      -3 * thetaCuspFullSource x ^ (2 : ℕ) := by
  let F := thetaCuspFullSource
  let L := thetaCuspLogSource
  let S := thetaCuspCenterCompensationSign
  have hFpos : 0 < F x := thetaCuspFullSource_pos_all x
  have hF2 : 0 < F x ^ (2 : ℕ) := by positivity
  have hS0 : S x = 0 := by
    rw [thetaCuspCenterCompensationSource_eq_sign] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hFpos.ne')
  have hL2 : iteratedDeriv 2 L x < 0 := by
    rw [iteratedDeriv_two_thetaCuspLogSource_eq]
    exact div_neg_of_neg_of_pos (thetaCuspLogConcavityNumerator_neg_all x) hF2
  have hD : HasDerivAt (deriv L) (iteratedDeriv 2 L x) x := by
    simpa only [Nat.reduceAdd, iteratedDeriv_one] using
      (hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x)
  have hS : HasDerivAt S (2 * deriv L x + 2*x*iteratedDeriv 2 L x) x := by
    convert (hasDerivAt_const x (3 : ℝ)).add
      (((hasDerivAt_id x).const_mul 2).mul hD) using 1 <;>
      first
      | rfl
      | (simp only [id_eq]; ring)
  have hF : HasDerivAt F (deriv F x) x := by
    simpa only [iteratedDeriv_one] using hasDerivAt_thetaCuspFullSource_iterate_zero x
  have hG : HasDerivAt (fun y => F y ^ (2 : ℕ) * S y)
      ((2*F x*deriv F x)*S x + F x ^ (2 : ℕ)*(2*deriv L x+2*x*iteratedDeriv 2 L x)) x := by
    convert (hF.pow 2).mul hS using 1 <;>
      first
      | rfl
      | (simp only [Pi.pow_apply]; ring)
  have heq : thetaCuspCenterCompensationSource =
      (fun y => F y ^ (2 : ℕ) * S y) := by
    funext y
    exact thetaCuspCenterCompensationSource_eq_sign y
  have hG_eq : deriv thetaCuspCenterCompensationSource x =
      F x ^ (2 : ℕ)*(2*deriv L x+2*x*iteratedDeriv 2 L x) := by
    rw [heq]
    simpa only [hS0, mul_zero, zero_add] using hG.deriv
  have hL2term : 2*x*x*iteratedDeriv 2 L x < 0 := by
    exact mul_neg_of_pos_of_neg (by positivity) hL2
  have hcross : x*(2*deriv L x+2*x*iteratedDeriv 2 L x) < -3 := by
    dsimp [S, thetaCuspCenterCompensationSign] at hS0
    nlinarith only [hS0, hL2term]
  have hbound := mul_lt_mul_of_pos_left hcross hF2
  rw [hG_eq]
  nlinarith only [hbound]


end
end RHTower
