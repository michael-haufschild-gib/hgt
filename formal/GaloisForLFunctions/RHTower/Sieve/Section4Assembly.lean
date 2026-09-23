import GaloisForLFunctions.RHTower.Sieve.Section4ExceptionalCofactor
import GaloisForLFunctions.RHTower.Sieve.JointLadderHarmonic
import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare

/-!
# Assembling exposé §4 over the short ladder

The jointly weighted polynomial is the short ladder of products minus its defect
(`Sieve/JointLadderProduct`); the harmonic Cauchy–Schwarz splits the ladder into its steps
(`Sieve/JointLadderHarmonic`); each step is estimated by `Sieve/Section4BlockFull`.  This module
carries out the composition, leaving the per-step bound as a parameter.

It also records the mean value theorem (Lemma 2.4) at a general coefficient bound, which is what the
non-exceptional half of each step needs: the long-weighted cofactor is bounded by `#Q`, not by `1`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Lemma 2.4 at a general coefficient bound.** -/
theorem integral_Icc_normSq_logPoly_le_support_bound (a : ℕ → ℂ) {s : Finset ℕ}
    (hs0 : (0 : ℕ) ∉ s) {M : ℕ} (hsM : ∀ n ∈ s, n ≤ M) {Ω W : ℝ} (hΩ : 0 < Ω)
    (ha : ∀ n, ‖a n‖ ≤ Ω) (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ Ω ^ (2 : ℕ) * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) * (s.card : ℝ)) := by
  classical
  have ha1 : ∀ n, ‖a n / (Ω : ℂ)‖ ≤ 1 := by
    intro n
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΩ, div_le_one hΩ]
    exact ha n
  have hbase := integral_Icc_normSq_logPoly_le_support (fun n => a n / (Ω : ℂ)) hs0 hsM ha1 hW
  have hrep : ∀ w : ℝ, ‖logPoly (fun n => a n / (Ω : ℂ)) s w‖ ^ (2 : ℕ)
      = ‖logPoly a s w‖ ^ (2 : ℕ) / Ω ^ (2 : ℕ) := by
    intro w
    rw [logPoly_div_const, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΩ, div_pow]
  have hint : (∫ w in Set.Icc (-W) W, ‖logPoly (fun n => a n / (Ω : ℂ)) s w‖ ^ (2 : ℕ))
      = (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ (2 : ℕ)) / Ω ^ (2 : ℕ) := by
    rw [← MeasureTheory.integral_div]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => hrep w
  rw [hint, div_le_iff₀ (by positivity)] at hbase
  linarith [hbase]

/-- **The joint polynomial over the short ladder, with the per-step bound as a parameter.** -/
theorem integral_normSq_jointOmegaPoly_le {P Q : Finset ℕ} {A₀ B₀ : ℕ} {R η W : ℝ}
    (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime) (hQprime : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
    (hPrange : ∀ p ∈ P, R < (p : ℝ) ∧ (p : ℝ) ≤ R * (1 + η) ^ L)
    (u : ℕ → ℝ) (hu : ∀ j ∈ Finset.range L, 0 < u j) (J : ℕ → ℝ)
    (hJ : ∀ j ∈ Finset.range L,
      (∫ w in Set.Icc (-W) W,
          ‖primeBlockPoly (geomBlock P R (1 + η) j) w‖ ^ (2 : ℕ)
            * ‖omegaWeightedMoebiusPoly Q (geomCofactorBlockAt A₀ B₀ R η j) w‖ ^ (2 : ℕ)) ≤ J j) :
    (∫ w in Set.Icc (-W) W, ‖jointOmegaPoly P Q (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ 2 * ((∑ j ∈ Finset.range L, 1 / u j) * ∑ j ∈ Finset.range L, u j * J j)
        + 2 * ∫ w in Set.Icc (-W) W, ‖jointLadderProductDefect P Q A₀ B₀ R η L w‖ ^ (2 : ℕ) := by
  classical
  have hcontLad : Continuous (jointLadderProductPoly P Q A₀ B₀ R η L) := by
    refine continuous_finsetSum _ fun j _ => ?_
    exact (continuous_primeBlockPoly _).mul (continuous_logPoly _ _)
  have hcontDef : Continuous (jointLadderProductDefect P Q A₀ B₀ R η L) := by
    refine continuous_finsetSum _ fun x _ => ?_
    exact (continuous_moebiusPhase _).mul (continuous_logPoly _ _)
  have hdec : ∀ w : ℝ, jointOmegaPoly P Q (Finset.Icc A₀ B₀) w
      = jointLadderProductPoly P Q A₀ B₀ R η L w
        + (-(jointLadderProductDefect P Q A₀ B₀ R η L w)) := by
    intro w
    have h := jointLadderProductPoly_sub_jointOmega_eq A₀ B₀ hR hη hL hPprime hQprime hPQ
      hPrange w
    linear_combination -h
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => by rw [hdec w]]
  have hsplit := setIntegral_normSq_add_le
    (F := jointLadderProductPoly P Q A₀ B₀ R η L)
    (G := fun w => -(jointLadderProductDefect P Q A₀ B₀ R η L w))
    hcontLad hcontDef.neg measurableSet_Icc (subset_refl (Set.Icc (-W) W))
  have hneg : (∫ w in Set.Icc (-W) W, ‖-(jointLadderProductDefect P Q A₀ B₀ R η L w)‖ ^ (2 : ℕ))
      = ∫ w in Set.Icc (-W) W, ‖jointLadderProductDefect P Q A₀ B₀ R η L w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [norm_neg]
  rw [hneg] at hsplit
  have hharm := integral_normSq_jointLadderProductPoly_le (P := P) (Q := Q) A₀ B₀ R η u hu W
  have hstep : ∀ j ∈ Finset.range L,
      u j * (∫ w in Set.Icc (-W) W,
          ‖primeBlockPoly (geomBlock P R (1 + η) j) w‖ ^ (2 : ℕ)
            * ‖logPoly (omegaQCoeff Q) (geomCofactorBlockAt A₀ B₀ R η j) w‖ ^ (2 : ℕ))
        ≤ u j * J j := by
    intro j hj
    refine mul_le_mul_of_nonneg_left ?_ (hu j hj).le
    refine le_trans (le_of_eq ?_) (hJ j hj)
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [omegaWeightedMoebiusPoly_eq_logPoly]
  have hmass : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, 1 / u j :=
    Finset.sum_nonneg fun j hj => div_nonneg zero_le_one (hu j hj).le
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hmass
  linarith [hsplit, hharm, hsum]

end

end RHTower.Sieve
