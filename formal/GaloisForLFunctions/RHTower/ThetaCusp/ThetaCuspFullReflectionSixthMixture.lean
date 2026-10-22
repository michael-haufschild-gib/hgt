import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionFourthTuran
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionSixthTuran

open Real Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-!
# Sixth-order transport for the complete theta likelihood correction

The fourth-order reflection transport stopped before the two ordinary Bell jets
needed by the reflection-odd four-point wall.  The atomwise fifth and sixth
majorants now admit the same Gaussian summation mechanism.  This module proves
that the complete higher-mode likelihood correction has these two additional
derivatives on the physical half-line.
-/

private theorem scale_pow_five_mul_exp_tail_le_pi_pow
    {tau d : ℝ} (htau : Real.pi ≤ tau) (hd : 3 ≤ d) :
    tau ^ (5 : ℕ) * Real.exp (-tau * d) ≤
      Real.pi ^ (5 : ℕ) * Real.exp (-Real.pi * d) := by
  let y := tau - Real.pi
  let z := d * y
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzy : 3 * y ≤ z := by
    dsimp [z]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hy]
  have htauBase : tau ≤ Real.pi * (1 + y / 3) := by
    have hprod := mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hy
    dsimp [y] at hprod ⊢
    nlinarith
  have htauPow : tau ^ (5 : ℕ) ≤ Real.pi ^ (5 : ℕ) * (1 + y / 3) ^ (5 : ℕ) := by
    convert pow_le_pow_left₀ (le_trans Real.pi_pos.le htau) htauBase 5 using 1 <;>
      first | rfl | ring
  have hTaylor0 := Real.sum_le_exp_of_nonneg hz 6
  have hTaylor : 1 + z + z ^ (2 : ℕ) / 2 + z ^ (3 : ℕ) / 6 + z ^ (4 : ℕ) / 24 + z ^ (5 : ℕ) / 120 ≤
      Real.exp z := by
    norm_num [Finset.sum_range_succ] at hTaylor0 ⊢
    exact hTaylor0
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 2
  have hcube := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 3
  have hfour := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 4
  have hfive := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 5
  have hsq' : 9 * y ^ (2 : ℕ) ≤ z ^ (2 : ℕ) := by nlinarith [hsq]
  have hcube' : 27 * y ^ (3 : ℕ) ≤ z ^ (3 : ℕ) := by nlinarith [hcube]
  have hfour' : 81 * y ^ (4 : ℕ) ≤ z ^ (4 : ℕ) := by nlinarith [hfour]
  have hfive' : 243 * y ^ (5 : ℕ) ≤ z ^ (5 : ℕ) := by nlinarith [hfive]
  have hpoly : (1 + y / 3) ^ (5 : ℕ) ≤
      1 + z + z ^ (2 : ℕ) / 2 + z ^ (3 : ℕ) / 6 + z ^ (4 : ℕ) / 24 + z ^ (5 : ℕ) / 120 := by
    rw [show (1 + y / 3) ^ (5 : ℕ) =
        1 + (5 / 3 : ℝ) * y + (10 / 9 : ℝ) * y ^ (2 : ℕ) +
          (10 / 27 : ℝ) * y ^ (3 : ℕ) + (5 / 81 : ℝ) * y ^ (4 : ℕ) +
          (1 / 243 : ℝ) * y ^ (5 : ℕ) by ring]
    have hlin1 : (5 / 3 : ℝ) * y ≤ z := by nlinarith [hzy]
    have hlin2 : (10 / 9 : ℝ) * y ^ (2 : ℕ) ≤ z ^ (2 : ℕ) / 2 := by nlinarith [hsq']
    have hlin3 : (10 / 27 : ℝ) * y ^ (3 : ℕ) ≤ z ^ (3 : ℕ) / 6 := by nlinarith [hcube']
    have hlin4 : (5 / 81 : ℝ) * y ^ (4 : ℕ) ≤ z ^ (4 : ℕ) / 24 := by nlinarith [hfour']
    have hlin5 : (1 / 243 : ℝ) * y ^ (5 : ℕ) ≤ z ^ (5 : ℕ) / 120 := by
      calc
        (1 / 243 : ℝ) * y ^ (5 : ℕ) = (1 / 59049 : ℝ) * (243 * y ^ (5 : ℕ)) := by ring
        _ ≤ (1 / 59049 : ℝ) * z ^ (5 : ℕ) :=
          mul_le_mul_of_nonneg_left hfive' (by norm_num)
        _ = z ^ (5 : ℕ) / 59049 := by ring
        _ ≤ z ^ (5 : ℕ) / 120 := by
          exact div_le_div_of_nonneg_left (pow_nonneg hz 5) (by norm_num) (by norm_num)
    linarith
  have htauExp : tau ^ (5 : ℕ) ≤ Real.pi ^ (5 : ℕ) * Real.exp z :=
    htauPow.trans (mul_le_mul_of_nonneg_left (hpoly.trans hTaylor)
      (pow_nonneg Real.pi_pos.le 5))
  calc
    tau ^ (5 : ℕ) * Real.exp (-tau * d) ≤
        (Real.pi ^ (5 : ℕ) * Real.exp z) * Real.exp (-tau * d) := by gcongr
    _ = Real.pi ^ (5 : ℕ) * Real.exp (-Real.pi * d) := by
      rw [mul_assoc, ← Real.exp_add]
      dsimp [z, y]
      congr 2
      ring

private theorem scale_pow_six_mul_exp_tail_le_pi_pow
    {tau d : ℝ} (htau : Real.pi ≤ tau) (hd : 3 ≤ d) :
    tau ^ (6 : ℕ) * Real.exp (-tau * d) ≤
      Real.pi ^ (6 : ℕ) * Real.exp (-Real.pi * d) := by
  let y := tau - Real.pi
  let z := d * y
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzy : 3 * y ≤ z := by
    dsimp [z]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hy]
  have htauBase : tau ≤ Real.pi * (1 + y / 3) := by
    have hprod := mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hy
    dsimp [y] at hprod ⊢
    nlinarith
  have htauPow : tau ^ (6 : ℕ) ≤ Real.pi ^ (6 : ℕ) * (1 + y / 3) ^ (6 : ℕ) := by
    convert pow_le_pow_left₀ (le_trans Real.pi_pos.le htau) htauBase 6 using 1 <;>
      first | rfl | ring
  have hTaylor0 := Real.sum_le_exp_of_nonneg hz 7
  have hTaylor : 1 + z + z ^ (2 : ℕ) / 2 + z ^ (3 : ℕ) / 6 + z ^ (4 : ℕ) / 24 + z ^ (5 : ℕ) / 120 +
      z ^ (6 : ℕ) / 720 ≤ Real.exp z := by
    norm_num [Finset.sum_range_succ] at hTaylor0 ⊢
    exact hTaylor0
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 2
  have hcube := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 3
  have hfour := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 4
  have hfive := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 5
  have hsix := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 6
  have hsq' : 9 * y ^ (2 : ℕ) ≤ z ^ (2 : ℕ) := by nlinarith [hsq]
  have hcube' : 27 * y ^ (3 : ℕ) ≤ z ^ (3 : ℕ) := by nlinarith [hcube]
  have hfour' : 81 * y ^ (4 : ℕ) ≤ z ^ (4 : ℕ) := by nlinarith [hfour]
  have hfive' : 243 * y ^ (5 : ℕ) ≤ z ^ (5 : ℕ) := by nlinarith [hfive]
  have hsix' : 729 * y ^ (6 : ℕ) ≤ z ^ (6 : ℕ) := by nlinarith [hsix]
  have hpoly : (1 + y / 3) ^ (6 : ℕ) ≤
      1 + z + z ^ (2 : ℕ) / 2 + z ^ (3 : ℕ) / 6 + z ^ (4 : ℕ) / 24 + z ^ (5 : ℕ) / 120 + z ^ (6 : ℕ) / 720 := by
    rw [show (1 + y / 3) ^ (6 : ℕ) =
        1 + 2 * y + (5 / 3 : ℝ) * y ^ (2 : ℕ) + (20 / 27 : ℝ) * y ^ (3 : ℕ) +
          (5 / 27 : ℝ) * y ^ (4 : ℕ) + (2 / 81 : ℝ) * y ^ (5 : ℕ) +
          (1 / 729 : ℝ) * y ^ (6 : ℕ) by ring]
    have hlin1 : 2 * y ≤ z := by
      calc
        2 * y ≤ 3 * y := by nlinarith
        _ ≤ z := hzy
    have hlin2 : (5 / 3 : ℝ) * y ^ (2 : ℕ) ≤ z ^ (2 : ℕ) / 2 := by
      calc
        (5 / 3 : ℝ) * y ^ (2 : ℕ) = (5 / 27 : ℝ) * (9 * y ^ (2 : ℕ)) := by ring
        _ ≤ (5 / 27 : ℝ) * z ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hsq' (by norm_num)
        _ = z ^ (2 : ℕ) / (27 / 5 : ℝ) := by ring
        _ ≤ z ^ (2 : ℕ) / 2 := by
          exact div_le_div_of_nonneg_left (pow_nonneg hz 2) (by norm_num) (by norm_num)
    have hlin3 : (20 / 27 : ℝ) * y ^ (3 : ℕ) ≤ z ^ (3 : ℕ) / 6 := by
      calc
        (20 / 27 : ℝ) * y ^ (3 : ℕ) = (20 / 729 : ℝ) * (27 * y ^ (3 : ℕ)) := by ring
        _ ≤ (20 / 729 : ℝ) * z ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_left hcube' (by norm_num)
        _ = z ^ (3 : ℕ) / (729 / 20 : ℝ) := by ring
        _ ≤ z ^ (3 : ℕ) / 6 := by
          exact div_le_div_of_nonneg_left (pow_nonneg hz 3) (by norm_num) (by norm_num)
    have hlin4 : (5 / 27 : ℝ) * y ^ (4 : ℕ) ≤ z ^ (4 : ℕ) / 24 := by
      calc
        (5 / 27 : ℝ) * y ^ (4 : ℕ) = (5 / 2187 : ℝ) * (81 * y ^ (4 : ℕ)) := by ring
        _ ≤ (5 / 2187 : ℝ) * z ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_left hfour' (by norm_num)
        _ = z ^ (4 : ℕ) / (2187 / 5 : ℝ) := by ring
        _ ≤ z ^ (4 : ℕ) / 24 := by
          exact div_le_div_of_nonneg_left (pow_nonneg hz 4) (by norm_num) (by norm_num)
    have hlin5 : (2 / 81 : ℝ) * y ^ (5 : ℕ) ≤ z ^ (5 : ℕ) / 120 := by
      calc
        (2 / 81 : ℝ) * y ^ (5 : ℕ) = (2 / 19683 : ℝ) * (243 * y ^ (5 : ℕ)) := by ring
        _ ≤ (2 / 19683 : ℝ) * z ^ (5 : ℕ) :=
          mul_le_mul_of_nonneg_left hfive' (by norm_num)
        _ = z ^ (5 : ℕ) / (19683 / 2 : ℝ) := by ring
        _ ≤ z ^ (5 : ℕ) / 120 := by
          exact div_le_div_of_nonneg_left (pow_nonneg hz 5) (by norm_num) (by norm_num)
    have hlin6 : (1 / 729 : ℝ) * y ^ (6 : ℕ) ≤ z ^ (6 : ℕ) / 720 := by
      calc
        (1 / 729 : ℝ) * y ^ (6 : ℕ) = (1 / 531441 : ℝ) * (729 * y ^ (6 : ℕ)) := by ring
        _ ≤ (1 / 531441 : ℝ) * z ^ (6 : ℕ) :=
          mul_le_mul_of_nonneg_left hsix' (by norm_num)
        _ = z ^ (6 : ℕ) / 531441 := by ring
        _ ≤ z ^ (6 : ℕ) / 720 := by
          exact div_le_div_of_nonneg_left (pow_nonneg hz 6) (by norm_num) (by norm_num)
    linarith
  have htauExp : tau ^ (6 : ℕ) ≤ Real.pi ^ (6 : ℕ) * Real.exp z :=
    htauPow.trans (mul_le_mul_of_nonneg_left (hpoly.trans hTaylor)
      (pow_nonneg Real.pi_pos.le 6))
  calc
    tau ^ (6 : ℕ) * Real.exp (-tau * d) ≤
        (Real.pi ^ (6 : ℕ) * Real.exp z) * Real.exp (-tau * d) := by gcongr
    _ = Real.pi ^ (6 : ℕ) * Real.exp (-Real.pi * d) := by
      rw [mul_assoc, ← Real.exp_add]
      dsimp [z, y]
      congr 2
      ring

private theorem thetaCuspAtomLikelihoodRatioJetFive_majorant
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodRatioJetFive (k + 2) x| ≤
      10000 * Real.pi ^ (5 : ℕ) * thetaCuspReflectionJetTailWeight 5 k := by
  let n := k + 2
  let tau := thetaCuspLogConcavityScale x
  let d := (n : ℝ) ^ (2 : ℕ) - 1
  have hj := thetaCuspAtomLikelihoodRatioJetFive_abs_le (n := n) (by omega) hx
  have hr := thetaCuspAtomLikelihoodRatio_le_dynamic (n := n) (by omega) hx
  have htauPi : Real.pi ≤ tau := by
    dsimp [tau, thetaCuspLogConcavityScale]
    have he := Real.one_le_exp hx.le
    have hs : 1 ≤ Real.exp x ^ (2 : ℕ) := by nlinarith [Real.exp_pos x]
    nlinarith [Real.pi_pos]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 2 ≤ n)
  have hd : (3 : ℝ) ≤ d := by dsimp [d]; nlinarith
  have htail := scale_pow_five_mul_exp_tail_le_pi_pow htauPi hd
  calc
    |thetaCuspAtomLikelihoodRatioJetFive n x| ≤
        5000 * (tau * d) ^ (5 : ℕ) * thetaCuspAtomLikelihoodRatio n x := by
      simpa only [n, tau, d] using hj
    _ ≤ 5000 * (tau * d) ^ (5 : ℕ) *
        (2 * (n : ℝ) ^ (4 : ℕ) * Real.exp (-tau * d)) := by
      apply mul_le_mul_of_nonneg_left hr
      exact mul_nonneg (by norm_num)
        (pow_nonneg (mul_nonneg (le_trans Real.pi_pos.le htauPi)
          (le_trans (by norm_num) hd)) 5)
    _ = 10000 * (n : ℝ) ^ (4 : ℕ) * d ^ (5 : ℕ) *
        (tau ^ (5 : ℕ) * Real.exp (-tau * d)) := by ring
    _ ≤ 10000 * (n : ℝ) ^ (4 : ℕ) * d ^ (5 : ℕ) *
        (Real.pi ^ (5 : ℕ) * Real.exp (-Real.pi * d)) := by
      apply mul_le_mul_of_nonneg_left htail
      exact mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (le_trans (by norm_num) hnR) 4))
        (pow_nonneg (le_trans (by norm_num) hd) 5)
    _ = 10000 * Real.pi ^ (5 : ℕ) * thetaCuspReflectionJetTailWeight 5 k := by
      unfold thetaCuspReflectionJetTailWeight
      dsimp [n, d]
      ring

private theorem thetaCuspAtomLikelihoodRatioJetSix_majorant
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodRatioJetSix (k + 2) x| ≤
      120000 * Real.pi ^ (6 : ℕ) * thetaCuspReflectionJetTailWeight 6 k := by
  let n := k + 2
  let tau := thetaCuspLogConcavityScale x
  let d := (n : ℝ) ^ (2 : ℕ) - 1
  have hj := thetaCuspAtomLikelihoodRatioJetSix_abs_le (n := n) (by omega) hx
  have hr := thetaCuspAtomLikelihoodRatio_le_dynamic (n := n) (by omega) hx
  have htauPi : Real.pi ≤ tau := by
    dsimp [tau, thetaCuspLogConcavityScale]
    have he := Real.one_le_exp hx.le
    have hs : 1 ≤ Real.exp x ^ (2 : ℕ) := by nlinarith [Real.exp_pos x]
    nlinarith [Real.pi_pos]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 2 ≤ n)
  have hd : (3 : ℝ) ≤ d := by dsimp [d]; nlinarith
  have htail := scale_pow_six_mul_exp_tail_le_pi_pow htauPi hd
  calc
    |thetaCuspAtomLikelihoodRatioJetSix n x| ≤
        60000 * (tau * d) ^ (6 : ℕ) * thetaCuspAtomLikelihoodRatio n x := by
      simpa only [n, tau, d] using hj
    _ ≤ 60000 * (tau * d) ^ (6 : ℕ) *
        (2 * (n : ℝ) ^ (4 : ℕ) * Real.exp (-tau * d)) := by
      apply mul_le_mul_of_nonneg_left hr
      exact mul_nonneg (by norm_num)
        (pow_nonneg (mul_nonneg (le_trans Real.pi_pos.le htauPi)
          (le_trans (by norm_num) hd)) 6)
    _ = 120000 * (n : ℝ) ^ (4 : ℕ) * d ^ (6 : ℕ) *
        (tau ^ (6 : ℕ) * Real.exp (-tau * d)) := by ring
    _ ≤ 120000 * (n : ℝ) ^ (4 : ℕ) * d ^ (6 : ℕ) *
        (Real.pi ^ (6 : ℕ) * Real.exp (-Real.pi * d)) := by
      apply mul_le_mul_of_nonneg_left htail
      exact mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (le_trans (by norm_num) hnR) 4))
        (pow_nonneg (le_trans (by norm_num) hd) 6)
    _ = 120000 * Real.pi ^ (6 : ℕ) * thetaCuspReflectionJetTailWeight 6 k := by
      unfold thetaCuspReflectionJetTailWeight
      dsimp [n, d]
      ring

/-- Fifth derivative series of the complete higher-to-first likelihood correction. -/
def thetaCuspHigherLikelihoodJetFive (x : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspAtomLikelihoodRatioJetFive (k + 2) x

/-- Sixth derivative series of the complete higher-to-first likelihood correction. -/
def thetaCuspHigherLikelihoodJetSix (x : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspAtomLikelihoodRatioJetSix (k + 2) x

theorem summable_thetaCuspHigherLikelihoodJetFive {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => thetaCuspAtomLikelihoodRatioJetFive (k + 2) x) := by
  have hs := (summable_thetaCuspReflectionJetTailWeight 5).mul_left
    (10000 * Real.pi ^ (5 : ℕ))
  exact Summable.of_norm_bounded hs fun k => by
    simpa only [Real.norm_eq_abs] using thetaCuspAtomLikelihoodRatioJetFive_majorant k hx

theorem summable_thetaCuspHigherLikelihoodJetSix {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => thetaCuspAtomLikelihoodRatioJetSix (k + 2) x) := by
  have hs := (summable_thetaCuspReflectionJetTailWeight 6).mul_left
    (120000 * Real.pi ^ (6 : ℕ))
  exact Summable.of_norm_bounded hs fun k => by
    simpa only [Real.norm_eq_abs] using thetaCuspAtomLikelihoodRatioJetSix_majorant k hx

/-- The complete fourth likelihood jet differentiates to its fifth jet. -/
theorem hasDerivAt_thetaCuspHigherLikelihoodJetFour
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspHigherLikelihoodJetFour
      (thetaCuspHigherLikelihoodJetFive x) x := by
  have hu := (summable_thetaCuspReflectionJetTailWeight 5).mul_left
    (10000 * Real.pi ^ (5 : ℕ))
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    ordConnected_Ioi.isPreconnected
    (fun k y hy => hasDerivAt_thetaCuspAtomLikelihoodRatioJetFour
      (n := k + 2) (by omega) hy)
    (fun k y hy => by
      rw [Real.norm_eq_abs]
      exact thetaCuspAtomLikelihoodRatioJetFive_majorant k hy)
    hx (summable_thetaCuspHigherLikelihoodJetFour hx) hx
  exact key

/-- The complete fifth likelihood jet differentiates to its sixth jet. -/
theorem hasDerivAt_thetaCuspHigherLikelihoodJetFive
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspHigherLikelihoodJetFive
      (thetaCuspHigherLikelihoodJetSix x) x := by
  have hu := (summable_thetaCuspReflectionJetTailWeight 6).mul_left
    (120000 * Real.pi ^ (6 : ℕ))
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    ordConnected_Ioi.isPreconnected
    (fun k y hy => hasDerivAt_thetaCuspAtomLikelihoodRatioJetFive
      (n := k + 2) (by omega) hy)
    (fun k y hy => by
      rw [Real.norm_eq_abs]
      exact thetaCuspAtomLikelihoodRatioJetSix_majorant k hy)
    hx (summable_thetaCuspHigherLikelihoodJetFive hx) hx
  exact key

end

end RHTower
