import GaloisForLFunctions.RHTower.ThetaCuspReflectionFourthTuran
import GaloisForLFunctions.HilbertMetric.ReflectionFourthJet

/-!
# Fourth reflection--Turan law for the complete theta source

This file passes the atomwise fourth likelihood-ratio signs through the infinite theta mixture.
The two sharp symbolic Gaussian sums are proved first.  Uniform summable majorants then justify
four differentiations of the complete higher-to-first likelihood ratio.  The resulting source
inequality is the strict fourth logarithmic reflection invariant required by the coalesced
Hedenmalm three-point wall.

Every estimate is symbolic and unconditional.  No zero data or Riemann-hypothesis assumption is
used.
-/

open Real Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Gaussian weight for the `j`th likelihood-ratio jet after retaining the exact separation
`n²-1`. -/
def thetaCuspReflectionJetTailWeight (j k : ℕ) : ℝ :=
  let n : ℕ := k + 2
  (n : ℝ) ^ 4 * ((n : ℝ) ^ 2 - 1) ^ j *
    Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))

theorem thetaCuspReflectionJetTailWeight_nonneg (j k : ℕ) :
    0 ≤ thetaCuspReflectionJetTailWeight j k := by
  have hn : (1 : ℝ) ≤ (k + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k + 2)
  have hd : 0 ≤ (((k + 2 : ℕ) : ℝ) ^ 2 - 1) := by nlinarith
  unfold thetaCuspReflectionJetTailWeight
  positivity

theorem summable_thetaCuspReflectionJetTailWeight (j : ℕ) :
    Summable (thetaCuspReflectionJetTailWeight j) := by
  have hs := summable_thetaCuspLogConcavityTailWeight (4 + 2 * j)
  apply Summable.of_norm_bounded hs
  intro k
  let n : ℕ := k + 2
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 1 ≤ n)
  have hd : 0 ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
  have hdle : (n : ℝ) ^ 2 - 1 ≤ (n : ℝ) ^ 2 := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (thetaCuspReflectionJetTailWeight_nonneg j k)]
  unfold thetaCuspReflectionJetTailWeight thetaCuspLogConcavityTailWeight
  dsimp only [n]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    (n : ℝ) ^ 4 * ((n : ℝ) ^ 2 - 1) ^ j ≤
        (n : ℝ) ^ 4 * ((n : ℝ) ^ 2) ^ j := by gcongr
    _ = (n : ℝ) ^ (4 + 2 * j) := by
      rw [← pow_mul, ← pow_add]

private theorem thetaCusp_nat_add_three_le_three_mul_two_pow (k : ℕ) :
    k + 3 ≤ 3 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      omega

private theorem thetaCusp_nat_add_three_pow_eight_le (k : ℕ) :
    (((k + 3 : ℕ) : ℝ) ^ 8) ≤ 6561 * (256 : ℝ) ^ k := by
  have hcast : ((k + 3 : ℕ) : ℝ) ≤ (3 * 2 ^ k : ℕ) := by
    exact_mod_cast thetaCusp_nat_add_three_le_three_mul_two_pow k
  calc
    (((k + 3 : ℕ) : ℝ) ^ 8) ≤ (((3 * 2 ^ k : ℕ) : ℝ) ^ 8) := by gcongr
    _ = 6561 * (256 : ℝ) ^ k := by
      push_cast
      rw [mul_pow]
      norm_num
      calc
        (((2 : ℝ) ^ k) ^ 8) = (2 : ℝ) ^ (k * 8) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (8 * k) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ 8) ^ k := by rw [pow_mul]
        _ = (256 : ℝ) ^ k := by norm_num

private theorem thetaCusp_nat_add_three_pow_ten_le (k : ℕ) :
    (((k + 3 : ℕ) : ℝ) ^ 10) ≤ 59049 * (1024 : ℝ) ^ k := by
  have hcast : ((k + 3 : ℕ) : ℝ) ≤ (3 * 2 ^ k : ℕ) := by
    exact_mod_cast thetaCusp_nat_add_three_le_three_mul_two_pow k
  calc
    (((k + 3 : ℕ) : ℝ) ^ 10) ≤ (((3 * 2 ^ k : ℕ) : ℝ) ^ 10) := by gcongr
    _ = 59049 * (1024 : ℝ) ^ k := by
      push_cast
      rw [mul_pow]
      norm_num
      calc
        (((2 : ℝ) ^ k) ^ 10) = (2 : ℝ) ^ (k * 10) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (10 * k) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ 10) ^ k := by rw [pow_mul]
        _ = (1024 : ℝ) ^ k := by norm_num

private theorem thetaCusp_tail_exponent_add_three_le (k : ℕ) :
    Real.exp (-Real.pi * (((k + 3 : ℕ) : ℝ) ^ 2 - 1)) ≤
      Real.exp (-8 * Real.pi) * (Real.exp (-5 * Real.pi)) ^ k := by
  have hsquare :
      (8 : ℝ) + 5 * k ≤ (((k + 3 : ℕ) : ℝ) ^ 2 - 1) := by
    push_cast
    nlinarith [sq_nonneg (k : ℝ)]
  have hexponent :
      -Real.pi * (((k + 3 : ℕ) : ℝ) ^ 2 - 1) ≤
        -8 * Real.pi + (k : ℕ) * (-5 * Real.pi) := by
    nlinarith [Real.pi_pos]
  calc
    _ ≤ Real.exp (-8 * Real.pi + (k : ℕ) * (-5 * Real.pi)) :=
      Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]

private theorem thetaCusp_exp_neg_five_pi_lt_one_div_sixteen_thousand :
    Real.exp (-5 * Real.pi) < (1 : ℝ) / 16000 := by
  nlinarith [thetaCusp_sixteen_mul_exp_neg_five_pi_lt]

private theorem thetaCusp_exp_neg_eight_pi_lt_one_div_onehundredninetytwo_million :
    Real.exp (-8 * Real.pi) < (1 : ℝ) / 192000000 := by
  rw [show -8 * Real.pi = -3 * Real.pi + -5 * Real.pi by ring,
    Real.exp_add]
  have h3 := thetaCusp_exp_neg_three_pi_lt
  have h5 := thetaCusp_exp_neg_five_pi_lt_one_div_sixteen_thousand
  have h3pos := Real.exp_pos (-3 * Real.pi)
  have h5pos := Real.exp_pos (-5 * Real.pi)
  calc
    Real.exp (-3 * Real.pi) * Real.exp (-5 * Real.pi) <
        (1 / 12000 : ℝ) * Real.exp (-5 * Real.pi) :=
      mul_lt_mul_of_pos_right h3 h5pos
    _ < (1 / 12000 : ℝ) * (1 / 16000 : ℝ) :=
      mul_lt_mul_of_pos_left h5 (by norm_num)
    _ = (1 : ℝ) / 192000000 := by norm_num

private theorem thetaCuspReflectionJetTailWeight_two_tail_le_geometric (k : ℕ) :
    thetaCuspReflectionJetTailWeight 2 (k + 1) ≤
      (6561 / 192000000 : ℝ) * ((2 / 125 : ℝ) ^ k) := by
  let n : ℕ := k + 3
  have hpow := thetaCusp_nat_add_three_pow_eight_le k
  have hexp := thetaCusp_tail_exponent_add_three_le k
  have hbase := thetaCusp_exp_neg_eight_pi_lt_one_div_onehundredninetytwo_million.le
  have hratio : 256 * Real.exp (-5 * Real.pi) ≤ (2 / 125 : ℝ) := by
    nlinarith [thetaCusp_sixteen_mul_exp_neg_five_pi_lt]
  unfold thetaCuspReflectionJetTailWeight
  dsimp only [n]
  have hk : (3 : ℝ) ≤ (k + 3 : ℕ) := by exact_mod_cast (by omega : 3 ≤ k + 3)
  have hd : 0 ≤ (((k + 3 : ℕ) : ℝ) ^ 2 - 1) := by nlinarith
  have hdle : (((k + 3 : ℕ) : ℝ) ^ 2 - 1) ^ 2 ≤
      (((k + 3 : ℕ) : ℝ) ^ 2) ^ 2 := by gcongr <;> nlinarith
  calc
    (((k + 3 : ℕ) : ℝ) ^ 4) *
          (((k + 3 : ℕ) : ℝ) ^ 2 - 1) ^ 2 *
        Real.exp (-Real.pi * (((k + 3 : ℕ) : ℝ) ^ 2 - 1)) ≤
      (((k + 3 : ℕ) : ℝ) ^ 8) *
        Real.exp (-Real.pi * (((k + 3 : ℕ) : ℝ) ^ 2 - 1)) := by
      gcongr
      nlinarith
    _ ≤ (6561 * (256 : ℝ) ^ k) *
        (Real.exp (-8 * Real.pi) * (Real.exp (-5 * Real.pi)) ^ k) := by gcongr
    _ = 6561 * Real.exp (-8 * Real.pi) *
        (256 * Real.exp (-5 * Real.pi)) ^ k := by ring
    _ ≤ 6561 * ((1 : ℝ) / 192000000) * ((2 / 125 : ℝ) ^ k) := by gcongr
    _ = (6561 / 192000000 : ℝ) * ((2 / 125 : ℝ) ^ k) := by ring

private theorem thetaCuspReflectionJetTailWeight_three_tail_le_geometric (k : ℕ) :
    thetaCuspReflectionJetTailWeight 3 (k + 1) ≤
      (59049 / 192000000 : ℝ) * ((8 / 125 : ℝ) ^ k) := by
  let n : ℕ := k + 3
  have hpow := thetaCusp_nat_add_three_pow_ten_le k
  have hexp := thetaCusp_tail_exponent_add_three_le k
  have hbase := thetaCusp_exp_neg_eight_pi_lt_one_div_onehundredninetytwo_million.le
  have hratio : 1024 * Real.exp (-5 * Real.pi) ≤ (8 / 125 : ℝ) := by
    nlinarith [thetaCusp_sixteen_mul_exp_neg_five_pi_lt]
  unfold thetaCuspReflectionJetTailWeight
  dsimp only [n]
  have hk : (3 : ℝ) ≤ (k + 3 : ℕ) := by exact_mod_cast (by omega : 3 ≤ k + 3)
  have hd : 0 ≤ (((k + 3 : ℕ) : ℝ) ^ 2 - 1) := by nlinarith
  have hdle : (((k + 3 : ℕ) : ℝ) ^ 2 - 1) ^ 3 ≤
      (((k + 3 : ℕ) : ℝ) ^ 2) ^ 3 := by gcongr <;> nlinarith
  calc
    (((k + 3 : ℕ) : ℝ) ^ 4) *
          (((k + 3 : ℕ) : ℝ) ^ 2 - 1) ^ 3 *
        Real.exp (-Real.pi * (((k + 3 : ℕ) : ℝ) ^ 2 - 1)) ≤
      (((k + 3 : ℕ) : ℝ) ^ 10) *
        Real.exp (-Real.pi * (((k + 3 : ℕ) : ℝ) ^ 2 - 1)) := by
      gcongr
      nlinarith
    _ ≤ (59049 * (1024 : ℝ) ^ k) *
        (Real.exp (-8 * Real.pi) * (Real.exp (-5 * Real.pi)) ^ k) := by gcongr
    _ = 59049 * Real.exp (-8 * Real.pi) *
        (1024 * Real.exp (-5 * Real.pi)) ^ k := by ring
    _ ≤ 59049 * ((1 : ℝ) / 192000000) * ((8 / 125 : ℝ) ^ k) := by gcongr
    _ = (59049 / 192000000 : ℝ) * ((8 / 125 : ℝ) ^ k) := by ring

/-- Exact-separation degree-eight Gaussian sum used by the second ratio jet. -/
theorem tsum_thetaCuspReflectionJetTailWeight_two_lt :
    (∑' k : ℕ, thetaCuspReflectionJetTailWeight 2 k) < (13 / 1000 : ℝ) := by
  have hs := summable_thetaCuspReflectionJetTailWeight 2
  have htail : Summable (fun k : ℕ => thetaCuspReflectionJetTailWeight 2 (k + 1)) :=
    (summable_nat_add_iff 1).2 hs
  have hgeo : Summable (fun k : ℕ =>
      (6561 / 192000000 : ℝ) * ((2 / 125 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(2 / 125 : ℝ)‖ < 1)).mul_left _
  have hfirst : thetaCuspReflectionJetTailWeight 2 0 < (3 / 250 : ℝ) := by
    unfold thetaCuspReflectionJetTailWeight
    norm_num
    have hexp : Real.exp (-(Real.pi * 3)) < (1 : ℝ) / 12000 := by
      convert thetaCusp_exp_neg_three_pi_lt using 1 <;> ring
    nlinarith
  have htailsum :
      (∑' k : ℕ, thetaCuspReflectionJetTailWeight 2 (k + 1)) ≤
        (6561 / 192000000 : ℝ) * (1 - (2 / 125 : ℝ))⁻¹ := by
    calc
      _ ≤ ∑' k : ℕ, (6561 / 192000000 : ℝ) * ((2 / 125 : ℝ) ^ k) :=
        Summable.tsum_le_tsum thetaCuspReflectionJetTailWeight_two_tail_le_geometric htail hgeo
      _ = _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  rw [← hs.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num at htailsum ⊢
  linarith

/-- Exact-separation degree-ten Gaussian sum used by the third ratio jet. -/
theorem tsum_thetaCuspReflectionJetTailWeight_three_lt :
    (∑' k : ℕ, thetaCuspReflectionJetTailWeight 3 k) < (37 / 1000 : ℝ) := by
  have hs := summable_thetaCuspReflectionJetTailWeight 3
  have htail : Summable (fun k : ℕ => thetaCuspReflectionJetTailWeight 3 (k + 1)) :=
    (summable_nat_add_iff 1).2 hs
  have hgeo : Summable (fun k : ℕ =>
      (59049 / 192000000 : ℝ) * ((8 / 125 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(8 / 125 : ℝ)‖ < 1)).mul_left _
  have hfirst : thetaCuspReflectionJetTailWeight 3 0 < (9 / 250 : ℝ) := by
    unfold thetaCuspReflectionJetTailWeight
    norm_num
    have hexp : Real.exp (-(Real.pi * 3)) < (1 : ℝ) / 12000 := by
      convert thetaCusp_exp_neg_three_pi_lt using 1 <;> ring
    nlinarith
  have htailsum :
      (∑' k : ℕ, thetaCuspReflectionJetTailWeight 3 (k + 1)) ≤
        (59049 / 192000000 : ℝ) * (1 - (8 / 125 : ℝ))⁻¹ := by
    calc
      _ ≤ ∑' k : ℕ, (59049 / 192000000 : ℝ) * ((8 / 125 : ℝ) ^ k) :=
        Summable.tsum_le_tsum thetaCuspReflectionJetTailWeight_three_tail_le_geometric htail hgeo
      _ = _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  rw [← hs.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num at htailsum ⊢
  linarith

private theorem scale_pow_two_mul_exp_tail_le_pi_pow
    {tau d : ℝ} (htau : Real.pi ≤ tau) (hd : 3 ≤ d) :
    tau ^ 2 * Real.exp (-tau * d) ≤
      Real.pi ^ 2 * Real.exp (-Real.pi * d) := by
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
  have htauPow : tau ^ 2 ≤ Real.pi ^ 2 * (1 + y / 3) ^ 2 := by
    convert pow_le_pow_left₀ (le_trans Real.pi_pos.le htau) htauBase 2 using 1 <;> ring
  have hTaylor0 := Real.sum_le_exp_of_nonneg hz 3
  have hTaylor : 1 + z + z ^ 2 / 2 ≤ Real.exp z := by
    norm_num [Finset.sum_range_succ] at hTaylor0 ⊢
    exact hTaylor0
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 2
  have hpoly : (1 + y / 3) ^ 2 ≤ 1 + z + z ^ 2 / 2 := by nlinarith
  have htauExp : tau ^ 2 ≤ Real.pi ^ 2 * Real.exp z :=
    htauPow.trans (mul_le_mul_of_nonneg_left (hpoly.trans hTaylor) (sq_nonneg _))
  calc
    tau ^ 2 * Real.exp (-tau * d) ≤
        (Real.pi ^ 2 * Real.exp z) * Real.exp (-tau * d) := by gcongr
    _ = Real.pi ^ 2 * Real.exp (-Real.pi * d) := by
      rw [mul_assoc, ← Real.exp_add]
      dsimp [z, y]
      congr 2
      ring

private theorem scale_pow_three_mul_exp_tail_le_pi_pow
    {tau d : ℝ} (htau : Real.pi ≤ tau) (hd : 3 ≤ d) :
    tau ^ 3 * Real.exp (-tau * d) ≤
      Real.pi ^ 3 * Real.exp (-Real.pi * d) := by
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
  have htauPow : tau ^ 3 ≤ Real.pi ^ 3 * (1 + y / 3) ^ 3 := by
    convert pow_le_pow_left₀ (le_trans Real.pi_pos.le htau) htauBase 3 using 1 <;> ring
  have hTaylor0 := Real.sum_le_exp_of_nonneg hz 4
  have hTaylor : 1 + z + z ^ 2 / 2 + z ^ 3 / 6 ≤ Real.exp z := by
    norm_num [Finset.sum_range_succ] at hTaylor0 ⊢
    exact hTaylor0
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 2
  have hcube := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 3
  have hpoly : (1 + y / 3) ^ 3 ≤ 1 + z + z ^ 2 / 2 + z ^ 3 / 6 := by
    nlinarith
  have htauExp : tau ^ 3 ≤ Real.pi ^ 3 * Real.exp z :=
    htauPow.trans (mul_le_mul_of_nonneg_left (hpoly.trans hTaylor) (pow_nonneg Real.pi_pos.le 3))
  calc
    tau ^ 3 * Real.exp (-tau * d) ≤
        (Real.pi ^ 3 * Real.exp z) * Real.exp (-tau * d) := by gcongr
    _ = Real.pi ^ 3 * Real.exp (-Real.pi * d) := by
      rw [mul_assoc, ← Real.exp_add]
      dsimp [z, y]
      congr 2
      ring

private theorem scale_pow_four_mul_exp_tail_le_pi_pow
    {tau d : ℝ} (htau : Real.pi ≤ tau) (hd : 3 ≤ d) :
    tau ^ 4 * Real.exp (-tau * d) ≤
      Real.pi ^ 4 * Real.exp (-Real.pi * d) := by
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
  have htauPow : tau ^ 4 ≤ Real.pi ^ 4 * (1 + y / 3) ^ 4 := by
    convert pow_le_pow_left₀ (le_trans Real.pi_pos.le htau) htauBase 4 using 1 <;> ring
  have hTaylor0 := Real.sum_le_exp_of_nonneg hz 5
  have hTaylor : 1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 ≤ Real.exp z := by
    norm_num [Finset.sum_range_succ] at hTaylor0 ⊢
    exact hTaylor0
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 2
  have hcube := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 3
  have hfour := pow_le_pow_left₀ (mul_nonneg (by norm_num) hy) hzy 4
  have hpoly : (1 + y / 3) ^ 4 ≤
      1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 := by
    nlinarith
  have htauExp : tau ^ 4 ≤ Real.pi ^ 4 * Real.exp z :=
    htauPow.trans (mul_le_mul_of_nonneg_left (hpoly.trans hTaylor) (pow_nonneg Real.pi_pos.le 4))
  calc
    tau ^ 4 * Real.exp (-tau * d) ≤
        (Real.pi ^ 4 * Real.exp z) * Real.exp (-tau * d) := by gcongr
    _ = Real.pi ^ 4 * Real.exp (-Real.pi * d) := by
      rw [mul_assoc, ← Real.exp_add]
      dsimp [z, y]
      congr 2
      ring

private theorem thetaCuspAtomLikelihoodRatio_le_dynamic
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    thetaCuspAtomLikelihoodRatio n x ≤
      2 * (n : ℝ) ^ 4 *
        Real.exp (-thetaCuspLogConcavityScale x * ((n : ℝ) ^ 2 - 1)) := by
  have hfirst := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hx (by norm_num)
  rw [thetaCuspAtomLikelihoodRatio, div_le_iff₀ hfirst]
  simpa only [mul_assoc] using
    thetaCuspSourceTerm_le_first_dynamic (n := n) (by omega) hx.le

private theorem thetaCuspAtomLikelihoodRatioJetOne_majorant
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodRatioJetOne (k + 2) x| ≤
      (160 / 9 : ℝ) * thetaCuspLogConcavityTailWeight 6 k := by
  let n := k + 2
  let tau := thetaCuspLogConcavityScale x
  let d := (n : ℝ) ^ 2 - 1
  have hj := thetaCuspAtomLikelihoodRatioJetOne_abs_le (n := n) (by omega) hx
  have hr := thetaCuspAtomLikelihoodRatio_le_dynamic (n := n) (by omega) hx
  have htail := thetaCuspLogConcavityScale_mul_exp_tail_one (n := n) (by omega) hx.le
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 2 ≤ n)
  have hd : 0 ≤ d := by dsimp [d]; nlinarith
  have hdle : d ≤ (n : ℝ) ^ 2 := by dsimp [d]; linarith
  have htau : 0 ≤ tau := by exact (thetaCuspLogConcavityScale_pos x).le
  calc
    |thetaCuspAtomLikelihoodRatioJetOne n x| ≤
        (20 / 9 : ℝ) * (tau * d) * thetaCuspAtomLikelihoodRatio n x := by
      simpa only [n, tau, d] using hj
    _ ≤ (20 / 9 : ℝ) * (tau * d) *
        (2 * (n : ℝ) ^ 4 * Real.exp (-tau * d)) := by gcongr
    _ = (40 / 9 : ℝ) * (n : ℝ) ^ 4 * d *
        (tau * Real.exp (-tau * d)) := by ring
    _ ≤ (40 / 9 : ℝ) * (n : ℝ) ^ 4 * ((n : ℝ) ^ 2) *
        (4 * Real.exp (-Real.pi * d)) := by gcongr
    _ = (160 / 9 : ℝ) * thetaCuspLogConcavityTailWeight 6 k := by
      unfold thetaCuspLogConcavityTailWeight
      dsimp [n, d]
      ring

private theorem thetaCuspAtomLikelihoodRatioJetTwo_majorant
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaCuspAtomLikelihoodRatioJetTwo (k + 2) x ≤
      (800 / 81 : ℝ) * Real.pi ^ 2 * thetaCuspReflectionJetTailWeight 2 k := by
  let n := k + 2
  let tau := thetaCuspLogConcavityScale x
  let d := (n : ℝ) ^ 2 - 1
  have hj := (thetaCuspAtomLikelihoodRatioJetTwo_pos_le (n := n) (by omega) hx).2
  have hr := thetaCuspAtomLikelihoodRatio_le_dynamic (n := n) (by omega) hx
  have htauPi : Real.pi ≤ tau := by
    dsimp [tau, thetaCuspLogConcavityScale]
    have he := Real.one_le_exp hx.le
    have hs : 1 ≤ Real.exp x ^ 2 := by nlinarith [Real.exp_pos x]
    nlinarith [Real.pi_pos]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 2 ≤ n)
  have hd : (3 : ℝ) ≤ d := by dsimp [d]; nlinarith
  have htail := scale_pow_two_mul_exp_tail_le_pi_pow htauPi hd
  calc
    thetaCuspAtomLikelihoodRatioJetTwo n x ≤
        (400 / 81 : ℝ) * (tau * d) ^ 2 * thetaCuspAtomLikelihoodRatio n x := by
      simpa only [n, tau, d] using hj
    _ ≤ (400 / 81 : ℝ) * (tau * d) ^ 2 *
        (2 * (n : ℝ) ^ 4 * Real.exp (-tau * d)) := by gcongr
    _ = (800 / 81 : ℝ) * (n : ℝ) ^ 4 * d ^ 2 *
        (tau ^ 2 * Real.exp (-tau * d)) := by ring
    _ ≤ (800 / 81 : ℝ) * (n : ℝ) ^ 4 * d ^ 2 *
        (Real.pi ^ 2 * Real.exp (-Real.pi * d)) := by gcongr
    _ = (800 / 81 : ℝ) * Real.pi ^ 2 * thetaCuspReflectionJetTailWeight 2 k := by
      unfold thetaCuspReflectionJetTailWeight
      dsimp [n, d]
      ring

private theorem thetaCuspAtomLikelihoodRatioJetThree_majorant
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodRatioJetThree (k + 2) x| ≤
      24 * Real.pi ^ 3 * thetaCuspReflectionJetTailWeight 3 k := by
  let n := k + 2
  let tau := thetaCuspLogConcavityScale x
  let d := (n : ℝ) ^ 2 - 1
  have hj := (thetaCuspAtomLikelihoodRatioJetThree_neg_abs_le
    (n := n) (by omega) hx).2
  have hr := thetaCuspAtomLikelihoodRatio_le_dynamic (n := n) (by omega) hx
  have htauPi : Real.pi ≤ tau := by
    dsimp [tau, thetaCuspLogConcavityScale]
    have he := Real.one_le_exp hx.le
    have hs : 1 ≤ Real.exp x ^ 2 := by nlinarith [Real.exp_pos x]
    nlinarith [Real.pi_pos]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 2 ≤ n)
  have hd : (3 : ℝ) ≤ d := by dsimp [d]; nlinarith
  have htail := scale_pow_three_mul_exp_tail_le_pi_pow htauPi hd
  calc
    |thetaCuspAtomLikelihoodRatioJetThree n x| ≤
        12 * (tau * d) ^ 3 * thetaCuspAtomLikelihoodRatio n x := by
      simpa only [n, tau, d] using hj
    _ ≤ 12 * (tau * d) ^ 3 *
        (2 * (n : ℝ) ^ 4 * Real.exp (-tau * d)) := by
      apply mul_le_mul_of_nonneg_left hr
      exact mul_nonneg (by norm_num)
        (pow_nonneg (mul_nonneg (le_trans Real.pi_pos.le htauPi)
          (le_trans (by norm_num) hd)) 3)
    _ = 24 * (n : ℝ) ^ 4 * d ^ 3 *
        (tau ^ 3 * Real.exp (-tau * d)) := by ring
    _ ≤ 24 * (n : ℝ) ^ 4 * d ^ 3 *
        (Real.pi ^ 3 * Real.exp (-Real.pi * d)) := by gcongr
    _ = 24 * Real.pi ^ 3 * thetaCuspReflectionJetTailWeight 3 k := by
      unfold thetaCuspReflectionJetTailWeight
      dsimp [n, d]
      ring

private theorem thetaCuspAtomLikelihoodRatioJetFour_majorant
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodRatioJetFour (k + 2) x| ≤
      1200 * Real.pi ^ 4 * thetaCuspReflectionJetTailWeight 4 k := by
  let n := k + 2
  let tau := thetaCuspLogConcavityScale x
  let d := (n : ℝ) ^ 2 - 1
  have hj := thetaCuspAtomLikelihoodRatioJetFour_abs_le (n := n) (by omega) hx
  have hr := thetaCuspAtomLikelihoodRatio_le_dynamic (n := n) (by omega) hx
  have htauPi : Real.pi ≤ tau := by
    dsimp [tau, thetaCuspLogConcavityScale]
    have he := Real.one_le_exp hx.le
    have hs : 1 ≤ Real.exp x ^ 2 := by nlinarith [Real.exp_pos x]
    nlinarith [Real.pi_pos]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 2 ≤ n)
  have hd : (3 : ℝ) ≤ d := by dsimp [d]; nlinarith
  have htail := scale_pow_four_mul_exp_tail_le_pi_pow htauPi hd
  calc
    |thetaCuspAtomLikelihoodRatioJetFour n x| ≤
        600 * (tau * d) ^ 4 * thetaCuspAtomLikelihoodRatio n x := by
      simpa only [n, tau, d] using hj
    _ ≤ 600 * (tau * d) ^ 4 *
        (2 * (n : ℝ) ^ 4 * Real.exp (-tau * d)) := by gcongr
    _ = 1200 * (n : ℝ) ^ 4 * d ^ 4 *
        (tau ^ 4 * Real.exp (-tau * d)) := by ring
    _ ≤ 1200 * (n : ℝ) ^ 4 * d ^ 4 *
        (Real.pi ^ 4 * Real.exp (-Real.pi * d)) := by gcongr
    _ = 1200 * Real.pi ^ 4 * thetaCuspReflectionJetTailWeight 4 k := by
      unfold thetaCuspReflectionJetTailWeight
      dsimp [n, d]
      ring

/-- Complete higher-to-first likelihood-ratio derivative series. -/
def thetaCuspHigherLikelihoodJetOne (x : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspAtomLikelihoodRatioJetOne (k + 2) x

def thetaCuspHigherLikelihoodJetTwo (x : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspAtomLikelihoodRatioJetTwo (k + 2) x

def thetaCuspHigherLikelihoodJetThree (x : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspAtomLikelihoodRatioJetThree (k + 2) x

def thetaCuspHigherLikelihoodJetFour (x : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspAtomLikelihoodRatioJetFour (k + 2) x

private theorem summable_thetaCuspHigherLikelihoodJetOne {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => thetaCuspAtomLikelihoodRatioJetOne (k + 2) x) := by
  have hs := (summable_thetaCuspLogConcavityTailWeight 6).mul_left (160 / 9 : ℝ)
  exact Summable.of_norm_bounded hs fun k => by
    simpa only [Real.norm_eq_abs] using thetaCuspAtomLikelihoodRatioJetOne_majorant k hx

private theorem summable_thetaCuspHigherLikelihoodJetTwo {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => thetaCuspAtomLikelihoodRatioJetTwo (k + 2) x) := by
  have hs := (summable_thetaCuspReflectionJetTailWeight 2).mul_left
    ((800 / 81 : ℝ) * Real.pi ^ 2)
  exact Summable.of_norm_bounded hs fun k => by
    rw [Real.norm_eq_abs, abs_of_pos (thetaCuspAtomLikelihoodRatioJetTwo_pos_le
      (n := k + 2) (by omega) hx).1]
    exact thetaCuspAtomLikelihoodRatioJetTwo_majorant k hx

private theorem summable_thetaCuspHigherLikelihoodJetThree {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => thetaCuspAtomLikelihoodRatioJetThree (k + 2) x) := by
  have hs := (summable_thetaCuspReflectionJetTailWeight 3).mul_left
    (24 * Real.pi ^ 3)
  exact Summable.of_norm_bounded hs fun k => by
    simpa only [Real.norm_eq_abs] using thetaCuspAtomLikelihoodRatioJetThree_majorant k hx

private theorem summable_thetaCuspHigherLikelihoodJetFour {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => thetaCuspAtomLikelihoodRatioJetFour (k + 2) x) := by
  have hs := (summable_thetaCuspReflectionJetTailWeight 4).mul_left
    (1200 * Real.pi ^ 4)
  exact Summable.of_norm_bounded hs fun k => by
    simpa only [Real.norm_eq_abs] using thetaCuspAtomLikelihoodRatioJetFour_majorant k hx

theorem hasDerivAt_thetaCuspHigherToFirstAtomLikelihoodRatio
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspHigherToFirstAtomLikelihoodRatio
      (thetaCuspHigherLikelihoodJetOne x) x := by
  have hu := (summable_thetaCuspLogConcavityTailWeight 6).mul_left (160 / 9 : ℝ)
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    ordConnected_Ioi.isPreconnected
    (fun k y hy => hasDerivAt_thetaCuspAtomLikelihoodRatio
      (n := k + 2) (by omega) hy)
    (fun k y hy => by
      rw [Real.norm_eq_abs]
      simpa [thetaCuspAtomLikelihoodRatioJetOne,
        thetaCuspAtomLikelihoodLogJetZero] using
          thetaCuspAtomLikelihoodRatioJetOne_majorant k hy)
    hx (summable_thetaCuspHigherAtomLikelihoodRatios x) hx
  have heq : (fun y : ℝ => ∑' k : ℕ, thetaCuspAtomLikelihoodRatio (k + 2) y) =ᶠ[nhds x]
      thetaCuspHigherToFirstAtomLikelihoodRatio := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (thetaCuspHigherToFirstAtomLikelihoodRatio_eq_tsum y).symm
  simpa only [thetaCuspHigherLikelihoodJetOne] using key.congr_of_eventuallyEq heq.symm

theorem hasDerivAt_thetaCuspHigherLikelihoodJetOne
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspHigherLikelihoodJetOne
      (thetaCuspHigherLikelihoodJetTwo x) x := by
  have hu := (summable_thetaCuspReflectionJetTailWeight 2).mul_left
    ((800 / 81 : ℝ) * Real.pi ^ 2)
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    ordConnected_Ioi.isPreconnected
    (fun k y hy => hasDerivAt_thetaCuspAtomLikelihoodRatioJetOne
      (n := k + 2) (by omega) hy)
    (fun k y hy => by
      rw [Real.norm_eq_abs, abs_of_pos (thetaCuspAtomLikelihoodRatioJetTwo_pos_le
        (n := k + 2) (by omega) hy).1]
      exact thetaCuspAtomLikelihoodRatioJetTwo_majorant k hy)
    hx (summable_thetaCuspHigherLikelihoodJetOne hx) hx
  simpa only [thetaCuspHigherLikelihoodJetOne,
    thetaCuspHigherLikelihoodJetTwo] using key

theorem hasDerivAt_thetaCuspHigherLikelihoodJetTwo
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspHigherLikelihoodJetTwo
      (thetaCuspHigherLikelihoodJetThree x) x := by
  have hu := (summable_thetaCuspReflectionJetTailWeight 3).mul_left
    (24 * Real.pi ^ 3)
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    ordConnected_Ioi.isPreconnected
    (fun k y hy => hasDerivAt_thetaCuspAtomLikelihoodRatioJetTwo
      (n := k + 2) (by omega) hy)
    (fun k y hy => by
      rw [Real.norm_eq_abs]
      exact thetaCuspAtomLikelihoodRatioJetThree_majorant k hy)
    hx (summable_thetaCuspHigherLikelihoodJetTwo hx) hx
  simpa only [thetaCuspHigherLikelihoodJetTwo,
    thetaCuspHigherLikelihoodJetThree] using key

theorem hasDerivAt_thetaCuspHigherLikelihoodJetThree
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspHigherLikelihoodJetThree
      (thetaCuspHigherLikelihoodJetFour x) x := by
  have hu := (summable_thetaCuspReflectionJetTailWeight 4).mul_left
    (1200 * Real.pi ^ 4)
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    ordConnected_Ioi.isPreconnected
    (fun k y hy => hasDerivAt_thetaCuspAtomLikelihoodRatioJetThree
      (n := k + 2) (by omega) hy)
    (fun k y hy => by
      rw [Real.norm_eq_abs]
      exact thetaCuspAtomLikelihoodRatioJetFour_majorant k hy)
    hx (summable_thetaCuspHigherLikelihoodJetThree hx) hx
  simpa only [thetaCuspHigherLikelihoodJetThree,
    thetaCuspHigherLikelihoodJetFour] using key

end

end RHTower

namespace RHTower

noncomputable section

/-! ### Quantitative jets of the complete higher-to-first ratio -/

theorem thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg
    {x : ℝ} (hx : 0 < x) :
    0 ≤ thetaCuspHigherToFirstAtomLikelihoodRatio x := by
  rw [thetaCuspHigherToFirstAtomLikelihoodRatio_eq_tsum]
  exact tsum_nonneg fun k =>
    (thetaCuspAtomLikelihoodRatio_pos (n := k + 2) (by omega) hx).le

theorem abs_thetaCuspHigherLikelihoodJetOne_lt
    {x : ℝ} (hx : 0 < x) :
    |thetaCuspHigherLikelihoodJetOne x| < (1 / 10 : ℝ) := by
  have hs := summable_thetaCuspHigherLikelihoodJetOne hx
  have habs : Summable (fun k : ℕ =>
      |thetaCuspAtomLikelihoodRatioJetOne (k + 2) x|) := by
    simpa only [Real.norm_eq_abs] using hs.norm
  have hmajor := (summable_thetaCuspLogConcavityTailWeight 6).mul_left (160 / 9 : ℝ)
  unfold thetaCuspHigherLikelihoodJetOne
  calc
    |∑' k : ℕ, thetaCuspAtomLikelihoodRatioJetOne (k + 2) x| ≤
        ∑' k : ℕ, |thetaCuspAtomLikelihoodRatioJetOne (k + 2) x| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k : ℕ, (160 / 9 : ℝ) * thetaCuspLogConcavityTailWeight 6 k :=
      Summable.tsum_le_tsum
        (fun k => thetaCuspAtomLikelihoodRatioJetOne_majorant k hx) habs hmajor
    _ = (160 / 9 : ℝ) *
        (∑' k : ℕ, thetaCuspLogConcavityTailWeight 6 k) := by rw [tsum_mul_left]
    _ ≤ (160 / 9 : ℝ) * ((4 : ℝ) / 747) := by
      gcongr
      exact tsum_thetaCuspLogConcavityTailWeight_six_le
    _ < (1 / 10 : ℝ) := by norm_num

theorem thetaCuspHigherLikelihoodJetTwo_pos
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspHigherLikelihoodJetTwo x := by
  have hs := summable_thetaCuspHigherLikelihoodJetTwo hx
  unfold thetaCuspHigherLikelihoodJetTwo
  exact hs.tsum_pos
    (fun k => (thetaCuspAtomLikelihoodRatioJetTwo_pos_le
      (n := k + 2) (by omega) hx).1.le)
    0 (thetaCuspAtomLikelihoodRatioJetTwo_pos_le (n := 2) (by norm_num) hx).1

theorem thetaCuspHigherLikelihoodJetTwo_lt
    {x : ℝ} (hx : 0 < x) :
    thetaCuspHigherLikelihoodJetTwo x < (13 / 10 : ℝ) := by
  have hs := summable_thetaCuspHigherLikelihoodJetTwo hx
  have hmajor := (summable_thetaCuspReflectionJetTailWeight 2).mul_left
    ((800 / 81 : ℝ) * Real.pi ^ 2)
  have hpi2 : Real.pi ^ 2 < (10 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  unfold thetaCuspHigherLikelihoodJetTwo
  calc
    (∑' k : ℕ, thetaCuspAtomLikelihoodRatioJetTwo (k + 2) x) ≤
        ∑' k : ℕ, (800 / 81 : ℝ) * Real.pi ^ 2 *
          thetaCuspReflectionJetTailWeight 2 k :=
      Summable.tsum_le_tsum
        (fun k => thetaCuspAtomLikelihoodRatioJetTwo_majorant k hx) hs hmajor
    _ = (800 / 81 : ℝ) * Real.pi ^ 2 *
        (∑' k : ℕ, thetaCuspReflectionJetTailWeight 2 k) := by rw [tsum_mul_left]
    _ < (13 / 10 : ℝ) := by
      have hsum := tsum_thetaCuspReflectionJetTailWeight_two_lt
      have hsum0 : 0 ≤ ∑' k : ℕ, thetaCuspReflectionJetTailWeight 2 k :=
        tsum_nonneg (fun k => thetaCuspReflectionJetTailWeight_nonneg 2 k)
      have hproduct := mul_lt_mul_of_nonneg hpi2 hsum (by positivity) hsum0
      nlinarith

theorem abs_thetaCuspHigherLikelihoodJetThree_lt
    {x : ℝ} (hx : 0 < x) :
    |thetaCuspHigherLikelihoodJetThree x| < (29 : ℝ) := by
  have hs := summable_thetaCuspHigherLikelihoodJetThree hx
  have habs : Summable (fun k : ℕ =>
      |thetaCuspAtomLikelihoodRatioJetThree (k + 2) x|) := by
    simpa only [Real.norm_eq_abs] using hs.norm
  have hmajor := (summable_thetaCuspReflectionJetTailWeight 3).mul_left
    (24 * Real.pi ^ 3)
  have hpi2 : Real.pi ^ 2 < (10 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpi3 : Real.pi ^ 3 < (32 : ℝ) := by
    calc
      Real.pi ^ 3 = Real.pi ^ 2 * Real.pi := by ring
      _ < 10 * Real.pi := mul_lt_mul_of_pos_right hpi2 Real.pi_pos
      _ < 10 * 3.1416 := mul_lt_mul_of_pos_left Real.pi_lt_d4 (by norm_num)
      _ < 32 := by norm_num
  unfold thetaCuspHigherLikelihoodJetThree
  calc
    |∑' k : ℕ, thetaCuspAtomLikelihoodRatioJetThree (k + 2) x| ≤
        ∑' k : ℕ, |thetaCuspAtomLikelihoodRatioJetThree (k + 2) x| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k : ℕ, 24 * Real.pi ^ 3 * thetaCuspReflectionJetTailWeight 3 k :=
      Summable.tsum_le_tsum
        (fun k => thetaCuspAtomLikelihoodRatioJetThree_majorant k hx) habs hmajor
    _ = 24 * Real.pi ^ 3 *
        (∑' k : ℕ, thetaCuspReflectionJetTailWeight 3 k) := by rw [tsum_mul_left]
    _ < (29 : ℝ) := by
      have hsum := tsum_thetaCuspReflectionJetTailWeight_three_lt
      have hsum0 : 0 ≤ ∑' k : ℕ, thetaCuspReflectionJetTailWeight 3 k :=
        tsum_nonneg (fun k => thetaCuspReflectionJetTailWeight_nonneg 3 k)
      have hproduct := mul_lt_mul_of_nonneg hpi3 hsum (by positivity) hsum0
      nlinarith

theorem thetaCuspHigherLikelihoodJetFour_pos
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspHigherLikelihoodJetFour x := by
  have hs := summable_thetaCuspHigherLikelihoodJetFour hx
  unfold thetaCuspHigherLikelihoodJetFour
  exact hs.tsum_pos
    (fun k => (thetaCuspAtomLikelihoodRatioJetFour_pos
      (n := k + 2) (by omega) hx).le)
    0 (thetaCuspAtomLikelihoodRatioJetFour_pos (n := 2) (by norm_num) hx)

private theorem thetaCuspLogConcavityScale_mul_atomLikelihoodRatioJetTwo_majorant
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaCuspLogConcavityScale x *
        thetaCuspAtomLikelihoodRatioJetTwo (k + 2) x ≤
      (800 / 81 : ℝ) * Real.pi ^ 3 * thetaCuspReflectionJetTailWeight 2 k := by
  let n := k + 2
  let tau := thetaCuspLogConcavityScale x
  let d := (n : ℝ) ^ 2 - 1
  have hj := (thetaCuspAtomLikelihoodRatioJetTwo_pos_le (n := n) (by omega) hx).2
  have hr := thetaCuspAtomLikelihoodRatio_le_dynamic (n := n) (by omega) hx
  have htauPi : Real.pi ≤ tau := by
    dsimp [tau, thetaCuspLogConcavityScale]
    have he := Real.one_le_exp hx.le
    have hs : 1 ≤ Real.exp x ^ 2 := by nlinarith [Real.exp_pos x]
    nlinarith [Real.pi_pos]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 2 ≤ n)
  have hd : (3 : ℝ) ≤ d := by dsimp [d]; nlinarith
  have htau0 : 0 ≤ tau := le_trans Real.pi_pos.le htauPi
  have htail := scale_pow_three_mul_exp_tail_le_pi_pow htauPi hd
  calc
    tau * thetaCuspAtomLikelihoodRatioJetTwo n x ≤
        tau * ((400 / 81 : ℝ) * (tau * d) ^ 2 *
          thetaCuspAtomLikelihoodRatio n x) := by gcongr
    _ ≤ tau * ((400 / 81 : ℝ) * (tau * d) ^ 2 *
        (2 * (n : ℝ) ^ 4 * Real.exp (-tau * d))) := by gcongr
    _ = (800 / 81 : ℝ) * (n : ℝ) ^ 4 * d ^ 2 *
        (tau ^ 3 * Real.exp (-tau * d)) := by ring
    _ ≤ (800 / 81 : ℝ) * (n : ℝ) ^ 4 * d ^ 2 *
        (Real.pi ^ 3 * Real.exp (-Real.pi * d)) := by gcongr
    _ = (800 / 81 : ℝ) * Real.pi ^ 3 * thetaCuspReflectionJetTailWeight 2 k := by
      unfold thetaCuspReflectionJetTailWeight
      dsimp [n, d]
      ring

private theorem thetaCuspLogConcavityScale_mul_higherLikelihoodJetTwo_le
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLogConcavityScale x * thetaCuspHigherLikelihoodJetTwo x ≤
      (800 / 81 : ℝ) * Real.pi ^ 3 * (13 / 1000 : ℝ) := by
  have hs := summable_thetaCuspHigherLikelihoodJetTwo hx
  have hmajor := (summable_thetaCuspReflectionJetTailWeight 2).mul_left
    ((800 / 81 : ℝ) * Real.pi ^ 3)
  rw [thetaCuspHigherLikelihoodJetTwo, ← tsum_mul_left]
  calc
    (∑' k : ℕ, thetaCuspLogConcavityScale x *
        thetaCuspAtomLikelihoodRatioJetTwo (k + 2) x) ≤
      ∑' k : ℕ, (800 / 81 : ℝ) * Real.pi ^ 3 *
        thetaCuspReflectionJetTailWeight 2 k :=
      Summable.tsum_le_tsum
        (fun k => thetaCuspLogConcavityScale_mul_atomLikelihoodRatioJetTwo_majorant k hx)
        (hs.mul_left _) hmajor
    _ = (800 / 81 : ℝ) * Real.pi ^ 3 *
        (∑' k : ℕ, thetaCuspReflectionJetTailWeight 2 k) := by rw [tsum_mul_left]
    _ ≤ (800 / 81 : ℝ) * Real.pi ^ 3 * (13 / 1000 : ℝ) := by
      gcongr
      exact tsum_thetaCuspReflectionJetTailWeight_two_lt.le

private theorem thetaCuspFirstLogCurvature_lt_twenty_thirds_scale
    {x : ℝ} (hx : 0 < x) :
    thetaCuspBornWittenLogCurvature 1 x <
      (20 / 3 : ℝ) * thetaCuspLogConcavityScale x := by
  let A := thetaCuspLogConcavityScale x
  have hA : 3 < A := thetaCuspLogConcavityScale_gt_three hx.le
  have hden : 0 < (A - 3 / 2) ^ 2 := sq_pos_of_pos (by linarith)
  have hfrac : A / (A - 3 / 2) ^ 2 < (4 / 3 : ℝ) := by
    apply (div_lt_iff₀ hden).2
    have hprod : 0 < (A - 3) * (4 * A - 3) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hscale : thetaCuspMorseScale 1 x = A := by
    simp [thetaCuspMorseScale, A, thetaCuspLogConcavityScale]
  unfold thetaCuspBornWittenLogCurvature thetaCuspBornWittenCurvature
  rw [thetaCuspBornWittenWeight_eq, hscale]
  change 2 * (2 * A + 3 * A / (A - 3 / 2) ^ 2) < (20 / 3 : ℝ) * A
  calc
    2 * (2 * A + 3 * A / (A - 3 / 2) ^ 2) =
        4 * A + 6 * (A / (A - 3 / 2) ^ 2) := by ring
    _ < 4 * A + 6 * (4 / 3 : ℝ) := by gcongr
    _ < (20 / 3 : ℝ) * A := by linarith

/-- The curvature/second-tail product is small enough for the fourth logarithmic perturbation. -/
theorem eight_mul_thetaCuspFirstLogCurvature_mul_higherLikelihoodJetTwo_lt
    {x : ℝ} (hx : 0 < x) :
    8 * thetaCuspBornWittenLogCurvature 1 x *
        thetaCuspHigherLikelihoodJetTwo x < 220 := by
  let A := thetaCuspLogConcavityScale x
  let c := thetaCuspBornWittenLogCurvature 1 x
  let r2 := thetaCuspHigherLikelihoodJetTwo x
  have hA := thetaCuspLogConcavityScale_pos x
  have hc := thetaCuspFirstLogCurvature_lt_twenty_thirds_scale hx
  have hr2 := thetaCuspHigherLikelihoodJetTwo_pos hx
  have hAr2 := thetaCuspLogConcavityScale_mul_higherLikelihoodJetTwo_le hx
  have hpi2 : Real.pi ^ 2 < (10 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpi3 : Real.pi ^ 3 < (32 : ℝ) := by
    calc
      Real.pi ^ 3 = Real.pi ^ 2 * Real.pi := by ring
      _ < 10 * Real.pi := mul_lt_mul_of_pos_right hpi2 Real.pi_pos
      _ < 10 * 3.1416 := mul_lt_mul_of_pos_left Real.pi_lt_d4 (by norm_num)
      _ < 32 := by norm_num
  have hcr2 : c * r2 < (20 / 3 : ℝ) * (A * r2) := by
    simpa only [A, c, r2, mul_assoc] using mul_lt_mul_of_pos_right hc hr2
  dsimp [A, c, r2] at hcr2 hAr2 ⊢
  nlinarith [mul_lt_mul_of_pos_right hpi3 (by norm_num : (0 : ℝ) < 13 / 1000)]

end

end RHTower

namespace RHTower

noncomputable section

/-- The first theta atom has a quantitative fourth logarithmic Turan margin on the
positive half-line.  This is the source margin against which all higher-atom
perturbation terms are charged. -/
theorem thetaCuspFirstAtomLogFourthTuran_gt_four_hundred
    {x : ℝ} (hx : 0 < x) :
    (400 : ℝ) <
      4 * thetaCuspBornWittenLogCurvature 1 x ^ 2 -
        thetaCuspBornWittenLogFourthDerivative 1 x := by
  let A := thetaCuspLogConcavityScale x
  let B := A - 3 / 2
  have hA : 3 < A := thetaCuspLogConcavityScale_gt_three hx.le
  have hB : 0 < B := by dsimp [B]; linarith
  have hscale : thetaCuspMorseScale 1 x = A := by
    simp [thetaCuspMorseScale, A, thetaCuspLogConcavityScale]
  have hc : thetaCuspBornWittenLogCurvature 1 x =
      4 * A + 6 * A / B ^ 2 := by
    unfold thetaCuspBornWittenLogCurvature thetaCuspBornWittenCurvature
    rw [thetaCuspBornWittenWeight_eq, hscale]
    dsimp [B]
    ring
  have hv4 : thetaCuspBornWittenLogFourthDerivative 1 x =
      16 * A + 24 * A / B ^ 2 + 216 * A / B ^ 3 + 324 * A / B ^ 4 := by
    unfold thetaCuspBornWittenLogFourthDerivative
    rw [thetaCuspBornWittenWeight_eq, hscale]
    dsimp [B]
    field_simp [hB.ne'] <;> ring
  have hdecomp :
      4 * thetaCuspBornWittenLogCurvature 1 x ^ 2 -
          thetaCuspBornWittenLogFourthDerivative 1 x =
        16 * A * (4 * A - 1) +
          24 * A * (8 * A - 1) / B ^ 2 -
          72 * A ^ 2 / B ^ 4 := by
    rw [hc, hv4]
    field_simp [hB.ne'] <;> ring
  have hfrac : A / B ^ 4 < (16 / 27 : ℝ) := by
    apply (div_lt_iff₀ (pow_pos hB 4)).2
    let y := A - 3
    have hy : 0 < y := by dsimp [y]; linarith
    apply sub_pos.mp
    rw [show (16 / 27 : ℝ) * B ^ 4 - A =
        (16 / 27) * y ^ 4 + (32 / 9) * y ^ 3 + 8 * y ^ 2 + 7 * y by
      dsimp [B, y]
      ring]
    positivity
  have hlead : (176 / 3 : ℝ) * A ^ 2 < 16 * A * (4 * A - 1) := by
    have hA0 : 0 < A := by linarith
    have hgap : 0 < A - 3 := by linarith
    nlinarith [mul_pos hA0 hgap]
  have hmiddle : 0 < 24 * A * (8 * A - 1) / B ^ 2 := by
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
    · exact sq_pos_of_pos hB
  have htailProduct : 72 * A * (A / B ^ 4) < (128 / 3 : ℝ) * A := by
    have hA0 : 0 < A := by linarith
    nlinarith [mul_lt_mul_of_pos_left hfrac (mul_pos (by norm_num : (0 : ℝ) < 72) hA0)]
  have htailIdentity : 72 * A ^ 2 / B ^ 4 = 72 * A * (A / B ^ 4) := by
    field_simp [hB.ne'] <;> ring
  have htailLinear : 72 * A ^ 2 / B ^ 4 < (128 / 3 : ℝ) * A := by
    rw [htailIdentity]
    exact htailProduct
  have hlinearQuadratic : (128 / 3 : ℝ) * A < (128 / 9 : ℝ) * A ^ 2 := by
    have hA0 : 0 < A := by linarith
    nlinarith [mul_pos hA0 (sub_pos.mpr hA)]
  have hA2 : (9 : ℝ) < A ^ 2 := by nlinarith
  rw [hdecomp]
  nlinarith

end

end RHTower

namespace RHTower

noncomputable section

/-- Second logarithmic derivative of the complete higher-to-first-atom correction. -/
def thetaCuspHigherLikelihoodLogJetTwo (x : ℝ) : ℝ :=
  thetaCuspHigherLikelihoodJetTwo x /
      (1 + thetaCuspHigherToFirstAtomLikelihoodRatio x) -
    thetaCuspHigherLikelihoodJetOne x ^ 2 /
      (1 + thetaCuspHigherToFirstAtomLikelihoodRatio x) ^ 2

/-- Fourth logarithmic derivative of the complete higher-to-first-atom correction. -/
def thetaCuspHigherLikelihoodLogJetFour (x : ℝ) : ℝ :=
  let s := 1 + thetaCuspHigherToFirstAtomLikelihoodRatio x
  thetaCuspHigherLikelihoodJetFour x / s -
    4 * thetaCuspHigherLikelihoodJetOne x * thetaCuspHigherLikelihoodJetThree x / s ^ 2 -
    3 * thetaCuspHigherLikelihoodJetTwo x ^ 2 / s ^ 2 +
    12 * thetaCuspHigherLikelihoodJetOne x ^ 2 * thetaCuspHigherLikelihoodJetTwo x / s ^ 3 -
    6 * thetaCuspHigherLikelihoodJetOne x ^ 4 / s ^ 4

/-- The logarithmic second correction is bounded above by the ordinary second tail jet. -/
theorem thetaCuspHigherLikelihoodLogJetTwo_le
    {x : ℝ} (hx : 0 < x) :
    thetaCuspHigherLikelihoodLogJetTwo x ≤ thetaCuspHigherLikelihoodJetTwo x := by
  let r0 := thetaCuspHigherToFirstAtomLikelihoodRatio x
  let r1 := thetaCuspHigherLikelihoodJetOne x
  let r2 := thetaCuspHigherLikelihoodJetTwo x
  let s := 1 + r0
  have hr0 : 0 ≤ r0 := by
    simpa only [r0] using thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg hx
  have hr2 : 0 < r2 := by simpa only [r2] using thetaCuspHigherLikelihoodJetTwo_pos hx
  have hs : 0 < s := by dsimp [s]; linarith
  have hdiv : r2 / s ≤ r2 := by
    apply (div_le_iff₀ hs).2
    have : 0 ≤ r2 * r0 := mul_nonneg hr2.le hr0
    dsimp [s]
    nlinarith
  have hsquare : 0 ≤ r1 ^ 2 / s ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  dsimp [thetaCuspHigherLikelihoodLogJetTwo, r0, r1, r2, s] at hdiv hsquare ⊢
  linarith

/-- The fourth logarithmic correction from all higher atoms loses less than seventeen units. -/
theorem neg_seventeen_lt_thetaCuspHigherLikelihoodLogJetFour
    {x : ℝ} (hx : 0 < x) :
    (-17 : ℝ) < thetaCuspHigherLikelihoodLogJetFour x := by
  let r0 := thetaCuspHigherToFirstAtomLikelihoodRatio x
  let r1 := thetaCuspHigherLikelihoodJetOne x
  let r2 := thetaCuspHigherLikelihoodJetTwo x
  let r3 := thetaCuspHigherLikelihoodJetThree x
  let r4 := thetaCuspHigherLikelihoodJetFour x
  let s := 1 + r0
  have hr0 : 0 ≤ r0 := by
    simpa only [r0] using thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg hx
  have hs : 1 ≤ s := by dsimp [s]; linarith
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hr1 := abs_thetaCuspHigherLikelihoodJetOne_lt hx
  have hr2pos : 0 < r2 := by simpa only [r2] using thetaCuspHigherLikelihoodJetTwo_pos hx
  have hr2 : r2 < (13 / 10 : ℝ) := by
    simpa only [r2] using thetaCuspHigherLikelihoodJetTwo_lt hx
  have hr3 : |r3| < (29 : ℝ) := by
    simpa only [r3] using abs_thetaCuspHigherLikelihoodJetThree_lt hx
  have hr4 : 0 < r4 := by simpa only [r4] using thetaCuspHigherLikelihoodJetFour_pos hx
  have hcrossDiv : r1 * r3 / s ^ 2 ≤ |r1| * |r3| := by
    apply (div_le_iff₀ (sq_pos_of_pos hs0)).2
    have hraw : r1 * r3 ≤ |r1| * |r3| := by
      calc
        r1 * r3 ≤ |r1 * r3| := le_abs_self _
        _ = |r1| * |r3| := abs_mul r1 r3
    have hscale : |r1| * |r3| ≤ |r1| * |r3| * s ^ 2 := by
      have hnonneg : 0 ≤ |r1| * |r3| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hs2 : 1 ≤ s ^ 2 := by nlinarith
      nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hs2)]
    exact hraw.trans hscale
  have hr2Div : r2 ^ 2 / s ^ 2 ≤ r2 ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hs0)).2
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg r2) (sub_nonneg.mpr hs2)]
  have hr1FourDiv : r1 ^ 4 / s ^ 4 ≤ |r1| ^ 4 := by
    apply (div_le_iff₀ (pow_pos hs0 4)).2
    have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ hs
    have heq : r1 ^ 4 = |r1| ^ 4 := by
      calc
        r1 ^ 4 = (r1 ^ 2) ^ 2 := by ring
        _ = (|r1| ^ 2) ^ 2 := by rw [sq_abs]
        _ = |r1| ^ 4 := by ring
    rw [heq]
    nlinarith [mul_nonneg (pow_nonneg (abs_nonneg r1) 4) (sub_nonneg.mpr hs4)]
  have hcross : |r1| * |r3| < (29 / 10 : ℝ) := by
    have := mul_lt_mul_of_nonneg hr1 hr3 (abs_nonneg r1) (abs_nonneg r3)
    norm_num at this ⊢
    exact this
  have hr2sq : r2 ^ 2 < (169 / 100 : ℝ) := by
    have hsum : 0 < (13 / 10 : ℝ) + r2 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hr2) hsum]
  have hr1sq : |r1| ^ 2 < (1 / 100 : ℝ) := by
    have hsum : 0 < (1 / 10 : ℝ) + |r1| := by positivity
    nlinarith [mul_pos (sub_pos.mpr hr1) hsum]
  have hr1four : |r1| ^ 4 < (1 / 10000 : ℝ) := by
    have hsum : 0 < (1 / 100 : ℝ) + |r1| ^ 2 := by positivity
    nlinarith [mul_pos (sub_pos.mpr hr1sq) hsum]
  have hpositiveFour : 0 < r4 / s := div_pos hr4 hs0
  have hpositiveCubic : 0 ≤ 12 * r1 ^ 2 * r2 / s ^ 3 := by positivity
  have hcrossTerm :
      -4 * |r1| * |r3| ≤ -4 * r1 * r3 / s ^ 2 := by
    have h := mul_le_mul_of_nonpos_left hcrossDiv (by norm_num : (-4 : ℝ) ≤ 0)
    convert h using 1 <;> ring
  have hr2Term : -3 * r2 ^ 2 ≤ -3 * r2 ^ 2 / s ^ 2 := by
    have h := mul_le_mul_of_nonpos_left hr2Div (by norm_num : (-3 : ℝ) ≤ 0)
    convert h using 1 <;> ring
  have hr1FourTerm : -6 * |r1| ^ 4 ≤ -6 * r1 ^ 4 / s ^ 4 := by
    have h := mul_le_mul_of_nonpos_left hr1FourDiv (by norm_num : (-6 : ℝ) ≤ 0)
    convert h using 1 <;> ring
  have hcrossLower : (-58 / 5 : ℝ) < -4 * r1 * r3 / s ^ 2 := by
    nlinarith
  have hr2Lower : (-507 / 100 : ℝ) < -3 * r2 ^ 2 / s ^ 2 := by
    nlinarith
  have hr1FourLower : (-3 / 5000 : ℝ) < -6 * r1 ^ 4 / s ^ 4 := by
    nlinarith
  change (-17 : ℝ) < r4 / s - 4 * r1 * r3 / s ^ 2 - 3 * r2 ^ 2 / s ^ 2 +
    12 * r1 ^ 2 * r2 / s ^ 3 - 6 * r1 ^ 4 / s ^ 4
  calc
    (-17 : ℝ) < (-58 / 5 : ℝ) + (-507 / 100 : ℝ) + (-3 / 5000 : ℝ) := by
      norm_num
    _ < r4 / s + (-4 * r1 * r3 / s ^ 2) + (-3 * r2 ^ 2 / s ^ 2) +
        12 * r1 ^ 2 * r2 / s ^ 3 + (-6 * r1 ^ 4 / s ^ 4) := by
      linarith
    _ = r4 / s - 4 * r1 * r3 / s ^ 2 - 3 * r2 ^ 2 / s ^ 2 +
        12 * r1 ^ 2 * r2 / s ^ 3 - 6 * r1 ^ 4 / s ^ 4 := by ring

/-- The normalized fourth logarithmic Turan invariant of the complete theta source. -/
def thetaCuspFullLogFourthTuranNormalized (x : ℝ) : ℝ :=
  -thetaCuspBornWittenLogFourthDerivative 1 x +
    thetaCuspHigherLikelihoodLogJetFour x +
    4 * (-thetaCuspBornWittenLogCurvature 1 x +
      thetaCuspHigherLikelihoodLogJetTwo x) ^ 2

/-- The complete theta source retains a uniform positive fourth logarithmic Turan margin on the
positive half-line after every higher atom is included. -/
theorem one_hundred_sixty_lt_thetaCuspFullLogFourthTuranNormalized
    {x : ℝ} (hx : 0 < x) :
    (160 : ℝ) < thetaCuspFullLogFourthTuranNormalized x := by
  let c := thetaCuspBornWittenLogCurvature 1 x
  let e2 := thetaCuspHigherLikelihoodLogJetTwo x
  let e4 := thetaCuspHigherLikelihoodLogJetFour x
  let r2 := thetaCuspHigherLikelihoodJetTwo x
  have hbase := thetaCuspFirstAtomLogFourthTuran_gt_four_hundred hx
  have he4 : (-17 : ℝ) < e4 := by
    simpa only [e4] using neg_seventeen_lt_thetaCuspHigherLikelihoodLogJetFour hx
  have he2 : e2 ≤ r2 := by
    simpa only [e2, r2] using thetaCuspHigherLikelihoodLogJetTwo_le hx
  have hc : 0 < c := by
    have h := nineteen_le_thetaCuspBornWittenLogCurvature (n := 1) (by norm_num) hx.le
    dsimp only [c]
    linarith
  have hcross := eight_mul_thetaCuspFirstLogCurvature_mul_higherLikelihoodJetTwo_lt hx
  have hcross' : 8 * c * e2 < (220 : ℝ) := by
    have hle : 8 * c * e2 ≤ 8 * c * r2 := by gcongr
    exact lt_of_le_of_lt hle hcross
  have he2sq : 0 ≤ e2 ^ 2 := sq_nonneg e2
  dsimp [thetaCuspFullLogFourthTuranNormalized, c, e2, e4] at hbase he4 hcross' he2sq ⊢
  nlinarith

end

end RHTower

namespace RHTower

noncomputable section

/-- Logarithm of the complete higher-to-first correction factor. -/
def thetaCuspHigherLikelihoodLog (x : ℝ) : ℝ :=
  Real.log (1 + thetaCuspHigherToFirstAtomLikelihoodRatio x)

/-- First logarithmic jet of the complete correction factor. -/
def thetaCuspHigherLikelihoodLogJetOne (x : ℝ) : ℝ :=
  thetaCuspHigherLikelihoodJetOne x /
    (1 + thetaCuspHigherToFirstAtomLikelihoodRatio x)

/-- Third logarithmic jet of the complete correction factor. -/
def thetaCuspHigherLikelihoodLogJetThree (x : ℝ) : ℝ :=
  let s := 1 + thetaCuspHigherToFirstAtomLikelihoodRatio x
  thetaCuspHigherLikelihoodJetThree x / s -
    3 * thetaCuspHigherLikelihoodJetOne x * thetaCuspHigherLikelihoodJetTwo x / s ^ 2 +
    2 * thetaCuspHigherLikelihoodJetOne x ^ 3 / s ^ 3

/-- Exact first derivative of the complete higher likelihood log-factor. -/
theorem hasDerivAt_thetaCuspHigherLikelihoodLog
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspHigherLikelihoodLog
      (thetaCuspHigherLikelihoodLogJetOne x) x := by
  have h0 := hasDerivAt_thetaCuspHigherToFirstAtomLikelihoodRatio hx
  have hs := h0.const_add 1
  have hspos : 0 < 1 + thetaCuspHigherToFirstAtomLikelihoodRatio x := by
    have h := thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg hx
    linarith
  simpa only [thetaCuspHigherLikelihoodLog, thetaCuspHigherLikelihoodLogJetOne] using
    hs.log hspos.ne'

/-- Exact second derivative of the complete higher likelihood log-factor. -/
theorem hasDerivAt_thetaCuspHigherLikelihoodLogJetOne
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspHigherLikelihoodLogJetOne
      (thetaCuspHigherLikelihoodLogJetTwo x) x := by
  have h0 := hasDerivAt_thetaCuspHigherToFirstAtomLikelihoodRatio hx
  have h1 := hasDerivAt_thetaCuspHigherLikelihoodJetOne hx
  have hs := h0.const_add 1
  have hspos : 0 < 1 + thetaCuspHigherToFirstAtomLikelihoodRatio x := by
    have h := thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg hx
    linarith
  have hquot := h1.div hs hspos.ne'
  convert hquot using 1
  unfold thetaCuspHigherLikelihoodLogJetTwo
  field_simp [hspos.ne']

/-- Exact third derivative of the complete higher likelihood log-factor. -/
theorem hasDerivAt_thetaCuspHigherLikelihoodLogJetTwo
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspHigherLikelihoodLogJetTwo
      (thetaCuspHigherLikelihoodLogJetThree x) x := by
  have h0 := hasDerivAt_thetaCuspHigherToFirstAtomLikelihoodRatio hx
  have h1 := hasDerivAt_thetaCuspHigherLikelihoodJetOne hx
  have h2 := hasDerivAt_thetaCuspHigherLikelihoodJetTwo hx
  have hs := h0.const_add 1
  have hspos : 0 < 1 + thetaCuspHigherToFirstAtomLikelihoodRatio x := by
    have h := thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg hx
    linarith
  have hraw := (h2.div hs hspos.ne').sub
    ((h1.pow 2).div (hs.pow 2) (pow_ne_zero 2 hspos.ne'))
  convert hraw using 1
  unfold thetaCuspHigherLikelihoodLogJetThree
  simp only [Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
  field_simp [hspos.ne']
  ring

/-- Exact fourth derivative of the complete higher likelihood log-factor. -/
theorem hasDerivAt_thetaCuspHigherLikelihoodLogJetThree
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspHigherLikelihoodLogJetThree
      (thetaCuspHigherLikelihoodLogJetFour x) x := by
  have h0 := hasDerivAt_thetaCuspHigherToFirstAtomLikelihoodRatio hx
  have h1 := hasDerivAt_thetaCuspHigherLikelihoodJetOne hx
  have h2 := hasDerivAt_thetaCuspHigherLikelihoodJetTwo hx
  have h3 := hasDerivAt_thetaCuspHigherLikelihoodJetThree hx
  have hs := h0.const_add 1
  have hspos : 0 < 1 + thetaCuspHigherToFirstAtomLikelihoodRatio x := by
    have h := thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg hx
    linarith
  have hraw := ((h3.div hs hspos.ne').sub
      (((h1.mul h2).const_mul 3).div (hs.pow 2) (pow_ne_zero 2 hspos.ne'))).add
    (((h1.pow 3).const_mul 2).div (hs.pow 3) (pow_ne_zero 3 hspos.ne'))
  convert hraw using 1
  · funext y
    simp only [thetaCuspHigherLikelihoodLogJetThree, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    ring_nf
  · unfold thetaCuspHigherLikelihoodLogJetFour
    simp only [Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
    field_simp [hspos.ne']
    ring

/-- Logarithm of the first positive theta atom. -/
def thetaCuspFirstAtomLog (x : ℝ) : ℝ :=
  Real.log (thetaCuspSourceTerm x 1)

def thetaCuspFirstAtomLogJetOne (x : ℝ) : ℝ :=
  -2 * thetaCuspBornWittenSuperpotential 1 x

def thetaCuspFirstAtomLogJetTwo (x : ℝ) : ℝ :=
  -thetaCuspBornWittenLogCurvature 1 x

def thetaCuspFirstAtomLogJetThree (x : ℝ) : ℝ :=
  -thetaCuspBornWittenLogThirdDerivative 1 x

def thetaCuspFirstAtomLogJetFour (x : ℝ) : ℝ :=
  -thetaCuspBornWittenLogFourthDerivative 1 x

private theorem hasDerivAt_thetaCuspFirstAtomLog
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFirstAtomLog (thetaCuspFirstAtomLogJetOne x) x := by
  have hsource := hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore
    (n := 1) (by norm_num) hx
  have hpos := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hx (by norm_num)
  have hlog := hsource.log hpos.ne'
  convert hlog using 1
  unfold thetaCuspFirstAtomLogJetOne
  field_simp [hpos.ne']

private theorem hasDerivAt_thetaCuspFirstAtomLogJetOne
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFirstAtomLogJetOne (thetaCuspFirstAtomLogJetTwo x) x := by
  have h := (hasDerivAt_thetaCuspBornWittenSuperpotential
    (n := 1) (by norm_num) hx.le).const_mul (-2)
  convert h using 1
  simp only [thetaCuspFirstAtomLogJetTwo, thetaCuspBornWittenLogCurvature]
  ring

private theorem hasDerivAt_thetaCuspFirstAtomLogJetTwo
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFirstAtomLogJetTwo (thetaCuspFirstAtomLogJetThree x) x := by
  simpa only [thetaCuspFirstAtomLogJetTwo, thetaCuspFirstAtomLogJetThree] using
    (hasDerivAt_thetaCuspBornWittenLogCurvature
      (n := 1) (by norm_num) hx.le).neg

private theorem hasDerivAt_thetaCuspFirstAtomLogJetThree
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFirstAtomLogJetThree (thetaCuspFirstAtomLogJetFour x) x := by
  simpa only [thetaCuspFirstAtomLogJetThree, thetaCuspFirstAtomLogJetFour] using
    (hasDerivAt_thetaCuspBornWittenLogThirdDerivative
      (n := 1) (by norm_num) hx.le).neg

/-- Local factorization of the complete source by its first atom and the exact higher tail. -/
theorem thetaCuspFullSource_eq_firstAtom_mul_higherFactor
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFullSource x = thetaCuspSourceTerm x 1 *
      (1 + thetaCuspHigherToFirstAtomLikelihoodRatio x) := by
  have hfirst := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hx (by norm_num)
  unfold thetaCuspHigherToFirstAtomLikelihoodRatio
  field_simp [hfirst.ne']
  ring

private def thetaCuspFullLogFactorZero (x : ℝ) : ℝ :=
  thetaCuspFirstAtomLog x + thetaCuspHigherLikelihoodLog x

private def thetaCuspFullLogFactorOne (x : ℝ) : ℝ :=
  thetaCuspFirstAtomLogJetOne x + thetaCuspHigherLikelihoodLogJetOne x

private def thetaCuspFullLogFactorTwo (x : ℝ) : ℝ :=
  thetaCuspFirstAtomLogJetTwo x + thetaCuspHigherLikelihoodLogJetTwo x

private def thetaCuspFullLogFactorThree (x : ℝ) : ℝ :=
  thetaCuspFirstAtomLogJetThree x + thetaCuspHigherLikelihoodLogJetThree x

private def thetaCuspFullLogFactorFour (x : ℝ) : ℝ :=
  thetaCuspFirstAtomLogJetFour x + thetaCuspHigherLikelihoodLogJetFour x

private theorem hasDerivAt_thetaCuspFullLogFactorZero
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFullLogFactorZero (thetaCuspFullLogFactorOne x) x := by
  simpa only [thetaCuspFullLogFactorZero, thetaCuspFullLogFactorOne] using
    (hasDerivAt_thetaCuspFirstAtomLog hx).add
      (hasDerivAt_thetaCuspHigherLikelihoodLog hx)

private theorem hasDerivAt_thetaCuspFullLogFactorOne
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFullLogFactorOne (thetaCuspFullLogFactorTwo x) x := by
  simpa only [thetaCuspFullLogFactorOne, thetaCuspFullLogFactorTwo] using
    (hasDerivAt_thetaCuspFirstAtomLogJetOne hx).add
      (hasDerivAt_thetaCuspHigherLikelihoodLogJetOne hx)

private theorem hasDerivAt_thetaCuspFullLogFactorTwo
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFullLogFactorTwo (thetaCuspFullLogFactorThree x) x := by
  simpa only [thetaCuspFullLogFactorTwo, thetaCuspFullLogFactorThree] using
    (hasDerivAt_thetaCuspFirstAtomLogJetTwo hx).add
      (hasDerivAt_thetaCuspHigherLikelihoodLogJetTwo hx)

private theorem hasDerivAt_thetaCuspFullLogFactorThree
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFullLogFactorThree (thetaCuspFullLogFactorFour x) x := by
  simpa only [thetaCuspFullLogFactorThree, thetaCuspFullLogFactorFour] using
    (hasDerivAt_thetaCuspFirstAtomLogJetThree hx).add
      (hasDerivAt_thetaCuspHigherLikelihoodLogJetThree hx)

private theorem thetaCuspLogSource_eventuallyEq_fullLogFactorZero
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLogSource =ᶠ[nhds x] thetaCuspFullLogFactorZero := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  have hfirst := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hy (by norm_num)
  have hhigher : 0 < 1 + thetaCuspHigherToFirstAtomLikelihoodRatio y := by
    have h := thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg hy
    linarith
  rw [thetaCuspLogSource, thetaCuspFullLogFactorZero,
    thetaCuspFullSource_eq_firstAtom_mul_higherFactor hy,
    Real.log_mul hfirst.ne' hhigher.ne']
  rfl

private theorem iteratedDeriv_one_thetaCuspLogSource_eq_factor
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 1 thetaCuspLogSource x = thetaCuspFullLogFactorOne x := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_thetaCuspFullLogFactorZero hx |>.congr_of_eventuallyEq
    (thetaCuspLogSource_eventuallyEq_fullLogFactorZero hx)).deriv

/-- The actual logarithmic source curvature is the first-atom curvature plus the exact complete
higher-tail correction. -/
theorem iteratedDeriv_two_thetaCuspLogSource_eq_factor
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 thetaCuspLogSource x =
      -thetaCuspBornWittenLogCurvature 1 x + thetaCuspHigherLikelihoodLogJetTwo x := by
  have heq : iteratedDeriv 1 thetaCuspLogSource =ᶠ[nhds x]
      thetaCuspFullLogFactorOne := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_one_thetaCuspLogSource_eq_factor hy
  rw [iteratedDeriv_succ]
  have h := (hasDerivAt_thetaCuspFullLogFactorOne hx |>.congr_of_eventuallyEq heq).deriv
  simpa only [thetaCuspFullLogFactorTwo, thetaCuspFirstAtomLogJetTwo] using h

private theorem iteratedDeriv_three_thetaCuspLogSource_eq_factor
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 thetaCuspLogSource x = thetaCuspFullLogFactorThree x := by
  have heq : iteratedDeriv 2 thetaCuspLogSource =ᶠ[nhds x]
      thetaCuspFullLogFactorTwo := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have h := iteratedDeriv_two_thetaCuspLogSource_eq_factor hy
    simpa only [thetaCuspFullLogFactorTwo, thetaCuspFirstAtomLogJetTwo] using h
  rw [iteratedDeriv_succ]
  exact (hasDerivAt_thetaCuspFullLogFactorTwo hx |>.congr_of_eventuallyEq heq).deriv

/-- Exact fourth logarithmic derivative of the actual complete theta source. -/
theorem iteratedDeriv_four_thetaCuspLogSource_eq_factor
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 4 thetaCuspLogSource x =
      -thetaCuspBornWittenLogFourthDerivative 1 x +
        thetaCuspHigherLikelihoodLogJetFour x := by
  have heq : iteratedDeriv 3 thetaCuspLogSource =ᶠ[nhds x]
      thetaCuspFullLogFactorThree := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_three_thetaCuspLogSource_eq_factor hy
  rw [iteratedDeriv_succ]
  have h := (hasDerivAt_thetaCuspFullLogFactorThree hx |>.congr_of_eventuallyEq heq).deriv
  simpa only [thetaCuspFullLogFactorFour, thetaCuspFirstAtomLogJetFour] using h

/-- Source-level fourth logarithmic Turan inequality for the complete Riemann--Jacobi theta
source.  This is the strict positive-half-line theorem required by the center-mixed fourth-jet
route. -/
theorem thetaCuspLogSource_fourthTuran_gt_one_hundred_sixty
    {x : ℝ} (hx : 0 < x) :
    (160 : ℝ) < iteratedDeriv 4 thetaCuspLogSource x +
      4 * iteratedDeriv 2 thetaCuspLogSource x ^ 2 := by
  rw [iteratedDeriv_four_thetaCuspLogSource_eq_factor hx,
    iteratedDeriv_two_thetaCuspLogSource_eq_factor hx]
  exact one_hundred_sixty_lt_thetaCuspFullLogFourthTuranNormalized hx

end

end RHTower

namespace RHTower

noncomputable section

private def thetaCuspFullLogExponentialJetZero (x : ℝ) : ℝ :=
  Real.exp (thetaCuspFullLogFactorZero x)

private def thetaCuspFullLogExponentialJetOne (x : ℝ) : ℝ :=
  thetaCuspFullLogExponentialJetZero x * thetaCuspFullLogFactorOne x

private def thetaCuspFullLogExponentialJetTwo (x : ℝ) : ℝ :=
  thetaCuspFullLogExponentialJetZero x *
    (thetaCuspFullLogFactorOne x ^ 2 + thetaCuspFullLogFactorTwo x)

private def thetaCuspFullLogExponentialJetThree (x : ℝ) : ℝ :=
  thetaCuspFullLogExponentialJetZero x *
    (thetaCuspFullLogFactorOne x ^ 3 +
      3 * thetaCuspFullLogFactorOne x * thetaCuspFullLogFactorTwo x +
      thetaCuspFullLogFactorThree x)

private def thetaCuspFullLogExponentialJetFour (x : ℝ) : ℝ :=
  thetaCuspFullLogExponentialJetZero x *
    (thetaCuspFullLogFactorOne x ^ 4 +
      6 * thetaCuspFullLogFactorOne x ^ 2 * thetaCuspFullLogFactorTwo x +
      3 * thetaCuspFullLogFactorTwo x ^ 2 +
      4 * thetaCuspFullLogFactorOne x * thetaCuspFullLogFactorThree x +
      thetaCuspFullLogFactorFour x)

private theorem hasDerivAt_thetaCuspFullLogExponentialJetZero
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFullLogExponentialJetZero
      (thetaCuspFullLogExponentialJetOne x) x := by
  simpa only [thetaCuspFullLogExponentialJetZero,
    thetaCuspFullLogExponentialJetOne] using
      (hasDerivAt_thetaCuspFullLogFactorZero hx).exp

private theorem hasDerivAt_thetaCuspFullLogExponentialJetOne
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFullLogExponentialJetOne
      (thetaCuspFullLogExponentialJetTwo x) x := by
  have h := (hasDerivAt_thetaCuspFullLogExponentialJetZero hx).mul
    (hasDerivAt_thetaCuspFullLogFactorOne hx)
  unfold thetaCuspFullLogExponentialJetOne thetaCuspFullLogExponentialJetTwo
  convert h using 1 <;> (try funext y) <;>
    simp only [thetaCuspFullLogExponentialJetOne] <;> ring

private theorem hasDerivAt_thetaCuspFullLogExponentialJetTwo
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFullLogExponentialJetTwo
      (thetaCuspFullLogExponentialJetThree x) x := by
  have h0 := hasDerivAt_thetaCuspFullLogExponentialJetZero hx
  have h1 := hasDerivAt_thetaCuspFullLogFactorOne hx
  have h2 := hasDerivAt_thetaCuspFullLogFactorTwo hx
  have hcoeff := (h1.pow 2).add h2
  unfold thetaCuspFullLogExponentialJetTwo thetaCuspFullLogExponentialJetThree
  convert h0.mul hcoeff using 1 <;> (try funext y) <;>
    simp only [thetaCuspFullLogExponentialJetOne, Pi.add_apply, Pi.mul_apply,
      Pi.pow_apply] <;> ring

private theorem hasDerivAt_thetaCuspFullLogExponentialJetThree
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFullLogExponentialJetThree
      (thetaCuspFullLogExponentialJetFour x) x := by
  have h0 := hasDerivAt_thetaCuspFullLogExponentialJetZero hx
  have h1 := hasDerivAt_thetaCuspFullLogFactorOne hx
  have h2 := hasDerivAt_thetaCuspFullLogFactorTwo hx
  have h3 := hasDerivAt_thetaCuspFullLogFactorThree hx
  have hcoeff := ((h1.pow 3).add ((h1.mul h2).const_mul 3)).add h3
  unfold thetaCuspFullLogExponentialJetThree thetaCuspFullLogExponentialJetFour
  convert h0.mul hcoeff using 1 <;> (try funext y) <;>
    simp only [thetaCuspFullLogExponentialJetOne, Pi.add_apply, Pi.mul_apply,
      Pi.pow_apply] <;> ring

private theorem thetaCuspFullSource_eventuallyEq_logExponentialJetZero
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFullSource =ᶠ[nhds x] thetaCuspFullLogExponentialJetZero := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  have hpos := thetaCuspFullSource_pos_of_pos hy
  have hlog := thetaCuspLogSource_eventuallyEq_fullLogFactorZero hy
  have hvalue := hlog.self_of_nhds
  rw [thetaCuspFullLogExponentialJetZero, ← hvalue, thetaCuspLogSource,
    Real.exp_log hpos]

private theorem iteratedDeriv_one_thetaCuspFullSource_eq_logExponentialJet
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 1 thetaCuspFullSource x = thetaCuspFullLogExponentialJetOne x := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_thetaCuspFullLogExponentialJetZero hx |>.congr_of_eventuallyEq
    (thetaCuspFullSource_eventuallyEq_logExponentialJetZero hx)).deriv

private theorem iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 thetaCuspFullSource x = thetaCuspFullLogExponentialJetTwo x := by
  have heq : iteratedDeriv 1 thetaCuspFullSource =ᶠ[nhds x]
      thetaCuspFullLogExponentialJetOne := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_one_thetaCuspFullSource_eq_logExponentialJet hy
  rw [iteratedDeriv_succ]
  exact (hasDerivAt_thetaCuspFullLogExponentialJetOne hx |>.congr_of_eventuallyEq heq).deriv

private theorem iteratedDeriv_three_thetaCuspFullSource_eq_logExponentialJet
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 thetaCuspFullSource x = thetaCuspFullLogExponentialJetThree x := by
  have heq : iteratedDeriv 2 thetaCuspFullSource =ᶠ[nhds x]
      thetaCuspFullLogExponentialJetTwo := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet hy
  rw [iteratedDeriv_succ]
  exact (hasDerivAt_thetaCuspFullLogExponentialJetTwo hx |>.congr_of_eventuallyEq heq).deriv

private theorem iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 4 thetaCuspFullSource x = thetaCuspFullLogExponentialJetFour x := by
  have heq : iteratedDeriv 3 thetaCuspFullSource =ᶠ[nhds x]
      thetaCuspFullLogExponentialJetThree := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_three_thetaCuspFullSource_eq_logExponentialJet hy
  rw [iteratedDeriv_succ]
  exact (hasDerivAt_thetaCuspFullLogExponentialJetThree hx |>.congr_of_eventuallyEq heq).deriv

/-- Zeroth center jet of the reflected source product at a positive source coordinate. -/
def thetaCuspSourceReflectionJetZero (x : ℝ) : ℝ :=
  thetaCuspFullSource x ^ 2

/-- Second center jet of the reflected source product. -/
def thetaCuspSourceReflectionJetTwo (x : ℝ) : ℝ :=
  2 * (thetaCuspFullSource x * iteratedDeriv 2 thetaCuspFullSource x -
    iteratedDeriv 1 thetaCuspFullSource x ^ 2)

/-- Fourth center jet of the reflected source product. -/
def thetaCuspSourceReflectionJetFour (x : ℝ) : ℝ :=
  2 * thetaCuspFullSource x * iteratedDeriv 4 thetaCuspFullSource x -
    8 * iteratedDeriv 1 thetaCuspFullSource x *
      iteratedDeriv 3 thetaCuspFullSource x +
    6 * iteratedDeriv 2 thetaCuspFullSource x ^ 2

/-- Exact source connector from the fourth reflected-product Hankel determinant to the fourth and
second logarithmic source factors. -/
theorem thetaCuspSourceReflectionFourthHankel_eq_logFactors
    {x : ℝ} (hx : 0 < x) :
    thetaCuspSourceReflectionJetZero x * thetaCuspSourceReflectionJetFour x -
        thetaCuspSourceReflectionJetTwo x ^ 2 =
      2 * thetaCuspFullSource x ^ 4 *
        (thetaCuspFullLogFactorFour x + 4 * thetaCuspFullLogFactorTwo x ^ 2) := by
  have hsource : thetaCuspFullSource x = thetaCuspFullLogExponentialJetZero x := by
    exact (thetaCuspFullSource_eventuallyEq_logExponentialJetZero hx).self_of_nhds
  rw [thetaCuspSourceReflectionJetZero, thetaCuspSourceReflectionJetTwo,
    thetaCuspSourceReflectionJetFour, hsource,
    iteratedDeriv_one_thetaCuspFullSource_eq_logExponentialJet hx,
    iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet hx,
    iteratedDeriv_three_thetaCuspFullSource_eq_logExponentialJet hx,
    iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet hx]
  unfold thetaCuspFullLogExponentialJetOne thetaCuspFullLogExponentialJetTwo
    thetaCuspFullLogExponentialJetThree thetaCuspFullLogExponentialJetFour
  have hzero : 0 < thetaCuspFullLogExponentialJetZero x := by
    unfold thetaCuspFullLogExponentialJetZero
    positivity
  change
    thetaCuspFullLogExponentialJetZero x ^ 2 *
        HilbertMetric.reflectedProductFourthJet
          (thetaCuspFullLogExponentialJetZero x)
          (thetaCuspFullLogExponentialJetZero x * thetaCuspFullLogFactorOne x)
          (thetaCuspFullLogExponentialJetZero x *
            (thetaCuspFullLogFactorOne x ^ 2 + thetaCuspFullLogFactorTwo x))
          (thetaCuspFullLogExponentialJetZero x *
            (thetaCuspFullLogFactorOne x ^ 3 +
              3 * thetaCuspFullLogFactorOne x * thetaCuspFullLogFactorTwo x +
              thetaCuspFullLogFactorThree x))
          (thetaCuspFullLogExponentialJetZero x *
            (thetaCuspFullLogFactorOne x ^ 4 +
              6 * thetaCuspFullLogFactorOne x ^ 2 * thetaCuspFullLogFactorTwo x +
              3 * thetaCuspFullLogFactorTwo x ^ 2 +
              4 * thetaCuspFullLogFactorOne x * thetaCuspFullLogFactorThree x +
              thetaCuspFullLogFactorFour x)) -
      HilbertMetric.reflectedProductSecondJet
          (thetaCuspFullLogExponentialJetZero x)
          (thetaCuspFullLogExponentialJetZero x * thetaCuspFullLogFactorOne x)
          (thetaCuspFullLogExponentialJetZero x *
            (thetaCuspFullLogFactorOne x ^ 2 + thetaCuspFullLogFactorTwo x)) ^ 2 =
      2 * thetaCuspFullLogExponentialJetZero x ^ 4 *
        (thetaCuspFullLogFactorFour x + 4 * thetaCuspFullLogFactorTwo x ^ 2)
  exact HilbertMetric.reflectedProduct_fourthHankel_of_logJets hzero.ne'

/-- The reflected complete source has a strictly positive fourth Hankel determinant at every
positive source coordinate. -/
theorem thetaCuspSourceReflectionFourthHankel_pos
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspSourceReflectionJetZero x * thetaCuspSourceReflectionJetFour x -
      thetaCuspSourceReflectionJetTwo x ^ 2 := by
  have hlog := thetaCuspLogSource_fourthTuran_gt_one_hundred_sixty hx
  rw [iteratedDeriv_four_thetaCuspLogSource_eq_factor hx,
    iteratedDeriv_two_thetaCuspLogSource_eq_factor hx] at hlog
  rw [thetaCuspSourceReflectionFourthHankel_eq_logFactors hx]
  have hfactor : 0 < thetaCuspFullSource x ^ 4 :=
    pow_pos (thetaCuspFullSource_pos_of_pos hx) 4
  have hlog' : (160 : ℝ) < thetaCuspFullLogFactorFour x +
      4 * thetaCuspFullLogFactorTwo x ^ 2 := by
    simpa only [thetaCuspFullLogFactorFour, thetaCuspFirstAtomLogJetFour,
      thetaCuspFullLogFactorTwo, thetaCuspFirstAtomLogJetTwo] using hlog
  exact mul_pos (mul_pos (by norm_num) hfactor) (by linarith)

end

end RHTower
