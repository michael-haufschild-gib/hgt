import GaloisForLFunctions.RHTower.ThetaCuspReflectionFourthTuran

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
      have hproduct := mul_lt_mul_of_nonneg hpi2 hsum hsum0 (by positivity)
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
      have hproduct := mul_lt_mul_of_nonneg hpi3 hsum hsum0 (by positivity)
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
    change Real.pi * ((1 : ℝ) * Real.exp x) ^ 2 = A
    dsimp [A, thetaCuspLogConcavityScale]
    ring
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
