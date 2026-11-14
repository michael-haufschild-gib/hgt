import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper
import GaloisForLFunctions.ArithmeticCriticalityTheory.CurvedGaugeArchimedeanBounds
import GaloisForLFunctions.RHTower.WeilLevyPoleGaussModeCancellation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan


/-!
# Gamma mass at the prime-three boundary

At diameter `log 3`, the Gamma tail is `log(2+√3)/2+π/6`.
Rational exponential estimates bound the normalized mass coefficient
below by `−4546/2500`.
-/

noncomputable section
open Real
namespace GaloisForLFunctions.WindowTowerOfSpecZ

/-- The corrected harmonic estimate at `64` gives a rational upper bound for Euler's constant. -/
theorem eulerMascheroniConstant_lt_577215667_div_1000000000 :
    Real.eulerMascheroniConstant < (577215667 / 1000000000 : ℝ) := by
  have h := _root_.RHTower.eulerMascheroniConstant_lt_secondUpper (n := 64) (by norm_num)
  have hlog : Real.log ((64 : ℕ) : ℝ) = 6 * Real.log 2 := by
    rw [show ((64 : ℕ) : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [_root_.RHTower.eulerMascheroniSecondUpper, if_neg (by norm_num),
    Real.eulerMascheroniSeq', if_neg (by norm_num), hlog] at h
  have hH : ((harmonic 64 : ℚ) : ℝ) - 6 * (6931471803 / 10000000000) -
      1 / (2 * 64) + 1 / (12 * 64 ^ 2) < (577215667 / 1000000000 : ℝ) := by
    norm_num [harmonic, Finset.sum_range_succ]
  norm_num at h
  linarith only [h, hH, Real.log_two_gt_d9]

/-- A finite exponential lower bound certifies an upper bound for `log π`. -/
theorem log_pi_le_114472989_div_100000000 :
    Real.log Real.pi ≤ (114472989 / 100000000 : ℝ) := by
  let x : ℝ := (114472989 / 100000000) / 2
  let q : ℝ := (∑ n ∈ Finset.range 11, x ^ n / (n.factorial : ℝ)) -
    x ^ 11 / 30000000
  have hx0 : 0 ≤ x := by norm_num [x]
  have hp := Real.exp_bound (x := x) (by norm_num [x]) (n := 11) (by norm_num)
  rw [abs_of_nonneg hx0] at hp
  have htail : x ^ 11 * ((11 + 1 : ℝ) / ((11 : ℕ).factorial * 11)) ≤
      x ^ 11 / 30000000 := by
    norm_num
  have hq : q ≤ Real.exp x := by
    have h := (abs_le.mp hp).1
    norm_num only [Nat.reduceSucc, Nat.cast_ofNat] at h
    dsimp only [q]
    linarith only [h, htail]
  have hr : (1772453851 / 1000000000 : ℝ) ≤ q := by
    norm_num [q, x, Finset.sum_range_succ, Nat.factorial]
  have hpi : Real.pi ≤ (1772453851 / 1000000000 : ℝ) ^ 2 :=
    Real.pi_lt_d20.le.trans (by norm_num)
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1772453851 / 1000000000)
    (hr.trans hq) 2
  rw [← Real.exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat] at he hpi
  have hl := Real.log_le_log Real.pi_pos (hpi.trans he)
  simpa only [Real.log_exp] using hl

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.eulerMascheroniConstant_lt_577215667_div_1000000000
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.log_pi_le_114472989_div_100000000

namespace GaloisForLFunctions.WindowTowerOfSpecZ
open _root_.RHTower.WeilLevyPoleGauss

/-- At `log 3`, the Gamma tail has an exact logarithmic and circular decomposition. -/
theorem archLevyAntideriv_log_three :
    archLevyAntideriv (Real.log 3) = Real.log (2 + Real.sqrt 3) / 2 + Real.pi / 6 := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have he : 0 < Real.exp (-Real.log 3 / 2) := Real.exp_pos _
  have he2 : Real.exp (-Real.log 3 / 2) ^ 2 = (1 / 3 : ℝ) := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-Real.log 3 / 2) = -Real.log 3 by ring,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hsq : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have her : Real.exp (-Real.log 3 / 2) = Real.sqrt 3 / 3 := by
    nlinarith only [he, he2, hs, hs0]
  have hei : Real.exp (-Real.log 3 / 2) = (Real.sqrt 3)⁻¹ := by
    rw [her]
    field_simp [hsq.ne']
    nlinarith only [hs]
  have hden : 0 < 1 - Real.exp (-Real.log 3 / 2) := by
    have h := Real.exp_lt_one_iff.mpr (show -Real.log 3 / 2 < 0 by linarith only [hlog])
    linarith only [h]
  have hratio : (1 + Real.exp (-Real.log 3 / 2)) /
      (1 - Real.exp (-Real.log 3 / 2)) = 2 + Real.sqrt 3 := by
    apply (div_eq_iff hden.ne').mpr
    rw [her]
    nlinarith only [hs]
  rw [archLevyAntideriv_eq_log_div hlog, hratio, hei, Real.arctan_inv_sqrt_three]
  ring

private theorem log_two_add_sqrt_three_lower :
    (1316957 / 1000000 : ℝ) ≤ Real.log (2 + Real.sqrt 3) := by
  let x : ℝ := (1316957 / 1000000) / 2
  let q : ℝ := (∑ n ∈ Finset.range 12, x ^ n / (n.factorial : ℝ)) +
    x ^ 12 / 400000000
  have hx0 : 0 ≤ x := by norm_num [x]
  have hp := Real.exp_bound (x := x) (by norm_num [x]) (n := 12) (by norm_num)
  rw [abs_of_nonneg hx0] at hp
  have htail : x ^ 12 * ((12 + 1 : ℝ) / ((12 : ℕ).factorial * 12)) ≤
      x ^ 12 / 400000000 := by
    norm_num
  have hq : Real.exp x ≤ q := by
    have h := (abs_le.mp hp).2
    norm_num only [Nat.reduceSucc, Nat.cast_ofNat] at h
    dsimp only [q]
    linarith only [h, htail]
  have hr : q ≤ (1931851 / 1000000 : ℝ) := by
    norm_num [q, x, Finset.sum_range_succ, Nat.factorial]
  have hs : (1732050 / 1000000 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have he := pow_le_pow_left₀ (Real.exp_pos x).le (hq.trans hr) 2
  rw [← Real.exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat] at he
  have hu : Real.exp (1316957 / 1000000 : ℝ) ≤ 2 + Real.sqrt 3 := by
    linarith only [he, hs]
  have hl := Real.log_le_log (Real.exp_pos _) hu
  simpa only [Real.log_exp] using hl

/-- The normalized Gamma mass coefficient at aperture `log(3)/2` is at least `−4546/2500`. -/
theorem gamma_mass_constant_at_aperture_log_three_half :
    -(4546 / 2500 : ℝ) ≤ Zeta23.EF.gammaBracket 0 + Real.log 2 + Real.log 3 / 2 -
      (Real.log 3) ^ 2 / 48 - (Real.log 3) ^ 3 / 48 +
      2 * archLevyAntideriv (Real.log 3) := by
  rw [archLevyAntideriv_log_three]
  have hlog : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
  have h2 := pow_le_pow_left₀ hlog Real.log_three_lt_d9.le 2
  have h3 := pow_le_pow_left₀ hlog Real.log_three_lt_d9.le 3
  have hbr := neg_gammaBracket_zero_eq
  have hg := eulerMascheroniConstant_lt_577215667_div_1000000000
  have hp := log_pi_le_114472989_div_100000000
  have hl := log_two_add_sqrt_three_lower
  linarith only [h2, h3, hbr, hg, hp, hl, Real.log_two_lt_d9,
    Real.log_three_gt_d9, Real.pi_lt_d6]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.archLevyAntideriv_log_three
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gamma_mass_constant_at_aperture_log_three_half
