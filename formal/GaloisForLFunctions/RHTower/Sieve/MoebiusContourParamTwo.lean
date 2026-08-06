import GaloisForLFunctions.RHTower.Sieve.MoebiusSavingKappaTwo

/-!
# Choosing the contour parameter at the width-`log^{-2}` rectangle

The parameter `K` controls two competing quantities: the left edge saves
`exp(-log x / log²K)`, which improves as `K` shrinks, while the truncation error carries
`x^{1/log²K}/K`, which improves as `K` grows.  Balancing them at

    log K ≍ (log x)^{1/3}

makes both `exp(-c (log x)^{1/3})`.  The choice is realised by

    contourParamTwo x = ⌈ exp( 2 (log x)^{1/3} ) ⌉₊,

whose logarithm is squeezed between `2(log x)^{1/3}` and `2(log x)^{1/3} + 1`.  The factor `2` is
what separates the two sides: at `log K = (log x)^{1/3}` exactly they cancel and nothing is saved.

The exponent `1/3` is forced by the square in the rectangle's half-width, exactly as the exponent
`1/10` of `contourParam` is forced by the ninth power there.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The arithmetic parameter attached to a cutoff of size `x`. -/
noncomputable def contourParamTwo (x : ℝ) : ℕ := ⌈Real.exp (2 * (Real.log x) ^ ((1 : ℝ) / 3))⌉₊

/-- The cube recovers the logarithm. -/
theorem rpow_third_pow {x : ℝ} (hx : 0 ≤ Real.log x) :
    ((Real.log x) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = Real.log x := by
  rw [← Real.rpow_natCast ((Real.log x) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hx]
  norm_num

/-- The parameter is at least the exponential. -/
theorem exp_le_contourParamTwo (x : ℝ) :
    Real.exp (2 * (Real.log x) ^ ((1 : ℝ) / 3)) ≤ (contourParamTwo x : ℝ) := Nat.le_ceil _

/-- Hence its logarithm is at least the exponent. -/
theorem le_log_contourParamTwo (x : ℝ) :
    2 * (Real.log x) ^ ((1 : ℝ) / 3) ≤ Real.log (contourParamTwo x) := by
  have hexp : (0 : ℝ) < Real.exp (2 * (Real.log x) ^ ((1 : ℝ) / 3)) := Real.exp_pos _
  calc 2 * (Real.log x) ^ ((1 : ℝ) / 3)
      = Real.log (Real.exp (2 * (Real.log x) ^ ((1 : ℝ) / 3))) := (Real.log_exp _).symm
    _ ≤ Real.log (contourParamTwo x) := Real.log_le_log hexp (exp_le_contourParamTwo x)

/-- The ceiling costs at most `1` in the logarithm. -/
theorem log_contourParamTwo_le {x : ℝ} (hx : 0 ≤ Real.log x) :
    Real.log (contourParamTwo x) ≤ 2 * (Real.log x) ^ ((1 : ℝ) / 3) + 1 := by
  set t : ℝ := (Real.log x) ^ ((1 : ℝ) / 3) with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hlt : ((contourParamTwo x : ℕ) : ℝ) < Real.exp (2 * t) + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (Real.exp_pos _))
  have hexp1 : (1 : ℝ) ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
  have hle2 : ((contourParamTwo x : ℕ) : ℝ) ≤ 2 * Real.exp (2 * t) := by linarith
  have hpos : (0 : ℝ) < ((contourParamTwo x : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) (exp_le_contourParamTwo x)
  calc Real.log (contourParamTwo x) ≤ Real.log (2 * Real.exp (2 * t)) :=
        Real.log_le_log hpos hle2
    _ = Real.log 2 + 2 * t := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    _ ≤ 2 * t + 1 := by
        have := Real.log_two_lt_d9
        linarith

/-- The logarithm of the parameter, squeezed on both sides by multiples of `(log x)^{1/3}`. -/
theorem log_contourParamTwo_le_three {x : ℝ} (hx : 1 ≤ Real.log x) :
    Real.log (contourParamTwo x) ≤ 3 * (Real.log x) ^ ((1 : ℝ) / 3) := by
  have hx0 : (0 : ℝ) ≤ Real.log x := by linarith
  have ht1 : (1 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 3) := Real.one_le_rpow hx (by norm_num)
  have := log_contourParamTwo_le hx0
  linarith

/-- **The left edge's saving at the balanced parameter.**  The exponent
`log x / log²K` is at least `(log x)^{1/3}/9`. -/
theorem le_saving_exponent_two {x : ℝ} (hx : 1 ≤ Real.log x) :
    (Real.log x) ^ ((1 : ℝ) / 3) / 9
      ≤ 1 / (Real.log (contourParamTwo x)) ^ 2 * Real.log x := by
  have hx0 : (0 : ℝ) ≤ Real.log x := by linarith
  set t : ℝ := (Real.log x) ^ ((1 : ℝ) / 3) with htdef
  have ht1 : (1 : ℝ) ≤ t := by rw [htdef]; exact Real.one_le_rpow hx (by norm_num)
  have ht0 : (0 : ℝ) < t := by linarith
  have hcube : t ^ (3 : ℕ) = Real.log x := rpow_third_pow hx0
  have hLlow : 2 * t ≤ Real.log (contourParamTwo x) := le_log_contourParamTwo x
  have hL0 : (0 : ℝ) < Real.log (contourParamTwo x) := by linarith
  have hLhi : Real.log (contourParamTwo x) ≤ 3 * t := log_contourParamTwo_le_three hx
  have hLsq : (Real.log (contourParamTwo x)) ^ 2 ≤ 9 * t ^ 2 := by nlinarith
  have hLsq0 : (0 : ℝ) < (Real.log (contourParamTwo x)) ^ 2 := by positivity
  rw [one_div, inv_mul_eq_div, div_le_div_iff₀ (by norm_num) hLsq0]
  have hexpand : Real.log x * 9 = 9 * (t * t ^ 2) := by
    rw [show t * t ^ 2 = t ^ (3 : ℕ) by ring, hcube]; ring
  rw [hexpand]
  nlinarith [hLsq, ht0]

/-- **The truncation side at the balanced parameter.**  The growth `x^{1/log²K}` of the right line
is beaten by the parameter itself, with `exp(-(7/4)(log x)^{1/3})` to spare. -/
theorem exp_saving_right_two {x : ℝ} (hx : 1 ≤ Real.log x) :
    Real.exp (1 / (Real.log (contourParamTwo x)) ^ 2 * Real.log x)
      ≤ Real.exp (-(7 / 4) * (Real.log x) ^ ((1 : ℝ) / 3)) * (contourParamTwo x : ℝ) := by
  have hx0 : (0 : ℝ) ≤ Real.log x := by linarith
  set t : ℝ := (Real.log x) ^ ((1 : ℝ) / 3) with htdef
  have ht1 : (1 : ℝ) ≤ t := by rw [htdef]; exact Real.one_le_rpow hx (by norm_num)
  have ht0 : (0 : ℝ) < t := by linarith
  have hcube : t ^ (3 : ℕ) = Real.log x := rpow_third_pow hx0
  have hLlow : 2 * t ≤ Real.log (contourParamTwo x) := le_log_contourParamTwo x
  have hL0 : (0 : ℝ) < Real.log (contourParamTwo x) := by linarith
  have hLsq : 4 * t ^ 2 ≤ (Real.log (contourParamTwo x)) ^ 2 := by nlinarith
  have hLsq0 : (0 : ℝ) < (Real.log (contourParamTwo x)) ^ 2 := by positivity
  -- the exponent is at most `t/4`
  have hexp : 1 / (Real.log (contourParamTwo x)) ^ 2 * Real.log x ≤ t / 4 := by
    rw [one_div, inv_mul_eq_div, div_le_div_iff₀ hLsq0 (by norm_num)]
    have hexpand : Real.log x * 4 = 4 * (t * t ^ 2) := by
      rw [show t * t ^ 2 = t ^ (3 : ℕ) by ring, hcube]; ring
    rw [hexpand]
    nlinarith [hLsq, ht0]
  have hnum : Real.exp (1 / (Real.log (contourParamTwo x)) ^ 2 * Real.log x)
      ≤ Real.exp (t / 4) := Real.exp_le_exp.mpr hexp
  have hden : Real.exp (2 * t) ≤ (contourParamTwo x : ℝ) := exp_le_contourParamTwo x
  have hA : Real.exp (-(7 / 4) * t) * Real.exp (2 * t) = Real.exp (t / 4) := by
    rw [← Real.exp_add]
    ring_nf
  have hB : Real.exp (-(7 / 4) * t) * Real.exp (2 * t)
      ≤ Real.exp (-(7 / 4) * t) * (contourParamTwo x : ℝ) :=
    mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
  linarith [hnum, hA, hB]

end RHTower.Sieve
