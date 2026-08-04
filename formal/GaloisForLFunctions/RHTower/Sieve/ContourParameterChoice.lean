import GaloisForLFunctions.RHTower.Sieve.EdgeBoundForm

/-!
# Choosing the contour parameter

The arithmetic parameter `K` controls two competing quantities: the edge bound grows like `log⁷K`,
and the saving is `exp(-c₀ log x / (16 log⁹K))`, which improves as `K` shrinks.  Balancing them at

    log K ≍ (log x)^{1/10}

makes the saving `exp(-κ (log x)^{1/10})`, which beats every power of `log K`.  The choice is
realised by

    contourParam x = ⌈ exp( (log x)^{1/10} ) ⌉₊,

whose logarithm is squeezed between `(log x)^{1/10}` and `(log x)^{1/10} + 1`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The arithmetic parameter attached to a cutoff of size `x`. -/
noncomputable def contourParam (x : ℝ) : ℕ := ⌈Real.exp ((Real.log x) ^ ((1 : ℝ) / 10))⌉₊

/-- The parameter is at least the exponential, so its logarithm is at least the exponent. -/
theorem le_log_contourParam (x : ℝ) :
    (Real.log x) ^ ((1 : ℝ) / 10) ≤ Real.log (contourParam x) := by
  have hexp : (0 : ℝ) < Real.exp ((Real.log x) ^ ((1 : ℝ) / 10)) := Real.exp_pos _
  have hle : Real.exp ((Real.log x) ^ ((1 : ℝ) / 10)) ≤ (contourParam x : ℝ) :=
    Nat.le_ceil _
  calc (Real.log x) ^ ((1 : ℝ) / 10)
      = Real.log (Real.exp ((Real.log x) ^ ((1 : ℝ) / 10))) := (Real.log_exp _).symm
    _ ≤ Real.log (contourParam x) := Real.log_le_log hexp hle

/-- The ceiling costs at most `1` in the logarithm. -/
theorem log_contourParam_le {x : ℝ} (hx : 0 ≤ Real.log x) :
    Real.log (contourParam x) ≤ (Real.log x) ^ ((1 : ℝ) / 10) + 1 := by
  set t : ℝ := (Real.log x) ^ ((1 : ℝ) / 10) with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hexp1 : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht0
  have hlt : ((contourParam x : ℕ) : ℝ) < Real.exp t + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (Real.exp_pos t))
  have hle2 : ((contourParam x : ℕ) : ℝ) ≤ 2 * Real.exp t := by linarith
  have hpos : (0 : ℝ) < ((contourParam x : ℕ) : ℝ) := by
    have := Real.exp_pos t
    have h0 : (0 : ℝ) < Real.exp t := this
    have hge : Real.exp t ≤ ((contourParam x : ℕ) : ℝ) := Nat.le_ceil _
    linarith
  calc Real.log (contourParam x) ≤ Real.log (2 * Real.exp t) := Real.log_le_log hpos hle2
    _ = Real.log 2 + t := by rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos t)),
        Real.log_exp]
    _ ≤ t + 1 := by
        have := Real.log_two_lt_d9
        linarith

/-- The tenth power recovers the logarithm. -/
theorem rpow_tenth_pow {x : ℝ} (hx : 0 ≤ Real.log x) :
    ((Real.log x) ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) = Real.log x := by
  rw [← Real.rpow_natCast ((Real.log x) ^ ((1 : ℝ) / 10)) 10, ← Real.rpow_mul hx]
  norm_num

/-- **The saving is at least an explicit power of the logarithm.**  With the balanced choice of `K`
the exponent `c₀ log x / (16 log⁹K)` is at least `c₀ (log x)^{1/10} / 8192`. -/
theorem le_saving_exponent {x : ℝ} (hx : 1 ≤ Real.log x) :
    zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192
      ≤ zeroFreeConst / (16 * (Real.log (contourParam x)) ^ 9) * Real.log x := by
  have hx0 : (0 : ℝ) ≤ Real.log x := by linarith
  set t : ℝ := (Real.log x) ^ ((1 : ℝ) / 10) with htdef
  have ht1 : 1 ≤ t := by
    rw [htdef]
    exact Real.one_le_rpow hx (by norm_num)
  have ht0 : (0 : ℝ) < t := by linarith
  have hten : t ^ (10 : ℕ) = Real.log x := rpow_tenth_pow hx0
  have hL : Real.log (contourParam x) ≤ t + 1 := log_contourParam_le hx0
  have hL0 : 0 < Real.log (contourParam x) := lt_of_lt_of_le ht0 (le_log_contourParam x)
  have hL2 : Real.log (contourParam x) ≤ 2 * t := by linarith
  have h9 : (Real.log (contourParam x)) ^ 9 ≤ 512 * t ^ 9 := by
    calc (Real.log (contourParam x)) ^ 9 ≤ (2 * t) ^ 9 := by gcongr
      _ = 512 * t ^ 9 := by ring
  have h9pos : (0 : ℝ) < (Real.log (contourParam x)) ^ 9 := by positivity
  have hA0 := zeroFreeConst_pos
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
  have hexpand : zeroFreeConst * Real.log x = zeroFreeConst * (t * t ^ 9) := by
    rw [show t * t ^ 9 = t ^ (10 : ℕ) by ring, hten]
  rw [hexpand]
  have hkey := mul_le_mul_of_nonneg_left h9 (le_of_lt (mul_pos hA0 ht0))
  linarith [hkey]

end RHTower.Sieve
