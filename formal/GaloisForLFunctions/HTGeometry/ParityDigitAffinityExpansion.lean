import GaloisForLFunctions.HTGeometry.GeometricHellingerDigits

/-!
# The parity digit carries the whole quadratic Hellinger defect

For two geometric laws with ratios `a` and `b`, the Hellinger affinity of their parity digit is
`(1 + √(ab)) / √((1+a)(1+b))`.  Its logarithm is `−½(√a − √b)²` up to `O(a² + b²)`: the first-order
terms cancel exactly, because `√(ab) − a/2 − b/2 = −½(√a − √b)²`, and the second-order terms
collect into `(a − b)²/4`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Second-order Taylor bound for the logarithm on `|x| ≤ 3/4`. -/
theorem abs_log_one_add_taylor_le {x : ℝ} (h : |x| ≤ 3 / 4) :
    |Real.log (1 + x) - x + x ^ 2 / 2| ≤ 4 * |x| ^ 3 := by
  have hx : |(-x)| < 1 := by
    rw [abs_neg]; linarith
  have h2 := Real.abs_log_sub_add_sum_range_le hx 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h2
  have hsub : (1 : ℝ) - -x = 1 + x := by ring
  rw [hsub] at h2
  have hexpand : (0 : ℝ) + (-x) ^ (0 + 1) / ((0 : ℕ) + 1) + (-x) ^ (1 + 1) / ((1 : ℕ) + 1)
      + Real.log (1 + x) = Real.log (1 + x) - x + x ^ 2 / 2 := by
    push_cast
    ring
  rw [hexpand] at h2
  rw [abs_neg] at h2
  norm_num at h2
  refine le_trans h2 ?_
  have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hden : (1 : ℝ) / 4 ≤ 1 - |x| := by linarith
  have hpos : (0 : ℝ) < 1 - |x| := by linarith
  rw [div_le_iff₀ hpos]
  have hkey : (0 : ℝ) ≤ |x| ^ 3 * (4 * (1 - |x|) - 1) :=
    mul_nonneg (pow_nonneg habs 3) (by linarith)
  nlinarith [hkey]

/-- **The parity digit's affinity is `1 − ½(√a − √b)² + O(a² + b²)` in logarithm.** -/
theorem abs_log_bitHellingerAffinity_zero_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a ≤ 3 / 4) (hb' : b ≤ 3 / 4) :
    |Real.log (bitHellingerAffinity a b 0) + (Real.sqrt a - Real.sqrt b) ^ 2 / 2|
      ≤ 4 * (a ^ 2 + b ^ 2) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  set s : ℝ := Real.sqrt (a * b) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a * b := Real.sq_sqrt hab
  have hsle : s ≤ 3 / 4 := by
    have hle : a * b ≤ (3 / 4) ^ 2 := by nlinarith
    nlinarith [hs2, hs0]
  have hsqa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsqb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hsab : s = Real.sqrt a * Real.sqrt b := by
    rw [hsdef, Real.sqrt_mul ha]
  have hsqdiff : (Real.sqrt a - Real.sqrt b) ^ 2 = a - 2 * s + b := by
    rw [hsab]
    nlinarith [hsqa, hsqb]
  -- the affinity in logarithmic form
  have hbit : bitHellingerAffinity a b 0 = (1 + s) / Real.sqrt ((1 + a) * (1 + b)) := by
    rw [bitHellingerAffinity, hsdef]
    norm_num
  have hprodpos : (0 : ℝ) < (1 + a) * (1 + b) := by positivity
  have hlog : Real.log (bitHellingerAffinity a b 0)
      = Real.log (1 + s) - (1 / 2) * (Real.log (1 + a) + Real.log (1 + b)) := by
    rw [hbit, Real.log_div (by positivity) (ne_of_gt (Real.sqrt_pos.mpr hprodpos)),
      Real.log_sqrt hprodpos.le, Real.log_mul (by positivity) (by positivity)]
    ring
  -- the three Taylor bounds
  have hTs := abs_log_one_add_taylor_le (x := s) (by rw [abs_of_nonneg hs0]; exact hsle)
  have hTa := abs_log_one_add_taylor_le (x := a) (by rw [abs_of_nonneg ha]; exact ha')
  have hTb := abs_log_one_add_taylor_le (x := b) (by rw [abs_of_nonneg hb]; exact hb')
  rw [abs_of_nonneg hs0] at hTs
  rw [abs_of_nonneg ha] at hTa
  rw [abs_of_nonneg hb] at hTb
  -- the cubic bounds
  have hcs : s ^ 3 ≤ 3 / 8 * (a ^ 2 + b ^ 2) := by
    have h1 : s ^ 3 = s * s ^ 2 := by ring
    rw [h1, hs2]
    nlinarith [sq_nonneg (a - b), ha, hb, hs0, hsle]
  have hca : a ^ 3 ≤ 3 / 4 * a ^ 2 := by nlinarith [sq_nonneg a, ha]
  have hcb : b ^ 3 ≤ 3 / 4 * b ^ 2 := by nlinarith [sq_nonneg b, hb]
  -- assemble
  have hkey : Real.log (bitHellingerAffinity a b 0) + (Real.sqrt a - Real.sqrt b) ^ 2 / 2
      = (Real.log (1 + s) - s + s ^ 2 / 2)
        - (1 / 2) * (Real.log (1 + a) - a + a ^ 2 / 2)
        - (1 / 2) * (Real.log (1 + b) - b + b ^ 2 / 2)
        + (a - b) ^ 2 / 4 := by
    rw [hlog, hsqdiff, hs2]
    ring
  rw [hkey, abs_le]
  have hA1 := neg_abs_le (Real.log (1 + s) - s + s ^ 2 / 2)
  have hA2 := le_abs_self (Real.log (1 + s) - s + s ^ 2 / 2)
  have hB1 := neg_abs_le (Real.log (1 + a) - a + a ^ 2 / 2)
  have hB2 := le_abs_self (Real.log (1 + a) - a + a ^ 2 / 2)
  have hC1 := neg_abs_le (Real.log (1 + b) - b + b ^ 2 / 2)
  have hC2 := le_abs_self (Real.log (1 + b) - b + b ^ 2 / 2)
  have hD0 : (0 : ℝ) ≤ (a - b) ^ 2 / 4 := by positivity
  have hD1 : (a - b) ^ 2 / 4 ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a + b)]
  constructor <;> linarith [hTs, hTa, hTb, hcs, hca, hcb]

end GaloisForLFunctions.HTGeometry
