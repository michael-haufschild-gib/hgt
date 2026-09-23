import GaloisForLFunctions.HTGeometry.ParityDigitAffinityExpansion

/-!
# The quadratic expansion of the geometric Hellinger affinity

The full geometric affinity has the same quadratic Hellinger defect as its parity digit: with
`s = √(ab)`,

`log H^geo(a,b) = ½ log(1-a) + ½ log(1-b) - log(1-s)
                = -½ (√a - √b)² - ¼ (a-b)² + O(a³ + b³ + s³)`,

because `s - a/2 - b/2 = -½ (√a - √b)²` is exactly the same first-order cancellation that governs
the parity digit.  Consequently the two affinities agree to second order and, at the critical
prime scaling, have the same all-prime limit.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The geometric affinity is `1 − ½(√a − √b)² + O(a² + b²)` in logarithm.** -/
theorem abs_log_geometricHellingerAffinity_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a ≤ 3 / 4) (hb' : b ≤ 3 / 4) :
    |Real.log (geometricHellingerAffinity a b) + (Real.sqrt a - Real.sqrt b) ^ (2 : ℕ) / 2|
      ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  set s : ℝ := Real.sqrt (a * b) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ (2 : ℕ) = a * b := Real.sq_sqrt hab
  have hsle : s ≤ 3 / 4 := by
    have hle : a * b ≤ (3 / 4 : ℝ) ^ (2 : ℕ) := by nlinarith
    nlinarith [hs2, hs0]
  have hsqa : Real.sqrt a ^ (2 : ℕ) = a := Real.sq_sqrt ha
  have hsqb : Real.sqrt b ^ (2 : ℕ) = b := Real.sq_sqrt hb
  have hsab : s = Real.sqrt a * Real.sqrt b := by rw [hsdef, Real.sqrt_mul ha]
  have hsqdiff : (Real.sqrt a - Real.sqrt b) ^ (2 : ℕ) = a - 2 * s + b := by
    rw [hsab]; nlinarith [hsqa, hsqb]
  clear_value s
  clear hsab hsqa hsqb
  have hA : (0 : ℝ) < 1 - a := by linarith
  have hB : (0 : ℝ) < 1 - b := by linarith
  have hS : (0 : ℝ) < 1 - s := by linarith
  -- the logarithm of the affinity splits
  have hsplit : Real.log (geometricHellingerAffinity a b)
      = (Real.log (1 - a) + Real.log (1 - b)) / 2 - Real.log (1 - s) := by
    rw [geometricHellingerAffinity, ← hsdef, Real.log_div (by positivity) (by linarith),
      Real.log_sqrt (by positivity), Real.log_mul (by linarith) (by linarith)]
  -- second-order Taylor for each logarithm
  have hEa := abs_log_one_add_taylor_le (x := -a) (by rw [abs_neg, abs_of_nonneg ha]; linarith)
  have hEb := abs_log_one_add_taylor_le (x := -b) (by rw [abs_neg, abs_of_nonneg hb]; linarith)
  have hEs := abs_log_one_add_taylor_le (x := -s) (by rw [abs_neg, abs_of_nonneg hs0]; linarith)
  rw [show (1 : ℝ) + -a = 1 - a by ring, abs_neg, abs_of_nonneg ha] at hEa
  rw [show (1 : ℝ) + -b = 1 - b by ring, abs_neg, abs_of_nonneg hb] at hEb
  rw [show (1 : ℝ) + -s = 1 - s by ring, abs_neg, abs_of_nonneg hs0] at hEs
  set Ea : ℝ := Real.log (1 - a) + a + a ^ (2 : ℕ) / 2 with hEadef
  set Eb : ℝ := Real.log (1 - b) + b + b ^ (2 : ℕ) / 2 with hEbdef
  set Es : ℝ := Real.log (1 - s) + s + s ^ (2 : ℕ) / 2 with hEsdef
  have hEa' : |Ea| ≤ 4 * a ^ (3 : ℕ) := by
    rw [hEadef]
    have : Real.log (1 - a) - -a + (-a) ^ (2 : ℕ) / 2 = Real.log (1 - a) + a + a ^ (2 : ℕ) / 2 := by ring
    rw [← this]
    exact hEa
  have hEb' : |Eb| ≤ 4 * b ^ (3 : ℕ) := by
    rw [hEbdef]
    have : Real.log (1 - b) - -b + (-b) ^ (2 : ℕ) / 2 = Real.log (1 - b) + b + b ^ (2 : ℕ) / 2 := by ring
    rw [← this]
    exact hEb
  have hEs' : |Es| ≤ 4 * s ^ (3 : ℕ) := by
    rw [hEsdef]
    have : Real.log (1 - s) - -s + (-s) ^ (2 : ℕ) / 2 = Real.log (1 - s) + s + s ^ (2 : ℕ) / 2 := by ring
    rw [← this]
    exact hEs
  -- the exact algebraic identity
  have hkey : Real.log (geometricHellingerAffinity a b) + (Real.sqrt a - Real.sqrt b) ^ (2 : ℕ) / 2
      = -((a - b) ^ (2 : ℕ) / 4) + (Ea + Eb) / 2 - Es := by
    rw [hsplit, hsqdiff, hEadef, hEbdef, hEsdef]
    linear_combination hs2 / 2
  rw [hkey]
  clear_value Ea Eb Es
  clear hEadef hEbdef hEsdef hsplit hEa hEb hEs hkey
  -- and the majorants
  have hcube_a : a ^ (3 : ℕ) ≤ a ^ (2 : ℕ) := by nlinarith
  have hcube_b : b ^ (3 : ℕ) ≤ b ^ (2 : ℕ) := by nlinarith
  have hcube_s : s ^ (3 : ℕ) ≤ 3 / 8 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
    have h1 : s ^ (3 : ℕ) = s * (a * b) := by rw [show s ^ (3 : ℕ) = s * s ^ (2 : ℕ) by ring, hs2]
    have h2 : a * b ≤ (a ^ (2 : ℕ) + b ^ (2 : ℕ)) / 2 := by nlinarith [sq_nonneg (a - b)]
    have h3 : s * (a * b) ≤ 3 / 4 * (a * b) := mul_le_mul_of_nonneg_right hsle hab
    rw [h1]
    linarith
  have hquad : (a - b) ^ (2 : ℕ) / 4 ≤ (a ^ (2 : ℕ) + b ^ (2 : ℕ)) / 2 := by nlinarith [sq_nonneg (a + b)]
  have hbound : |(-((a - b) ^ (2 : ℕ) / 4) + (Ea + Eb) / 2 - Es)|
      ≤ (a - b) ^ (2 : ℕ) / 4 + (|Ea| + |Eb|) / 2 + |Es| := by
    have h1 : |(-((a - b) ^ (2 : ℕ) / 4) + (Ea + Eb) / 2 - Es)|
        ≤ |(-((a - b) ^ (2 : ℕ) / 4) + (Ea + Eb) / 2)| + |Es| := abs_sub _ _
    have h2 : |(-((a - b) ^ (2 : ℕ) / 4) + (Ea + Eb) / 2)|
        ≤ |(-((a - b) ^ (2 : ℕ) / 4))| + |(Ea + Eb) / 2| := abs_add_le _ _
    have h3 : |(-((a - b) ^ (2 : ℕ) / 4))| = (a - b) ^ (2 : ℕ) / 4 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
    have h4 : |(Ea + Eb) / 2| ≤ (|Ea| + |Eb|) / 2 := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have := abs_add_le Ea Eb
      linarith
    linarith
  refine le_trans hbound ?_
  linarith

end GaloisForLFunctions.HTGeometry
