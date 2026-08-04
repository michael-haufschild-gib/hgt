import GaloisForLFunctions.RHTower.BandKaiserTrial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The two mass bounds for the Kaiser–Bessel trial

The band transform of the Kaiser–Bessel trial is the odd-factorial series
`sum_m 2 (c² - omega²)^m/(2m+1)!`, which is elementary on both sides of the band edge:

```text
|omega| < c :  2 sinh(sqrt(c² - omega²))/sqrt(c² - omega²),
|omega| > c :  2 sin(sqrt(omega² - c²))/sqrt(omega² - c²).
```

Inside the band the series has positive terms, so it is monotone in `c² - omega²`: on the inner band
`|omega| <= 1` it is bounded below by its value at `c² - 1`, which grows like `e^c/c`.  Outside the
band the sine form gives `|transform| <= 2 min(1, 1/sqrt(omega² - c²))`, whose square has a
logarithmically small tail integral.  These are the two mass bounds of the concentration ratio, and
their quotient is what produces the leakage envelope at the exponential rate `e^(-2c)`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral

/-- The odd-factorial series with a positive argument is the hyperbolic sine quotient. -/
theorem tsum_oddFactorial_sinh {v : ℝ} (hv : v ≠ 0) :
    (∑' m : ℕ, 2 * (v ^ 2) ^ m / (Nat.factorial (2 * m + 1) : ℝ))
      = 2 * Real.sinh v / v := by
  have hterm : ∀ m : ℕ, 2 * (v ^ 2) ^ m / (Nat.factorial (2 * m + 1) : ℝ)
      = (2 / v) * (v ^ (2 * m + 1) / (Nat.factorial (2 * m + 1) : ℝ)) := by
    intro m
    have hpow : (v ^ 2) ^ m = v ^ (2 * m) := (pow_mul v 2 m).symm
    have hfacpos : (0 : ℝ) < (Nat.factorial (2 * m + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    rw [hpow, pow_succ]
    field_simp
  rw [tsum_congr hterm, tsum_mul_left, ← Real.sinh_eq_tsum]
  ring

/-- The odd-factorial series with a negative argument is the sine quotient. -/
theorem tsum_oddFactorial_sin {u : ℝ} (hu : u ≠ 0) :
    (∑' m : ℕ, 2 * (-(u ^ 2)) ^ m / (Nat.factorial (2 * m + 1) : ℝ))
      = 2 * Real.sin u / u := by
  have hterm : ∀ m : ℕ, 2 * (-(u ^ 2)) ^ m / (Nat.factorial (2 * m + 1) : ℝ)
      = (2 / u) * ((-1) ^ m * u ^ (2 * m + 1) / (Nat.factorial (2 * m + 1) : ℝ)) := by
    intro m
    have hpow : (-(u ^ 2)) ^ m = (-1) ^ m * u ^ (2 * m) := by
      rw [show -(u ^ 2) = (-1) * u ^ 2 by ring, mul_pow, ← pow_mul]
    have hfacpos : (0 : ℝ) < (Nat.factorial (2 * m + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    rw [hpow, pow_succ]
    field_simp
  rw [tsum_congr hterm, tsum_mul_left, ← Real.sin_eq_tsum]
  ring

/-! ## The closed forms of the trial transform -/

/-- **Inside the band** the trial transform is a hyperbolic sine quotient. -/
theorem integral_kaiserTrial_cos_of_lt {c ω : ℝ} (h : ω ^ 2 < c ^ 2) :
    (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x))
      = 2 * Real.sinh (Real.sqrt (c ^ 2 - ω ^ 2)) / Real.sqrt (c ^ 2 - ω ^ 2) := by
  have hpos : 0 < c ^ 2 - ω ^ 2 := by linarith
  set v : ℝ := Real.sqrt (c ^ 2 - ω ^ 2) with hvdef
  have hvpos : 0 < v := Real.sqrt_pos.mpr hpos
  have hvsq : v ^ 2 = c ^ 2 - ω ^ 2 := Real.sq_sqrt hpos.le
  rw [integral_kaiserTrial_cos c ω, ← hvsq, tsum_oddFactorial_sinh (ne_of_gt hvpos)]

/-- **Outside the band** the trial transform is a sine quotient. -/
theorem integral_kaiserTrial_cos_of_gt {c ω : ℝ} (h : c ^ 2 < ω ^ 2) :
    (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x))
      = 2 * Real.sin (Real.sqrt (ω ^ 2 - c ^ 2)) / Real.sqrt (ω ^ 2 - c ^ 2) := by
  have hpos : 0 < ω ^ 2 - c ^ 2 := by linarith
  have hupos : 0 < Real.sqrt (ω ^ 2 - c ^ 2) := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt (ω ^ 2 - c ^ 2) ^ 2 = ω ^ 2 - c ^ 2 := Real.sq_sqrt hpos.le
  have hneg : c ^ 2 - ω ^ 2 = -(Real.sqrt (ω ^ 2 - c ^ 2) ^ 2) := by
    rw [hsq]
    ring
  rw [integral_kaiserTrial_cos c ω, hneg, tsum_oddFactorial_sin (ne_of_gt hupos)]

/-! ## The tail bound -/

/-- **The tail bound.**  Beyond the band edge the trial transform is at most `2` in absolute value and
decays like `2/sqrt(omega² - c²)`. -/
theorem abs_integral_kaiserTrial_cos_le {c ω : ℝ} (h : c ^ 2 < ω ^ 2) :
    |∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x)|
      ≤ min 2 (2 / Real.sqrt (ω ^ 2 - c ^ 2)) := by
  have hpos : 0 < ω ^ 2 - c ^ 2 := by linarith
  have hupos : 0 < Real.sqrt (ω ^ 2 - c ^ 2) := Real.sqrt_pos.mpr hpos
  rw [integral_kaiserTrial_cos_of_gt h]
  have habs : |2 * Real.sin (Real.sqrt (ω ^ 2 - c ^ 2)) / Real.sqrt (ω ^ 2 - c ^ 2)|
      = 2 * |Real.sin (Real.sqrt (ω ^ 2 - c ^ 2))| / Real.sqrt (ω ^ 2 - c ^ 2) := by
    rw [abs_div, abs_mul, abs_of_pos hupos]
    norm_num
  rw [habs]
  refine le_min ?_ ?_
  · -- `|sin u| <= u` for positive `u`
    have hsin : |Real.sin (Real.sqrt (ω ^ 2 - c ^ 2))| ≤ Real.sqrt (ω ^ 2 - c ^ 2) := by
      have h := Real.abs_sin_le_abs (x := Real.sqrt (ω ^ 2 - c ^ 2))
      rwa [abs_of_pos hupos] at h
    rw [div_le_iff₀ hupos]
    nlinarith [hsin, hupos]
  · have hsin : |Real.sin (Real.sqrt (ω ^ 2 - c ^ 2))| ≤ 1 := Real.abs_sin_le_one _
    gcongr
    linarith

/-! ## The inner-band lower bound -/

/-- The odd-factorial series is monotone in its argument. -/
theorem tsum_oddFactorial_mono {z w : ℝ} (hz : 0 ≤ z) (hzw : z ≤ w) :
    (∑' m : ℕ, 2 * z ^ m / (Nat.factorial (2 * m + 1) : ℝ))
      ≤ ∑' m : ℕ, 2 * w ^ m / (Nat.factorial (2 * m + 1) : ℝ) := by
  refine Summable.tsum_le_tsum (fun m => ?_) (summable_oddFactorial_pow z)
    (summable_oddFactorial_pow w)
  have hfacpos : (0 : ℝ) < (Nat.factorial (2 * m + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  gcongr

/-- **The inner-band lower bound.**  On `|omega| <= 1` the trial transform is at least its value at
the band edge parameter `c² - 1`, which is `2 sinh(sqrt(c²-1))/sqrt(c²-1)`. -/
theorem integral_kaiserTrial_cos_ge {c ω : ℝ} (hc : 1 < c ^ 2) (hω : ω ^ 2 ≤ 1) :
    2 * Real.sinh (Real.sqrt (c ^ 2 - 1)) / Real.sqrt (c ^ 2 - 1)
      ≤ ∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x) := by
  have hpos1 : 0 < c ^ 2 - 1 := by linarith
  set v : ℝ := Real.sqrt (c ^ 2 - 1) with hvdef
  have hvpos : 0 < v := Real.sqrt_pos.mpr hpos1
  have hvsq : v ^ 2 = c ^ 2 - 1 := Real.sq_sqrt hpos1.le
  have hmono := tsum_oddFactorial_mono (z := c ^ 2 - 1) (w := c ^ 2 - ω ^ 2) hpos1.le (by linarith)
  rw [integral_kaiserTrial_cos c ω]
  refine le_trans ?_ hmono
  rw [← hvsq, tsum_oddFactorial_sinh (ne_of_gt hvpos)]

/-- The hyperbolic sine quotient is at least `(e^v - 1)/v`, so the inner-band transform grows
exponentially in the aperture. -/
theorem sinh_quotient_ge {v : ℝ} (hv : 0 < v) :
    (Real.exp v - 1) / v ≤ 2 * Real.sinh v / v := by
  have hsinh : Real.sinh v = (Real.exp v - Real.exp (-v)) / 2 := by
    rw [Real.sinh_eq]
  have hexp : Real.exp (-v) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  rw [hsinh]
  rw [div_le_div_iff₀ hv hv]
  nlinarith [hexp, hv]

end GaloisForLFunctions.RHTower

end
