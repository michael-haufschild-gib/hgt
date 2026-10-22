import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorSkewPlateauHarmonic

/-!
# The constant mode against the bulk in the scalar-scalar plateau

At the constant harmonic `l = 0` the line form of the scalar-scalar plateau is
`8t¹⁵ + 36t¹³ + 46t¹¹ − (3151/8)t⁹ − …`, positive and at least `4t¹⁵` for `t ≥ 3`
(`skewPlateauLineForm_zero_ge`), while the denominator there is `128·4·((4t²−2)² + 36t²) ≤ 8704·t⁴`
for `t ≥ 5`; hence the constant-mode kernel is at least `t¹¹/2176` (`skewPlateauMu_constant_mode_im_ge`).
On the bulk band `t² ≤ l ≤ 3t²` the line form is at most `t⁹/1000` times the denominator for
`t ≥ 50` (`skewPlateauLineForm_bulk_upper`), so the bulk kernel is at most `t⁹/1000`
(`skewPlateauMu_bulk_im_le`); its leading value there is `−5t⁹/8192`. The constant mode's (positive)
kernel is therefore larger than the bulk scale by the factor `t²/2.7`: under the pure-scalar reading
the on-line sign of the clock coefficient is decided by the regularized constant term of the angular
square, i.e. by the cusp flux, against which the bulk is suppressed by `t⁻²`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

theorem skewPlateauLineForm_zero (t : ℝ) : skewPlateauLineForm t 0 = (-74655 / 2048 : ℝ) * t + (-58863 / 256 : ℝ) * t ^ (3 : ℕ) + (-19053 / 32 : ℝ) * t ^ (5 : ℕ) + (-36367 / 32 : ℝ) * t ^ (7 : ℕ) + (-3151 / 8 : ℝ) * t ^ (9 : ℕ) + (46 : ℝ) * t ^ (11 : ℕ) + (36 : ℝ) * t ^ (13 : ℕ) + (8 : ℝ) * t ^ (15 : ℕ) := by
  unfold skewPlateauLineForm
  ring

/-- At the constant harmonic the line form is at least `4t¹⁵` for `t ≥ 3`. -/
theorem skewPlateauLineForm_zero_ge (t : ℝ) (ht : (3 : ℝ) ≤ t) : 4 * t ^ (15 : ℕ) ≤ skewPlateauLineForm t 0 := by
  rw [skewPlateauLineForm_zero]
  have h1 : (0 : ℝ) < t := by linarith
  have p1 : t * 3 ^ (14 : ℕ) ≤ t ^ (15 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) ht 14
    calc t * 3 ^ (14 : ℕ) ≤ t * t ^ (14 : ℕ) := by exact mul_le_mul_of_nonneg_left this h1.le
      _ = t ^ (15 : ℕ) := by ring
  have p3 : t ^ (3 : ℕ) * 3 ^ (12 : ℕ) ≤ t ^ (15 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) ht 12
    calc t ^ (3 : ℕ) * 3 ^ (12 : ℕ) ≤ t ^ (3 : ℕ) * t ^ (12 : ℕ) := by exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = t ^ (15 : ℕ) := by ring
  have p5 : t ^ (5 : ℕ) * 3 ^ (10 : ℕ) ≤ t ^ (15 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) ht 10
    calc t ^ (5 : ℕ) * 3 ^ (10 : ℕ) ≤ t ^ (5 : ℕ) * t ^ (10 : ℕ) := by exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = t ^ (15 : ℕ) := by ring
  have p7 : t ^ (7 : ℕ) * 3 ^ (8 : ℕ) ≤ t ^ (15 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) ht 8
    calc t ^ (7 : ℕ) * 3 ^ (8 : ℕ) ≤ t ^ (7 : ℕ) * t ^ (8 : ℕ) := by exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = t ^ (15 : ℕ) := by ring
  have p9 : t ^ (9 : ℕ) * 3 ^ (6 : ℕ) ≤ t ^ (15 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) ht 6
    calc t ^ (9 : ℕ) * 3 ^ (6 : ℕ) ≤ t ^ (9 : ℕ) * t ^ (6 : ℕ) := by exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = t ^ (15 : ℕ) := by ring
  have q11 : (0 : ℝ) ≤ t ^ (11 : ℕ) := by positivity
  have q13 : (0 : ℝ) ≤ t ^ (13 : ℕ) := by positivity
  nlinarith

/-- The constant-mode kernel is at least `t¹¹/2176` for `t ≥ 5`. -/
theorem skewPlateauMu_constant_mode_im_ge (t : ℝ) (ht : (5 : ℝ) ≤ t) :
    t ^ (11 : ℕ) / 2176 ≤ (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-((0 : ℝ) : ℂ))).im := by
  have h := congrArg Complex.im (skewPlateauMu_line t 0 le_rfl)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
  have hden := skewPlateauLineDen_pos t 0 le_rfl
  have hF := skewPlateauLineForm_zero_ge t (by linarith)
  have hd : 128 * (2 + (0 : ℝ)) ^ (2 : ℕ) * ((4 * t ^ (2 : ℕ) - 2 - 0) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ)) ≤ 8704 * t ^ (4 : ℕ) := by
    have h25 : (25 : ℝ) ≤ t ^ (2 : ℕ) := by nlinarith
    have h4 : (625 : ℝ) ≤ t ^ (4 : ℕ) := by nlinarith
    nlinarith
  have hpos4 : (0 : ℝ) < t ^ (4 : ℕ) := by positivity
  -- Im * den = F ≥ 4 t^(15 : ℕ) and den ≤ 2176 t^(4 : ℕ)
  have hIm : (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-((0 : ℝ) : ℂ))).im *
      (128 * (2 + (0 : ℝ)) ^ (2 : ℕ) * ((4 * t ^ (2 : ℕ) - 2 - 0) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ))) = skewPlateauLineForm t 0 := by
    simpa using h
  have h15 : (0 : ℝ) < t ^ (15 : ℕ) := by positivity
  have hImpos : 0 < (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-((0 : ℝ) : ℂ))).im := by
    have : 0 < skewPlateauLineForm t 0 := by linarith
    exact pos_of_mul_pos_left (by rw [hIm]; exact this) hden.le
  have key : 4 * t ^ (15 : ℕ) ≤ (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-((0 : ℝ) : ℂ))).im * (8704 * t ^ (4 : ℕ)) := by
    have := mul_le_mul_of_nonneg_left hd hImpos.le
    linarith
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2176)]
  have h4 : t ^ (11 : ℕ) * t ^ (4 : ℕ) ≤ (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-((0 : ℝ) : ℂ))).im * 2176 * t ^ (4 : ℕ) := by
    have e1 : t ^ (11 : ℕ) * t ^ (4 : ℕ) = t ^ (15 : ℕ) := by ring
    rw [e1]
    have e2 : (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-((0 : ℝ) : ℂ))).im * 2176 * t ^ (4 : ℕ) =
        (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-((0 : ℝ) : ℂ))).im * (8704 * t ^ (4 : ℕ)) / 4 := by ring
    rw [e2]; linarith
  exact le_of_mul_le_mul_right h4 hpos4

theorem skewPlateauLineForm_bulk_upper (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : t ^ (2 : ℕ) ≤ l) (h2 : l ≤ 3 * t ^ (2 : ℕ)) :
    0 ≤ t ^ (9 : ℕ) * (128 * (2 + l) ^ (2 : ℕ) * ((4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ))) / 1000 - skewPlateauLineForm t l := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hg3 : (0 : ℝ) ≤ t - 50 := by linarith
  have hg2 : (0 : ℝ) ≤ 3 * t ^ (2 : ℕ) - l := by linarith
  have hg11 : (0 : ℝ) ≤ l - t ^ (2 : ℕ) := by linarith
  have hp50 : (0 : ℝ) ≤ t + 50 := by linarith
  have hp2 : (0 : ℝ) ≤ t + 2 := by linarith
  have key : t ^ (9 : ℕ) * (128 * (2 + l) ^ (2 : ℕ) * ((4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ))) / 1000 - skewPlateauLineForm t l = (16 / 125 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t - 50) * (t + 2)) + (768 / 125 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t - 50)) + (64 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (32 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l)) + (79936 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l)) + (16 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (64 / 125 : ℝ) * (t ^ (11 : ℕ) * l * (t - 50) * (t + 2)) + (3072 / 125 : ℝ) * (t ^ (12 : ℕ) * l) + (6144 / 125 : ℝ) * (t ^ (11 : ℕ) * l) + (256 / 125 : ℝ) * (t ^ (9 : ℕ) * l) + (128 / 125 : ℝ) * (t ^ (9 : ℕ) * l * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l)) + (319744 / 125 : ℝ) * (t ^ (9 : ℕ) * l * (3 * t ^ (2 : ℕ) - l)) + (64 / 125 : ℝ) * (t ^ (9 : ℕ) * l * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (2304 / 125 : ℝ) * (t ^ (11 : ℕ) * l) + (64 / 125 : ℝ) * (t ^ (11 : ℕ) * (t - 50) * (t + 2)) + (3072 / 125 : ℝ) * (t ^ (12 : ℕ)) + (6144 / 125 : ℝ) * (t ^ (11 : ℕ)) + (256 / 125 : ℝ) * (t ^ (9 : ℕ)) + (128 / 125 : ℝ) * (t ^ (9 : ℕ) * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l)) + (319744 / 125 : ℝ) * (t ^ (9 : ℕ) * (3 * t ^ (2 : ℕ) - l)) + (64 / 125 : ℝ) * (t ^ (9 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (2304 / 125 : ℝ) * (t ^ (11 : ℕ)) + (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ)) + (74655 / 2048 : ℝ) * (t) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) + (46 : ℝ) * (t ^ (7 : ℕ) * l * (l - t ^ (2 : ℕ))) + (46 : ℝ) * (t ^ (9 : ℕ) * (l - t ^ (2 : ℕ))) + (23 / 3125000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (36 : ℝ) * (t ^ (9 : ℕ) * l * (l - t ^ (2 : ℕ))) + (36 : ℝ) * (t ^ (11 : ℕ) * (l - t ^ (2 : ℕ))) + (9 / 625 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (8 : ℝ) * (t ^ (11 : ℕ) * l * (l - t ^ (2 : ℕ))) + (8 : ℝ) * (t ^ (13 : ℕ) * (l - t ^ (2 : ℕ))) + (95169 / 4096 : ℝ) * (t * l) + (728753 / 2048 : ℝ) * (t * l * (l - t ^ (2 : ℕ))) + (728753 / 200000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (402363 / 512 : ℝ) * (t ^ (3 : ℕ) * l * (l - t ^ (2 : ℕ))) + (402363 / 20000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (0 : ℕ) - 50 ^ (0 : ℕ))) + (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (715851 / 320000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (226443 / 16384 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (2037987 / 256000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (104607 / 6400000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (20241 / 1280000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (279 / 64 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (0 : ℕ) - 50 ^ (0 : ℕ))) + (123507555200938826755999 / 400000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have m0 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t - 50) * (t + 2) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) hg3) hp2)
  have m1 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t - 50) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) hg3)
  have m2 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m3 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) hg3) hp50) hg2)
  have m4 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) hg2)
  have m5 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (pow_nonneg hg2 2))
  have m6 : 0 ≤ t ^ (11 : ℕ) * l * (t - 50) * (t + 2) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) hl0) hg3) hp2)
  have m7 : 0 ≤ t ^ (12 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 12) hl0)
  have m8 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m9 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m10 : 0 ≤ t ^ (9 : ℕ) * l * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) hg3) hp50) hg2)
  have m11 : 0 ≤ t ^ (9 : ℕ) * l * (3 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) hg2)
  have m12 : 0 ≤ t ^ (9 : ℕ) * l * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) (pow_nonneg hg2 2))
  have m13 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m14 : 0 ≤ t ^ (11 : ℕ) * (t - 50) * (t + 2) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) hg3) hp2)
  have m15 : 0 ≤ t ^ (12 : ℕ) := (pow_nonneg ht0 12)
  have m16 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m17 : 0 ≤ t ^ (9 : ℕ) := (pow_nonneg ht0 9)
  have m18 : 0 ≤ t ^ (9 : ℕ) * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hg3) hp50) hg2)
  have m19 : 0 ≤ t ^ (9 : ℕ) * (3 * t ^ (2 : ℕ) - l) := (mul_nonneg (pow_nonneg ht0 9) hg2)
  have m20 : 0 ≤ t ^ (9 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hg2 2))
  have m21 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m22 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sq_nonneg (l - 4 * t ^ (2 : ℕ))))
  have m23 : 0 ≤ t := ht0
  have m24 : 0 ≤ t ^ (3 : ℕ) := (pow_nonneg ht0 3)
  have m25 : 0 ≤ t ^ (5 : ℕ) := (pow_nonneg ht0 5)
  have m26 : 0 ≤ t ^ (7 : ℕ) := (pow_nonneg ht0 7)
  have m27 : 0 ≤ t ^ (9 : ℕ) := (pow_nonneg ht0 9)
  have m28 : 0 ≤ t ^ (7 : ℕ) * l * (l - t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) hl0) hg11)
  have m29 : 0 ≤ t ^ (9 : ℕ) * (l - t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) hg11)
  have m30 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m31 : 0 ≤ t ^ (9 : ℕ) * l * (l - t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) hg11)
  have m32 : 0 ≤ t ^ (11 : ℕ) * (l - t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) hg11)
  have m33 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m34 : 0 ≤ t ^ (11 : ℕ) * l * (l - t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) hl0) hg11)
  have m35 : 0 ≤ t ^ (13 : ℕ) * (l - t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) hg11)
  have m36 : 0 ≤ t * l := (mul_nonneg ht0 hl0)
  have m37 : 0 ≤ t * l * (l - t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg ht0 hl0) hg11)
  have m38 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m39 : 0 ≤ t ^ (3 : ℕ) * l * (l - t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) hl0) hg11)
  have m40 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m41 : 0 ≤ t ^ (7 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 7) hl0)
  have m42 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m43 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m44 : 0 ≤ t ^ (13 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 13) hl0)
  have m45 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m46 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2))
  have m47 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m48 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2))
  have m49 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m50 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (0 : ℕ) - 50 ^ (0 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 0)))
  have m51 : 0 ≤ t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 1)))
  have m52 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m53 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3))
  have m54 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3))
  have m55 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3))
  have m56 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3))
  have m57 : 0 ≤ t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m58 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m59 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m60 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m61 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m62 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m63 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m64 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (0 : ℕ) - 50 ^ (0 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 0)))
  have m65 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have h0 : 0 ≤ (16 / 125 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t - 50) * (t + 2)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (768 / 125 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t - 50)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (64 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (32 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (79936 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (16 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (64 / 125 : ℝ) * (t ^ (11 : ℕ) * l * (t - 50) * (t + 2)) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (3072 / 125 : ℝ) * (t ^ (12 : ℕ) * l) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (6144 / 125 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (256 / 125 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (128 / 125 : ℝ) * (t ^ (9 : ℕ) * l * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (319744 / 125 : ℝ) * (t ^ (9 : ℕ) * l * (3 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (64 / 125 : ℝ) * (t ^ (9 : ℕ) * l * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (2304 / 125 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (64 / 125 : ℝ) * (t ^ (11 : ℕ) * (t - 50) * (t + 2)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (3072 / 125 : ℝ) * (t ^ (12 : ℕ)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (6144 / 125 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (256 / 125 : ℝ) * (t ^ (9 : ℕ)) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (128 / 125 : ℝ) * (t ^ (9 : ℕ) * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (319744 / 125 : ℝ) * (t ^ (9 : ℕ) * (3 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (64 / 125 : ℝ) * (t ^ (9 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (2304 / 125 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (74655 / 2048 : ℝ) * (t) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (46 : ℝ) * (t ^ (7 : ℕ) * l * (l - t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (46 : ℝ) * (t ^ (9 : ℕ) * (l - t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (23 / 3125000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (36 : ℝ) * (t ^ (9 : ℕ) * l * (l - t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (36 : ℝ) * (t ^ (11 : ℕ) * (l - t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (9 / 625 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (8 : ℝ) * (t ^ (11 : ℕ) * l * (l - t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (8 : ℝ) * (t ^ (13 : ℕ) * (l - t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (95169 / 4096 : ℝ) * (t * l) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (728753 / 2048 : ℝ) * (t * l * (l - t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (728753 / 200000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (402363 / 512 : ℝ) * (t ^ (3 : ℕ) * l * (l - t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (402363 / 20000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m40
  have h41 : 0 ≤ (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) := mul_nonneg (by norm_num) m41
  have h42 : 0 ≤ (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m42
  have h43 : 0 ≤ (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m43
  have h44 : 0 ≤ (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) := mul_nonneg (by norm_num) m44
  have h45 : 0 ≤ (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m45
  have h46 : 0 ≤ (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m46
  have h47 : 0 ≤ (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m47
  have h48 : 0 ≤ (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m48
  have h49 : 0 ≤ (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m49
  have h50 : 0 ≤ (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (0 : ℕ) - 50 ^ (0 : ℕ))) := mul_nonneg (by norm_num) m50
  have h51 : 0 ≤ (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) := mul_nonneg (by norm_num) m51
  have h52 : 0 ≤ (715851 / 320000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m52
  have h53 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m53
  have h54 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m54
  have h55 : 0 ≤ (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m55
  have h56 : 0 ≤ (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m56
  have h57 : 0 ≤ (226443 / 16384 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m57
  have h58 : 0 ≤ (2037987 / 256000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m58
  have h59 : 0 ≤ (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m59
  have h60 : 0 ≤ (104607 / 6400000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m60
  have h61 : 0 ≤ (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m61
  have h62 : 0 ≤ (20241 / 1280000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m62
  have h63 : 0 ≤ (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m63
  have h64 : 0 ≤ (279 / 64 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (0 : ℕ) - 50 ^ (0 : ℕ))) := mul_nonneg (by norm_num) m64
  have h65 : 0 ≤ (123507555200938826755999 / 400000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m65
  have hP : 0 ≤ (16 / 125 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t - 50) * (t + 2)) + (768 / 125 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t - 50)) + (64 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (32 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l)) + (79936 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l)) + (16 / 125 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (64 / 125 : ℝ) * (t ^ (11 : ℕ) * l * (t - 50) * (t + 2)) + (3072 / 125 : ℝ) * (t ^ (12 : ℕ) * l) + (6144 / 125 : ℝ) * (t ^ (11 : ℕ) * l) + (256 / 125 : ℝ) * (t ^ (9 : ℕ) * l) + (128 / 125 : ℝ) * (t ^ (9 : ℕ) * l * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l)) + (319744 / 125 : ℝ) * (t ^ (9 : ℕ) * l * (3 * t ^ (2 : ℕ) - l)) + (64 / 125 : ℝ) * (t ^ (9 : ℕ) * l * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (2304 / 125 : ℝ) * (t ^ (11 : ℕ) * l) + (64 / 125 : ℝ) * (t ^ (11 : ℕ) * (t - 50) * (t + 2)) + (3072 / 125 : ℝ) * (t ^ (12 : ℕ)) + (6144 / 125 : ℝ) * (t ^ (11 : ℕ)) + (256 / 125 : ℝ) * (t ^ (9 : ℕ)) + (128 / 125 : ℝ) * (t ^ (9 : ℕ) * (t - 50) * (t + 50) * (3 * t ^ (2 : ℕ) - l)) + (319744 / 125 : ℝ) * (t ^ (9 : ℕ) * (3 * t ^ (2 : ℕ) - l)) + (64 / 125 : ℝ) * (t ^ (9 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (2304 / 125 : ℝ) * (t ^ (11 : ℕ)) + (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ)) + (74655 / 2048 : ℝ) * (t) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) + (46 : ℝ) * (t ^ (7 : ℕ) * l * (l - t ^ (2 : ℕ))) + (46 : ℝ) * (t ^ (9 : ℕ) * (l - t ^ (2 : ℕ))) + (23 / 3125000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (36 : ℝ) * (t ^ (9 : ℕ) * l * (l - t ^ (2 : ℕ))) + (36 : ℝ) * (t ^ (11 : ℕ) * (l - t ^ (2 : ℕ))) + (9 / 625 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (8 : ℝ) * (t ^ (11 : ℕ) * l * (l - t ^ (2 : ℕ))) + (8 : ℝ) * (t ^ (13 : ℕ) * (l - t ^ (2 : ℕ))) + (95169 / 4096 : ℝ) * (t * l) + (728753 / 2048 : ℝ) * (t * l * (l - t ^ (2 : ℕ))) + (728753 / 200000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (402363 / 512 : ℝ) * (t ^ (3 : ℕ) * l * (l - t ^ (2 : ℕ))) + (402363 / 20000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (0 : ℕ) - 50 ^ (0 : ℕ))) + (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (715851 / 320000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (226443 / 16384 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (2037987 / 256000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (104607 / 6400000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (20241 / 1280000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (279 / 64 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (0 : ℕ) - 50 ^ (0 : ℕ))) + (123507555200938826755999 / 400000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48) h49) h50) h51) h52) h53) h54) h55) h56) h57) h58) h59) h60) h61) h62) h63) h64) h65)
  rw [key]
  exact hP

/-- On the bulk band the scalar-scalar kernel is at most `t⁹/1000` for `t ≥ 50`. -/
theorem skewPlateauMu_bulk_im_le (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : t ^ (2 : ℕ) ≤ l) (h2 : l ≤ 3 * t ^ (2 : ℕ)) :
    (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im ≤ t ^ (9 : ℕ) / 1000 := by
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have h := congrArg Complex.im (skewPlateauMu_line t l hl0)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
  have hden := skewPlateauLineDen_pos t l hl0
  have hU := skewPlateauLineForm_bulk_upper t l ht h1 h2
  have : (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im * (128 * (2 + l) ^ (2 : ℕ) * ((4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ))) ≤ t ^ (9 : ℕ) / 1000 * (128 * (2 + l) ^ (2 : ℕ) * ((4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ))) := by
    rw [h]; nlinarith
  exact le_of_mul_le_mul_right this hden

end RHTower.D4BMScalarStream
