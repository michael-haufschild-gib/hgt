import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorSkewConstantMode

/-!
# The low harmonic band of the scalar-scalar plateau

On the low band `0 ≤ l ≤ t` the scalar-scalar line form is at least `4t¹⁵` for `t ≥ 10`
(`skewPlateauLineForm_low_ge`: the negative leading square is absorbed by `l ≤ t`, and the constant
`8t¹⁵` pays for every lower-weight monomial), while the denominator is at most `2176·t⁴(2+l)²`; hence
`skewPlateauMu_low_band_im_ge`: the kernel is at least `t¹¹/(544(2+l)²)` on the whole low band. Since
the bulk kernel is of size `5t⁹/8192`, every low harmonic `l = O(1)` carries a kernel of the opposite
sign and larger by the factor `t²`: with the spectral densities of the square of the angular profile
(`∝ t⁻¹τ²` on the low band and `∝ t⁻²` on the bulk, from the four-Λ weight), the on-line sign of the
clock coefficient under the pure-scalar reading is controlled by the low harmonics, i.e. by
`|ζ(½ + 2it)|⁴`, and not by the bulk.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

/-- On the low band `0 ≤ l ≤ t` the line form is at least `4t¹⁵` for `t ≥ 10`. -/
theorem skewPlateauLineForm_low_ge (t l : ℝ) (ht : (10 : ℝ) ≤ t) (hl0 : 0 ≤ l) (h2 : l ≤ t) :
    4 * t ^ (15 : ℕ) ≤ skewPlateauLineForm t l := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hg12 : (0 : ℝ) ≤ t - l := by linarith
  have hg13 : (0 : ℝ) ≤ t - 10 := by linarith
  have hp4 : (0 : ℝ) ≤ t + l := by linarith
  have key : skewPlateauLineForm t l - 4 * t ^ (15 : ℕ) = (35 / 64 : ℝ) * (t ^ (11 : ℕ) * l ^ (3 : ℕ)) + (5 / 64 : ℝ) * (t ^ (10 : ℕ) * l ^ (3 : ℕ) * (t - l)) + (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ) * (t - 10)) + (45 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) + (5 / 4 : ℝ) * (t ^ (13 : ℕ) * (t - l) * (t + l)) + (14931 / 40960000000000000 : ℝ) * (t * (t ^ (14 : ℕ) - 10 ^ (14 : ℕ))) + (58863 / 256000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 10 ^ (12 : ℕ))) + (19053 / 320000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 10 ^ (10 : ℕ))) + (36367 / 3200000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 10 ^ (8 : ℕ))) + (3151 / 8000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 10 ^ (6 : ℕ))) + (46 : ℝ) * (t ^ (11 : ℕ)) + (36 : ℝ) * (t ^ (13 : ℕ)) + (95169 / 4096 : ℝ) * (t * (t - l)) + (95169 / 40960000000000000 : ℝ) * (t ^ (2 : ℕ) * (t ^ (13 : ℕ) - 10 ^ (13 : ℕ))) + (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) + (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * (t - l)) + (3383 / 128000000 : ℝ) * (t ^ (8 : ℕ) * (t ^ (7 : ℕ) - 10 ^ (7 : ℕ))) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * (t - l)) + (2259 / 800000 : ℝ) * (t ^ (10 : ℕ) * (t ^ (5 : ℕ) - 10 ^ (5 : ℕ))) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * (t - l)) + (443 / 8000 : ℝ) * (t ^ (12 : ℕ) * (t ^ (3 : ℕ) - 10 ^ (3 : ℕ))) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * (t - l)) + (29 / 20 : ℝ) * (t ^ (14 : ℕ) * (t ^ (1 : ℕ) - 10 ^ (1 : ℕ))) + (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l * (t - l)) + (896173 / 4096 : ℝ) * (t ^ (4 : ℕ) * (t - l)) + (896173 / 40960000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 10 ^ (10 : ℕ))) + (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l * (t - l)) + (6265 / 128 : ℝ) * (t ^ (8 : ℕ) * (t - l)) + (1253 / 25600000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 10 ^ (6 : ℕ))) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l * (t - l)) + (943 / 32 : ℝ) * (t ^ (10 : ℕ) * (t - l)) + (943 / 320000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 10 ^ (4 : ℕ))) + (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t - l)) + (76823 / 2048 : ℝ) * (t ^ (4 : ℕ) * l * (t - l)) + (76823 / 2048 : ℝ) * (t ^ (5 : ℕ) * (t - l)) + (76823 / 2048000000000 : ℝ) * (t ^ (6 : ℕ) * (t ^ (9 : ℕ) - 10 ^ (9 : ℕ))) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t - l)) + (2667 / 256 : ℝ) * (t ^ (6 : ℕ) * l * (t - l)) + (2667 / 256 : ℝ) * (t ^ (7 : ℕ) * (t - l)) + (2667 / 2560000000 : ℝ) * (t ^ (8 : ℕ) * (t ^ (7 : ℕ) - 10 ^ (7 : ℕ))) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t - l)) + (639 / 64 : ℝ) * (t ^ (8 : ℕ) * l * (t - l)) + (639 / 64 : ℝ) * (t ^ (9 : ℕ) * (t - l)) + (639 / 6400000 : ℝ) * (t ^ (10 : ℕ) * (t ^ (5 : ℕ) - 10 ^ (5 : ℕ))) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t - l)) + (83 / 32 : ℝ) * (t ^ (10 : ℕ) * l * (t - l)) + (83 / 32 : ℝ) * (t ^ (11 : ℕ) * (t - l)) + (83 / 32000 : ℝ) * (t ^ (12 : ℕ) * (t ^ (3 : ℕ) - 10 ^ (3 : ℕ))) + (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) + (2530670603472741 / 2048000000000000 : ℝ) * (t ^ (15 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have m0 : 0 ≤ t ^ (11 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 3))
  have m1 : 0 ≤ t ^ (10 : ℕ) * l ^ (3 : ℕ) * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 10) (pow_nonneg hl0 3)) hg12)
  have m2 : 0 ≤ t ^ (9 : ℕ) * l ^ (4 : ℕ) * (t - 10) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 4)) hg13)
  have m3 : 0 ≤ t ^ (9 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 4))
  have m4 : 0 ≤ t ^ (13 : ℕ) * (t - l) * (t + l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 13) hg12) hp4)
  have m5 : 0 ≤ t * (t ^ (14 : ℕ) - 10 ^ (14 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 14)))
  have m6 : 0 ≤ t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 10 ^ (12 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 12)))
  have m7 : 0 ≤ t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 10 ^ (10 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m8 : 0 ≤ t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 10 ^ (8 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m9 : 0 ≤ t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 10 ^ (6 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m10 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m11 : 0 ≤ t ^ (13 : ℕ) := (pow_nonneg ht0 13)
  have m12 : 0 ≤ t * (t - l) := (mul_nonneg ht0 hg12)
  have m13 : 0 ≤ t ^ (2 : ℕ) * (t ^ (13 : ℕ) - 10 ^ (13 : ℕ)) := (mul_nonneg (pow_nonneg ht0 2) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 13)))
  have m14 : 0 ≤ t ^ (3 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 3) hl0)
  have m15 : 0 ≤ t ^ (5 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 5) hl0)
  have m16 : 0 ≤ t ^ (7 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 7) hg12)
  have m17 : 0 ≤ t ^ (8 : ℕ) * (t ^ (7 : ℕ) - 10 ^ (7 : ℕ)) := (mul_nonneg (pow_nonneg ht0 8) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 7)))
  have m18 : 0 ≤ t ^ (9 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 9) hg12)
  have m19 : 0 ≤ t ^ (10 : ℕ) * (t ^ (5 : ℕ) - 10 ^ (5 : ℕ)) := (mul_nonneg (pow_nonneg ht0 10) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 5)))
  have m20 : 0 ≤ t ^ (11 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 11) hg12)
  have m21 : 0 ≤ t ^ (12 : ℕ) * (t ^ (3 : ℕ) - 10 ^ (3 : ℕ)) := (mul_nonneg (pow_nonneg ht0 12) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 3)))
  have m22 : 0 ≤ t ^ (13 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 13) hg12)
  have m23 : 0 ≤ t ^ (14 : ℕ) * (t ^ (1 : ℕ) - 10 ^ (1 : ℕ)) := (mul_nonneg (pow_nonneg ht0 14) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 1)))
  have m24 : 0 ≤ t * l ^ (2 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 2))
  have m25 : 0 ≤ t ^ (3 : ℕ) * l * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) hl0) hg12)
  have m26 : 0 ≤ t ^ (4 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 4) hg12)
  have m27 : 0 ≤ t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 10 ^ (10 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m28 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2))
  have m29 : 0 ≤ t ^ (7 : ℕ) * l * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) hl0) hg12)
  have m30 : 0 ≤ t ^ (8 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 8) hg12)
  have m31 : 0 ≤ t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 10 ^ (6 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m32 : 0 ≤ t ^ (9 : ℕ) * l * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) hg12)
  have m33 : 0 ≤ t ^ (10 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 10) hg12)
  have m34 : 0 ≤ t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 10 ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m35 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have m36 : 0 ≤ t * l ^ (3 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 3))
  have m37 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) hg12)
  have m38 : 0 ≤ t ^ (4 : ℕ) * l * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 4) hl0) hg12)
  have m39 : 0 ≤ t ^ (5 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 5) hg12)
  have m40 : 0 ≤ t ^ (6 : ℕ) * (t ^ (9 : ℕ) - 10 ^ (9 : ℕ)) := (mul_nonneg (pow_nonneg ht0 6) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 9)))
  have m41 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) hg12)
  have m42 : 0 ≤ t ^ (6 : ℕ) * l * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 6) hl0) hg12)
  have m43 : 0 ≤ t ^ (7 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 7) hg12)
  have m44 : 0 ≤ t ^ (8 : ℕ) * (t ^ (7 : ℕ) - 10 ^ (7 : ℕ)) := (mul_nonneg (pow_nonneg ht0 8) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 7)))
  have m45 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) hg12)
  have m46 : 0 ≤ t ^ (8 : ℕ) * l * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 8) hl0) hg12)
  have m47 : 0 ≤ t ^ (9 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 9) hg12)
  have m48 : 0 ≤ t ^ (10 : ℕ) * (t ^ (5 : ℕ) - 10 ^ (5 : ℕ)) := (mul_nonneg (pow_nonneg ht0 10) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 5)))
  have m49 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) hg12)
  have m50 : 0 ≤ t ^ (10 : ℕ) * l * (t - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 10) hl0) hg12)
  have m51 : 0 ≤ t ^ (11 : ℕ) * (t - l) := (mul_nonneg (pow_nonneg ht0 11) hg12)
  have m52 : 0 ≤ t ^ (12 : ℕ) * (t ^ (3 : ℕ) - 10 ^ (3 : ℕ)) := (mul_nonneg (pow_nonneg ht0 12) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 3)))
  have m53 : 0 ≤ t * l ^ (4 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 4))
  have m54 : 0 ≤ t ^ (3 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 4))
  have m55 : 0 ≤ t ^ (5 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 4))
  have m56 : 0 ≤ t ^ (7 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 4))
  have m57 : 0 ≤ t ^ (15 : ℕ) := (pow_nonneg ht0 15)
  have h0 : 0 ≤ (35 / 64 : ℝ) * (t ^ (11 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (5 / 64 : ℝ) * (t ^ (10 : ℕ) * l ^ (3 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ) * (t - 10)) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (45 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (5 / 4 : ℝ) * (t ^ (13 : ℕ) * (t - l) * (t + l)) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (14931 / 40960000000000000 : ℝ) * (t * (t ^ (14 : ℕ) - 10 ^ (14 : ℕ))) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (58863 / 256000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 10 ^ (12 : ℕ))) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (19053 / 320000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 10 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (36367 / 3200000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 10 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (3151 / 8000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 10 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (46 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (36 : ℝ) * (t ^ (13 : ℕ)) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (95169 / 4096 : ℝ) * (t * (t - l)) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (95169 / 40960000000000000 : ℝ) * (t ^ (2 : ℕ) * (t ^ (13 : ℕ) - 10 ^ (13 : ℕ))) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (3383 / 128000000 : ℝ) * (t ^ (8 : ℕ) * (t ^ (7 : ℕ) - 10 ^ (7 : ℕ))) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (2259 / 800000 : ℝ) * (t ^ (10 : ℕ) * (t ^ (5 : ℕ) - 10 ^ (5 : ℕ))) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (443 / 8 : ℝ) * (t ^ (11 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (443 / 8000 : ℝ) * (t ^ (12 : ℕ) * (t ^ (3 : ℕ) - 10 ^ (3 : ℕ))) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (29 / 2 : ℝ) * (t ^ (13 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (29 / 20 : ℝ) * (t ^ (14 : ℕ) * (t ^ (1 : ℕ) - 10 ^ (1 : ℕ))) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l * (t - l)) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (896173 / 4096 : ℝ) * (t ^ (4 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (896173 / 40960000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 10 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l * (t - l)) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (6265 / 128 : ℝ) * (t ^ (8 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (1253 / 25600000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 10 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l * (t - l)) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (943 / 32 : ℝ) * (t ^ (10 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (943 / 320000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 10 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (4 : ℕ) * l * (t - l)) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (5 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (76823 / 2048000000000 : ℝ) * (t ^ (6 : ℕ) * (t ^ (9 : ℕ) - 10 ^ (9 : ℕ))) := mul_nonneg (by norm_num) m40
  have h41 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m41
  have h42 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (6 : ℕ) * l * (t - l)) := mul_nonneg (by norm_num) m42
  have h43 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (7 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m43
  have h44 : 0 ≤ (2667 / 2560000000 : ℝ) * (t ^ (8 : ℕ) * (t ^ (7 : ℕ) - 10 ^ (7 : ℕ))) := mul_nonneg (by norm_num) m44
  have h45 : 0 ≤ (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m45
  have h46 : 0 ≤ (639 / 64 : ℝ) * (t ^ (8 : ℕ) * l * (t - l)) := mul_nonneg (by norm_num) m46
  have h47 : 0 ≤ (639 / 64 : ℝ) * (t ^ (9 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m47
  have h48 : 0 ≤ (639 / 6400000 : ℝ) * (t ^ (10 : ℕ) * (t ^ (5 : ℕ) - 10 ^ (5 : ℕ))) := mul_nonneg (by norm_num) m48
  have h49 : 0 ≤ (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m49
  have h50 : 0 ≤ (83 / 32 : ℝ) * (t ^ (10 : ℕ) * l * (t - l)) := mul_nonneg (by norm_num) m50
  have h51 : 0 ≤ (83 / 32 : ℝ) * (t ^ (11 : ℕ) * (t - l)) := mul_nonneg (by norm_num) m51
  have h52 : 0 ≤ (83 / 32000 : ℝ) * (t ^ (12 : ℕ) * (t ^ (3 : ℕ) - 10 ^ (3 : ℕ))) := mul_nonneg (by norm_num) m52
  have h53 : 0 ≤ (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m53
  have h54 : 0 ≤ (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m54
  have h55 : 0 ≤ (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m55
  have h56 : 0 ≤ (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m56
  have h57 : 0 ≤ (2530670603472741 / 2048000000000000 : ℝ) * (t ^ (15 : ℕ)) := mul_nonneg (by norm_num) m57
  have hP : 0 ≤ (35 / 64 : ℝ) * (t ^ (11 : ℕ) * l ^ (3 : ℕ)) + (5 / 64 : ℝ) * (t ^ (10 : ℕ) * l ^ (3 : ℕ) * (t - l)) + (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ) * (t - 10)) + (45 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) + (5 / 4 : ℝ) * (t ^ (13 : ℕ) * (t - l) * (t + l)) + (14931 / 40960000000000000 : ℝ) * (t * (t ^ (14 : ℕ) - 10 ^ (14 : ℕ))) + (58863 / 256000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 10 ^ (12 : ℕ))) + (19053 / 320000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 10 ^ (10 : ℕ))) + (36367 / 3200000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 10 ^ (8 : ℕ))) + (3151 / 8000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 10 ^ (6 : ℕ))) + (46 : ℝ) * (t ^ (11 : ℕ)) + (36 : ℝ) * (t ^ (13 : ℕ)) + (95169 / 4096 : ℝ) * (t * (t - l)) + (95169 / 40960000000000000 : ℝ) * (t ^ (2 : ℕ) * (t ^ (13 : ℕ) - 10 ^ (13 : ℕ))) + (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) + (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * (t - l)) + (3383 / 128000000 : ℝ) * (t ^ (8 : ℕ) * (t ^ (7 : ℕ) - 10 ^ (7 : ℕ))) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * (t - l)) + (2259 / 800000 : ℝ) * (t ^ (10 : ℕ) * (t ^ (5 : ℕ) - 10 ^ (5 : ℕ))) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * (t - l)) + (443 / 8000 : ℝ) * (t ^ (12 : ℕ) * (t ^ (3 : ℕ) - 10 ^ (3 : ℕ))) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * (t - l)) + (29 / 20 : ℝ) * (t ^ (14 : ℕ) * (t ^ (1 : ℕ) - 10 ^ (1 : ℕ))) + (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l * (t - l)) + (896173 / 4096 : ℝ) * (t ^ (4 : ℕ) * (t - l)) + (896173 / 40960000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 10 ^ (10 : ℕ))) + (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l * (t - l)) + (6265 / 128 : ℝ) * (t ^ (8 : ℕ) * (t - l)) + (1253 / 25600000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 10 ^ (6 : ℕ))) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l * (t - l)) + (943 / 32 : ℝ) * (t ^ (10 : ℕ) * (t - l)) + (943 / 320000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 10 ^ (4 : ℕ))) + (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t - l)) + (76823 / 2048 : ℝ) * (t ^ (4 : ℕ) * l * (t - l)) + (76823 / 2048 : ℝ) * (t ^ (5 : ℕ) * (t - l)) + (76823 / 2048000000000 : ℝ) * (t ^ (6 : ℕ) * (t ^ (9 : ℕ) - 10 ^ (9 : ℕ))) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t - l)) + (2667 / 256 : ℝ) * (t ^ (6 : ℕ) * l * (t - l)) + (2667 / 256 : ℝ) * (t ^ (7 : ℕ) * (t - l)) + (2667 / 2560000000 : ℝ) * (t ^ (8 : ℕ) * (t ^ (7 : ℕ) - 10 ^ (7 : ℕ))) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t - l)) + (639 / 64 : ℝ) * (t ^ (8 : ℕ) * l * (t - l)) + (639 / 64 : ℝ) * (t ^ (9 : ℕ) * (t - l)) + (639 / 6400000 : ℝ) * (t ^ (10 : ℕ) * (t ^ (5 : ℕ) - 10 ^ (5 : ℕ))) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t - l)) + (83 / 32 : ℝ) * (t ^ (10 : ℕ) * l * (t - l)) + (83 / 32 : ℝ) * (t ^ (11 : ℕ) * (t - l)) + (83 / 32000 : ℝ) * (t ^ (12 : ℕ) * (t ^ (3 : ℕ) - 10 ^ (3 : ℕ))) + (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) + (2530670603472741 / 2048000000000000 : ℝ) * (t ^ (15 : ℕ)) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48) h49) h50) h51) h52) h53) h54) h55) h56) h57)
  linarith

/-- On the low band the kernel is at least `t¹¹/(544(2+l)²)` for `t ≥ 10`. -/
theorem skewPlateauMu_low_band_im_ge (t l : ℝ) (ht : (10 : ℝ) ≤ t) (hl0 : 0 ≤ l) (h2 : l ≤ t) :
    t ^ (11 : ℕ) / (544 * (2 + l) ^ (2 : ℕ)) ≤ (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im := by
  have h := congrArg Complex.im (skewPlateauMu_line t l hl0)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
  have hden := skewPlateauLineDen_pos t l hl0
  have hF := skewPlateauLineForm_low_ge t l ht hl0 h2
  have h15 : (0 : ℝ) < t ^ (15 : ℕ) := by positivity
  have hsq : (0 : ℝ) < (2 + l) ^ (2 : ℕ) := by positivity
  have hpos4 : (0 : ℝ) < t ^ (4 : ℕ) := by positivity
  have hd : 128 * (2 + l) ^ (2 : ℕ) * ((4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ)) ≤ 2176 * t ^ (4 : ℕ) * (2 + l) ^ (2 : ℕ) := by
    have h100 : (100 : ℝ) ≤ t ^ (2 : ℕ) := by nlinarith
    have hin : (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ) ≤ 17 * t ^ (4 : ℕ) := by
      have hl2 : l ^ (2 : ℕ) ≤ t ^ (2 : ℕ) := by nlinarith
      nlinarith
    have := mul_le_mul_of_nonneg_left hin (by positivity : (0 : ℝ) ≤ 128 * (2 + l) ^ (2 : ℕ))
    linarith
  have hImpos : 0 < (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im := by
    have : 0 < skewPlateauLineForm t l := by linarith
    exact pos_of_mul_pos_left (by rw [h]; exact this) hden.le
  have key : 4 * t ^ (15 : ℕ) ≤ (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im * (2176 * t ^ (4 : ℕ) * (2 + l) ^ (2 : ℕ)) := by
    have := mul_le_mul_of_nonneg_left hd hImpos.le
    linarith
  rw [div_le_iff₀ (by positivity)]
  have h4 : t ^ (11 : ℕ) * t ^ (4 : ℕ) ≤ (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im * (544 * (2 + l) ^ (2 : ℕ)) * t ^ (4 : ℕ) := by
    have e1 : t ^ (11 : ℕ) * t ^ (4 : ℕ) = t ^ (15 : ℕ) := by ring
    rw [e1]
    have e2 : (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im * (544 * (2 + l) ^ (2 : ℕ)) * t ^ (4 : ℕ) =
        (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im * (2176 * t ^ (4 : ℕ) * (2 + l) ^ (2 : ℕ)) / 4 := by ring
    rw [e2]; linarith
  exact le_of_mul_le_mul_right h4 hpos4

end RHTower.D4BMScalarStream
