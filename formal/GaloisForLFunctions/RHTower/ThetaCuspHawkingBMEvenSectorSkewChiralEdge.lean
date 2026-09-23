import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewChiralSign

/-!
# The chiral kernel on the edge band: one sign on the whole spectral support

On `2t² ≤ l ≤ (17/4)t²` the leading part of the chiral line form,
`(1/16)·t⁵l²(l−4t²)²·((17/4)t² − l)·(3t² + 4l)`, is nonnegative but vanishes to second order at
the doubled-frequency edge `l = 4t²`; there the weight-fifteen form decides. In the Bernstein basis
of the band, `(l − 2t²)^i((17/4)t² − l)^{6−i}`, that form has all coefficients at least `22.66`, and
the lower weights cost at most `17.34` units of `t¹⁵` for `t ≥ 50`, so the chiral line form is
positive on the whole band (`skewPlateauMuChiralLine_pos_edge`). Together with the bulk certificate
this gives `skewPlateauMuChiral_line_im_pos_support`: for `t ≥ 50` the chiral kernel has positive
imaginary part at **every** harmonic `0 ≤ l ≤ (17/4)t²` — the whole spectral support of the square
of the angular profile, edge included.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

/-- The chiral line form is positive on the edge band `2t² ≤ l ≤ (17/4)t²` for `t ≥ 50`. -/
theorem skewPlateauMuChiralLine_pos_edge (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : 2 * t ^ (2 : ℕ) ≤ l) (h2 : l ≤ 17 / 4 * t ^ (2 : ℕ)) :
    0 < skewPlateauMuChiralLine t l := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hpos_t : (0 : ℝ) < t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hg3 : (0 : ℝ) ≤ t - 50 := by linarith
  have hg10 : (0 : ℝ) ≤ l - 2 * t ^ (2 : ℕ) := by linarith
  have hg9 : (0 : ℝ) ≤ 17 / 4 * t ^ (2 : ℕ) - l := by linarith
  have key : skewPlateauMuChiralLine t l = (3 / 16 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l)) + (1 / 4 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l)) + (2198528 / 531441 : ℝ) * (t ^ (3 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (6 : ℕ)) + (2603392 / 177147 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (5 : ℕ)) + (2497792 / 177147 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (4 : ℕ)) + (54466 / 531441 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (3 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (3 : ℕ)) + (442537 / 708588 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (4 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (9450497 / 1417176 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (5 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l)) + (1573801 / 1062882 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (6 : ℕ)) + (23263191 / 1250000000000000000000000000 : ℝ) * (t * (t ^ (14 : ℕ) - 50 ^ (14 : ℕ))) + (18458023 / 62500000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (4034501 / 3125000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (2482407 / 1250000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (51449 / 8 : ℝ) * (t ^ (9 : ℕ)) + (26942 : ℝ) * (t ^ (11 : ℕ)) + (10692 : ℝ) * (t ^ (13 : ℕ)) + (46446921 / 4096 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (789597657 / 4000000000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (70833639 / 2048 : ℝ) * (t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (1204171863 / 800000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (21512269 / 512 : ℝ) * (t ^ (5 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (365708573 / 80000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (2083147 / 64 : ℝ) * (t ^ (7 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (35413499 / 4000000000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (105371 / 8 : ℝ) * (t ^ (9 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (1791307 / 200000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (14387 / 8 : ℝ) * (t ^ (11 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (244579 / 80000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (11719707 / 4096 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (3386995323 / 6400000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (18409589 / 4096 : ℝ) * (t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (5320371221 / 2560000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (715991 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (33633 / 128 : ℝ) * (t ^ (7 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (9719937 / 12800000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (45511 / 32 : ℝ) * (t ^ (9 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (13152679 / 1280000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (2002689 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (82657 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (94637 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (19753 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (1504899 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (135679 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (26353 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (7791 / 512 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (5 : ℕ) - l ^ (5 : ℕ))) + (11062105887 / 3276800000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (231 / 128 : ℝ) * (t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (5 : ℕ) - l ^ (5 : ℕ))) + (327986967 / 327680000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (81 / 64 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (6 : ℕ) - l ^ (6 : ℕ))) + (1955143089 / 655360000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (5837353737757393400517204309 / 1250000000000000000000000000 : ℝ) * (t ^ (15 : ℕ)) := by
    unfold skewPlateauMuChiralLine skewPlateauLineForm skewPlateauMuCrossLine skewPlateauMuVVLine
    ring
  have mpos : 0 < t ^ (15 : ℕ) := pow_pos hpos_t 15
  have m0 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sq_nonneg (l - 4 * t ^ (2 : ℕ)))) hg9)
  have m1 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3)) (sq_nonneg (l - 4 * t ^ (2 : ℕ)))) hg9)
  have m2 : 0 ≤ t ^ (3 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (6 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hg9 6))
  have m3 : 0 ≤ t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (5 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) hg10) (pow_nonneg hg9 5))
  have m4 : 0 ≤ t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (4 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hg10 2)) (pow_nonneg hg9 4))
  have m5 : 0 ≤ t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (3 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (3 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hg10 3)) (pow_nonneg hg9 3))
  have m6 : 0 ≤ t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (4 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hg10 4)) (pow_nonneg hg9 2))
  have m7 : 0 ≤ t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (5 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hg10 5)) hg9)
  have m8 : 0 ≤ t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (6 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hg10 6))
  have m9 : 0 ≤ t * (t ^ (14 : ℕ) - 50 ^ (14 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 14)))
  have m10 : 0 ≤ t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 12)))
  have m11 : 0 ≤ t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m12 : 0 ≤ t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m13 : 0 ≤ t ^ (9 : ℕ) := (pow_nonneg ht0 9)
  have m14 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m15 : 0 ≤ t ^ (13 : ℕ) := (pow_nonneg ht0 13)
  have m16 : 0 ≤ t * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 1)))
  have m17 : 0 ≤ t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 12)))
  have m18 : 0 ≤ t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 1)))
  have m19 : 0 ≤ t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m20 : 0 ≤ t ^ (5 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 1)))
  have m21 : 0 ≤ t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m22 : 0 ≤ t ^ (7 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 1)))
  have m23 : 0 ≤ t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m24 : 0 ≤ t ^ (9 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 1)))
  have m25 : 0 ≤ t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m26 : 0 ≤ t ^ (11 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 1)))
  have m27 : 0 ≤ t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m28 : 0 ≤ t * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m29 : 0 ≤ t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m30 : 0 ≤ t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m31 : 0 ≤ t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m32 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2))
  have m33 : 0 ≤ t ^ (7 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m34 : 0 ≤ t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m35 : 0 ≤ t ^ (9 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m36 : 0 ≤ t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m37 : 0 ≤ t * l ^ (3 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 3))
  have m38 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3))
  have m39 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3))
  have m40 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3))
  have m41 : 0 ≤ t * l ^ (4 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 4))
  have m42 : 0 ≤ t ^ (3 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 4))
  have m43 : 0 ≤ t ^ (5 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 4))
  have m44 : 0 ≤ t * ((17 / 4 * t ^ (2 : ℕ)) ^ (5 : ℕ) - l ^ (5 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 5)))
  have m45 : 0 ≤ t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m46 : 0 ≤ t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (5 : ℕ) - l ^ (5 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 5)))
  have m47 : 0 ≤ t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m48 : 0 ≤ t * ((17 / 4 * t ^ (2 : ℕ)) ^ (6 : ℕ) - l ^ (6 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 6)))
  have m49 : 0 ≤ t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m50 : 0 ≤ t ^ (15 : ℕ) := (pow_nonneg ht0 15)
  have h0 : 0 ≤ (3 / 16 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (1 / 4 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (2198528 / 531441 : ℝ) * (t ^ (3 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (6 : ℕ)) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (2603392 / 177147 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (5 : ℕ)) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (2497792 / 177147 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (4 : ℕ)) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (54466 / 531441 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (3 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (3 : ℕ)) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (442537 / 708588 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (4 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (9450497 / 1417176 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (5 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (1573801 / 1062882 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (6 : ℕ)) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (23263191 / 1250000000000000000000000000 : ℝ) * (t * (t ^ (14 : ℕ) - 50 ^ (14 : ℕ))) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (18458023 / 62500000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (4034501 / 3125000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (2482407 / 1250000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (51449 / 8 : ℝ) * (t ^ (9 : ℕ)) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (26942 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (10692 : ℝ) * (t ^ (13 : ℕ)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (46446921 / 4096 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (789597657 / 4000000000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (70833639 / 2048 : ℝ) * (t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (1204171863 / 800000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (21512269 / 512 : ℝ) * (t ^ (5 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (365708573 / 80000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (2083147 / 64 : ℝ) * (t ^ (7 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (35413499 / 4000000000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (105371 / 8 : ℝ) * (t ^ (9 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (1791307 / 200000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (14387 / 8 : ℝ) * (t ^ (11 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (244579 / 80000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (11719707 / 4096 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (3386995323 / 6400000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (18409589 / 4096 : ℝ) * (t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (5320371221 / 2560000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (715991 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (33633 / 128 : ℝ) * (t ^ (7 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (9719937 / 12800000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (45511 / 32 : ℝ) * (t ^ (9 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (13152679 / 1280000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (2002689 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (82657 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (94637 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (19753 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m40
  have h41 : 0 ≤ (1504899 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m41
  have h42 : 0 ≤ (135679 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m42
  have h43 : 0 ≤ (26353 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m43
  have h44 : 0 ≤ (7791 / 512 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (5 : ℕ) - l ^ (5 : ℕ))) := mul_nonneg (by norm_num) m44
  have h45 : 0 ≤ (11062105887 / 3276800000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m45
  have h46 : 0 ≤ (231 / 128 : ℝ) * (t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (5 : ℕ) - l ^ (5 : ℕ))) := mul_nonneg (by norm_num) m46
  have h47 : 0 ≤ (327986967 / 327680000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m47
  have h48 : 0 ≤ (81 / 64 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (6 : ℕ) - l ^ (6 : ℕ))) := mul_nonneg (by norm_num) m48
  have h49 : 0 ≤ (1955143089 / 655360000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m49
  have hlast : 0 < (5837353737757393400517204309 / 1250000000000000000000000000 : ℝ) * (t ^ (15 : ℕ)) := mul_pos (by norm_num) mpos
  have hP : 0 < (3 / 16 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l)) + (1 / 4 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l)) + (2198528 / 531441 : ℝ) * (t ^ (3 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (6 : ℕ)) + (2603392 / 177147 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (5 : ℕ)) + (2497792 / 177147 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (4 : ℕ)) + (54466 / 531441 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (3 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (3 : ℕ)) + (442537 / 708588 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (4 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (9450497 / 1417176 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (5 : ℕ) * (17 / 4 * t ^ (2 : ℕ) - l)) + (1573801 / 1062882 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) ^ (6 : ℕ)) + (23263191 / 1250000000000000000000000000 : ℝ) * (t * (t ^ (14 : ℕ) - 50 ^ (14 : ℕ))) + (18458023 / 62500000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (4034501 / 3125000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (2482407 / 1250000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (51449 / 8 : ℝ) * (t ^ (9 : ℕ)) + (26942 : ℝ) * (t ^ (11 : ℕ)) + (10692 : ℝ) * (t ^ (13 : ℕ)) + (46446921 / 4096 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (789597657 / 4000000000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (70833639 / 2048 : ℝ) * (t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (1204171863 / 800000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (21512269 / 512 : ℝ) * (t ^ (5 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (365708573 / 80000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (2083147 / 64 : ℝ) * (t ^ (7 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (35413499 / 4000000000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (105371 / 8 : ℝ) * (t ^ (9 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (1791307 / 200000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (14387 / 8 : ℝ) * (t ^ (11 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (244579 / 80000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (11719707 / 4096 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (3386995323 / 6400000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (18409589 / 4096 : ℝ) * (t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (5320371221 / 2560000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (715991 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (33633 / 128 : ℝ) * (t ^ (7 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (9719937 / 12800000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (45511 / 32 : ℝ) * (t ^ (9 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (13152679 / 1280000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (2002689 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (82657 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (94637 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (19753 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (1504899 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (135679 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (26353 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (7791 / 512 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (5 : ℕ) - l ^ (5 : ℕ))) + (11062105887 / 3276800000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (231 / 128 : ℝ) * (t ^ (3 : ℕ) * ((17 / 4 * t ^ (2 : ℕ)) ^ (5 : ℕ) - l ^ (5 : ℕ))) + (327986967 / 327680000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (81 / 64 : ℝ) * (t * ((17 / 4 * t ^ (2 : ℕ)) ^ (6 : ℕ) - l ^ (6 : ℕ))) + (1955143089 / 655360000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (5837353737757393400517204309 / 1250000000000000000000000000 : ℝ) * (t ^ (15 : ℕ)) := add_pos_of_nonneg_of_pos (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48) h49) hlast
  rw [key]
  exact hP

/-- For `t ≥ 50` the chiral kernel has positive imaginary part at every harmonic of the spectral
support `0 ≤ l ≤ (17/4)t²`. -/
theorem skewPlateauMuChiral_line_im_pos_support (t l : ℝ) (ht : (50 : ℝ) ≤ t) (hl0 : 0 ≤ l) (h2 : l ≤ 17 / 4 * t ^ (2 : ℕ)) :
    0 < (skewPlateauMuChiral ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im := by
  rcases le_or_gt l (2 * t ^ (2 : ℕ)) with hb | hb
  · exact skewPlateauMuChiral_line_im_pos t l ht hl0 hb
  · have h := congrArg Complex.im (skewPlateauMuChiral_line t l hl0)
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
    have hden := skewPlateauLineDen_pos t l hl0
    have hF := skewPlateauMuChiralLine_pos_edge t l ht hb.le h2
    nlinarith

end RHTower.D4BMScalarStream
