import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewPlateauHarmonic

/-!
# Uniform bound of the scalar-scalar plateau kernel above the low band

On the critical line the plateau kernel at the harmonic `−l` is `i·Form(t,l)/D(t,l)` with the
positive denominator `D = 128(2+l)²((4t²−2−l)² + 36t²)` and the line form
`Form = −(5/64)t⁹l²(l−4t²)² + Lower`, where `Lower` collects the monomials of weight at most `15`
(the weight of `t^j l^k` being `j + 2k`).  For `t ≥ 50` and every harmonic `l ≥ t`,

`|Form(t,l)| ≤ t⁹·D(t,l)`, hence `|Im K(−3/2+it, −l)| ≤ t⁹`.

The leading term is controlled by the product structure of `D`: with `q = 4t²−2−l`,
`(l−4t²)² = (q+2)² ≤ 2q² + 8`, so `(5/64)t⁹l²(l−4t²)² ≤ (5/32)t⁹(2+l)²q² + (5/8)t⁹(2+l)²`, a small
fraction of `128t⁹(2+l)²q² + 4608t¹¹(2+l)²`.  The lower monomials are absorbed on three regions:
`t ≤ l ≤ 2t²`, where `q ≥ 2t²−2` and `(2+l)²q²` expands into nonnegative terms; `2t² ≤ l ≤ 8t²`,
where `l^k ≤ (8t²)^(k−2)·l²` and everything is absorbed by `t¹¹l²`; and `l ≥ 8t²`, where
`q² = l²/4 + (3(l−8t²)/2 + 8t² + 2)((l−8t²)/2 + 2)` makes `t⁹(2+l)²q² ≥ t⁹l⁴/4` explicit.
Each region certificate is an exact polynomial identity with nonnegative coefficients in the
region's nonnegative atoms.

Together with the constant-mode lower bound `t¹¹/2176` this isolates the on-line sign of the
two-rate clock to a comparison of spectral weights: the constant mode dominates as soon as the total
weight above the low band is at most `t²/2176` times the constant-mode weight.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

noncomputable section

theorem skewPlateauLineForm_bound_A_plus (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : t ≤ l) (h2 : l ≤ 2 * t ^ 2) :
    0 ≤ t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) + skewPlateauLineForm t l := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hT : (0 : ℝ) ≤ t - 50 := by linarith
  have hp : (0 : ℝ) ≤ t + 50 := by linarith
  have hs2 : (0 : ℝ) ≤ l + 2 := by linarith
  have hg : (0 : ℝ) ≤ l - t := by linarith
  have hh : (0 : ℝ) ≤ 2 * t ^ (2 : ℕ) - l := by linarith
  have hQ : (0 : ℝ) ≤ 2 * (t - 50) * (t + 50) + 4998 := by nlinarith
  have key : t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) + skewPlateauLineForm t l = (1 / 4000 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ) * l) + (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ)) + (14931 / 20480 : ℝ) * (t * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (14931 / 20480 : ℝ) * (l * (l - t)) + (14931 / 20480 : ℝ) * (t * (l - t)) + (14931 / 100000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (95169 / 4096 : ℝ) * (t ^ (0 : ℕ) * l * (l - t)) + (95169 / 20000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) + (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (58863 / 256 : ℝ) * (t * l * (l - t)) + (58863 / 256 : ℝ) * (t ^ (2 : ℕ) * (l - t)) + (58863 / 25000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) + (896173 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (76823 / 16000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (19053 / 32 : ℝ) * (t ^ (3 : ℕ) * l * (l - t)) + (19053 / 32 : ℝ) * (t ^ (4 : ℕ) * (l - t)) + (19053 / 1250000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) + (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (2667 / 800000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (36367 / 32 : ℝ) * (t ^ (5 : ℕ) * l * (l - t)) + (36367 / 32 : ℝ) * (t ^ (6 : ℕ) * (l - t)) + (36367 / 500000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (16915 / 64 : ℝ) * (t ^ (6 : ℕ) * l * (l - t)) + (3383 / 4000000000 : ℝ) * (t ^ (6 : ℕ) * l ^ (2 : ℕ) * (t ^ (5 : ℕ) - 50 ^ (5 : ℕ))) + (1253 / 160000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (639 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) + (3151 / 8 : ℝ) * (t ^ (7 : ℕ) * l * (l - t)) + (3151 / 8 : ℝ) * (t ^ (8 : ℕ) * (l - t)) + (3151 / 50000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2259 / 8 : ℝ) * (t ^ (8 : ℕ) * l * (l - t)) + (2259 / 1000000 : ℝ) * (t ^ (8 : ℕ) * l ^ (2 : ℕ) * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ))) + (943 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (46 : ℝ) * (t ^ (11 : ℕ) * l ^ (0 : ℕ)) + (443 / 8 : ℝ) * (t ^ (10 : ℕ) * l * (l - t)) + (443 / 400 : ℝ) * (t ^ (10 : ℕ) * l ^ (2 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (36 : ℝ) * (t ^ (13 : ℕ) * l ^ (0 : ℕ)) + (29 / 2 : ℝ) * (t ^ (12 : ℕ) * l * (l - t)) + (29 / 100 : ℝ) * (t ^ (12 : ℕ) * l ^ (2 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (29 / 100 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (8 : ℝ) * (t ^ (15 : ℕ) * l ^ (0 : ℕ)) + (7189222876393271432280191 / 1562500000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ) * l) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ)) + (102217 / 800 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (4091 / 16 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) * (2 * (t - 50) * (t + 50) + 4998)) + (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have m0 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) hT) hp)
  have m1 : 0 ≤ t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (sq_nonneg (4 * t ^ (2 : ℕ) - 2 - l)))
  have m2 : 0 ≤ t ^ (9 : ℕ) := (pow_nonneg ht0 9)
  have m3 : 0 ≤ t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) (sq_nonneg (4 * t ^ (2 : ℕ) - 2 - l)))
  have m4 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m5 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sq_nonneg (4 * t ^ (2 : ℕ) - 4 - l)))
  have m6 : 0 ≤ t * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 1)))
  have m7 : 0 ≤ l * (l - t) := (mul_nonneg hl0 hg)
  have m8 : 0 ≤ t * (l - t) := (mul_nonneg ht0 hg)
  have m9 : 0 ≤ t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 0) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 11)))
  have m10 : 0 ≤ t ^ (0 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 0) hl0) hg)
  have m11 : 0 ≤ t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 0) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 11)))
  have m12 : 0 ≤ t * l ^ (2 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 2))
  have m13 : 0 ≤ t * l ^ (3 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 3))
  have m14 : 0 ≤ t * l ^ (4 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 4))
  have m15 : 0 ≤ t * l * (l - t) := (mul_nonneg (mul_nonneg ht0 hl0) hg)
  have m16 : 0 ≤ t ^ (2 : ℕ) * (l - t) := (mul_nonneg (pow_nonneg ht0 2) hg)
  have m17 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m18 : 0 ≤ t ^ (3 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 3) hl0)
  have m19 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m20 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) hh)
  have m21 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m22 : 0 ≤ t ^ (3 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 4))
  have m23 : 0 ≤ t ^ (3 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) hl0) hg)
  have m24 : 0 ≤ t ^ (4 : ℕ) * (l - t) := (mul_nonneg (pow_nonneg ht0 4) hg)
  have m25 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m26 : 0 ≤ t ^ (5 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 5) hl0)
  have m27 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2))
  have m28 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) hh)
  have m29 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m30 : 0 ≤ t ^ (5 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 4))
  have m31 : 0 ≤ t ^ (5 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) hl0) hg)
  have m32 : 0 ≤ t ^ (6 : ℕ) * (l - t) := (mul_nonneg (pow_nonneg ht0 6) hg)
  have m33 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m34 : 0 ≤ t ^ (6 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 6) hl0) hg)
  have m35 : 0 ≤ t ^ (6 : ℕ) * l ^ (2 : ℕ) * (t ^ (5 : ℕ) - 50 ^ (5 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 6) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 5)))
  have m36 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m37 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) hh)
  have m38 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m39 : 0 ≤ t ^ (7 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 4))
  have m40 : 0 ≤ t ^ (7 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) hl0) hg)
  have m41 : 0 ≤ t ^ (8 : ℕ) * (l - t) := (mul_nonneg (pow_nonneg ht0 8) hg)
  have m42 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m43 : 0 ≤ t ^ (8 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 8) hl0) hg)
  have m44 : 0 ≤ t ^ (8 : ℕ) * l ^ (2 : ℕ) * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 8) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 3)))
  have m45 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m46 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) hh)
  have m47 : 0 ≤ t ^ (11 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 0))
  have m48 : 0 ≤ t ^ (10 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 10) hl0) hg)
  have m49 : 0 ≤ t ^ (10 : ℕ) * l ^ (2 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 10) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 1)))
  have m50 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have m51 : 0 ≤ t ^ (13 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 13) (pow_nonneg hl0 0))
  have m52 : 0 ≤ t ^ (12 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 12) hl0) hg)
  have m53 : 0 ≤ t ^ (12 : ℕ) * l ^ (2 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 12) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 1)))
  have m54 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m55 : 0 ≤ t ^ (15 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 15) (pow_nonneg hl0 0))
  have m56 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have m57 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m58 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m59 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (pow_nonneg hQ 2))
  have m60 : 0 ≤ t ^ (9 : ℕ) * l * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) (pow_nonneg hQ 2))
  have m61 : 0 ≤ t ^ (9 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hQ 2))
  have m62 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) * (2 * (t - 50) * (t + 50) + 4998) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) hh) hQ)
  have m63 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) (pow_nonneg hh 2))
  have h0 : 0 ≤ (1 / 4000 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (5 / 8 : ℝ) * (t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (5 / 2 : ℝ) * (t ^ (9 : ℕ)) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (5 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (5 / 2 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (14931 / 20480 : ℝ) * (t * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (14931 / 20480 : ℝ) * (l * (l - t)) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (14931 / 20480 : ℝ) * (t * (l - t)) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (14931 / 100000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (95169 / 4096 : ℝ) * (t ^ (0 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (95169 / 20000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (58863 / 256 : ℝ) * (t * l * (l - t)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (58863 / 256 : ℝ) * (t ^ (2 : ℕ) * (l - t)) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (58863 / 25000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (896173 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (76823 / 16000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (19053 / 32 : ℝ) * (t ^ (3 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (19053 / 32 : ℝ) * (t ^ (4 : ℕ) * (l - t)) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (19053 / 1250000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (2667 / 800000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (36367 / 32 : ℝ) * (t ^ (5 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (36367 / 32 : ℝ) * (t ^ (6 : ℕ) * (l - t)) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (36367 / 500000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (16915 / 64 : ℝ) * (t ^ (6 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (3383 / 4000000000 : ℝ) * (t ^ (6 : ℕ) * l ^ (2 : ℕ) * (t ^ (5 : ℕ) - 50 ^ (5 : ℕ))) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (1253 / 160000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (639 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (3151 / 8 : ℝ) * (t ^ (7 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m40
  have h41 : 0 ≤ (3151 / 8 : ℝ) * (t ^ (8 : ℕ) * (l - t)) := mul_nonneg (by norm_num) m41
  have h42 : 0 ≤ (3151 / 50000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m42
  have h43 : 0 ≤ (2259 / 8 : ℝ) * (t ^ (8 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m43
  have h44 : 0 ≤ (2259 / 1000000 : ℝ) * (t ^ (8 : ℕ) * l ^ (2 : ℕ) * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ))) := mul_nonneg (by norm_num) m44
  have h45 : 0 ≤ (943 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m45
  have h46 : 0 ≤ (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m46
  have h47 : 0 ≤ (46 : ℝ) * (t ^ (11 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m47
  have h48 : 0 ≤ (443 / 8 : ℝ) * (t ^ (10 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m48
  have h49 : 0 ≤ (443 / 400 : ℝ) * (t ^ (10 : ℕ) * l ^ (2 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) := mul_nonneg (by norm_num) m49
  have h50 : 0 ≤ (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m50
  have h51 : 0 ≤ (36 : ℝ) * (t ^ (13 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m51
  have h52 : 0 ≤ (29 / 2 : ℝ) * (t ^ (12 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m52
  have h53 : 0 ≤ (29 / 100 : ℝ) * (t ^ (12 : ℕ) * l ^ (2 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) := mul_nonneg (by norm_num) m53
  have h54 : 0 ≤ (29 / 100 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m54
  have h55 : 0 ≤ (8 : ℝ) * (t ^ (15 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m55
  have h56 : 0 ≤ (7189222876393271432280191 / 1562500000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m56
  have h57 : 0 ≤ (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m57
  have h58 : 0 ≤ (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m58
  have h59 : 0 ≤ (102217 / 800 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m59
  have h60 : 0 ≤ (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m60
  have h61 : 0 ≤ (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m61
  have h62 : 0 ≤ (4091 / 16 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) * (2 * (t - 50) * (t + 50) + 4998)) := mul_nonneg (by norm_num) m62
  have h63 : 0 ≤ (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m63
  have hP : 0 ≤ (1 / 4000 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ) * l) + (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ)) + (14931 / 20480 : ℝ) * (t * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (14931 / 20480 : ℝ) * (l * (l - t)) + (14931 / 20480 : ℝ) * (t * (l - t)) + (14931 / 100000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (95169 / 4096 : ℝ) * (t ^ (0 : ℕ) * l * (l - t)) + (95169 / 20000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) + (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (58863 / 256 : ℝ) * (t * l * (l - t)) + (58863 / 256 : ℝ) * (t ^ (2 : ℕ) * (l - t)) + (58863 / 25000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) + (896173 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (76823 / 16000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (19053 / 32 : ℝ) * (t ^ (3 : ℕ) * l * (l - t)) + (19053 / 32 : ℝ) * (t ^ (4 : ℕ) * (l - t)) + (19053 / 1250000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) + (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (2667 / 800000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (36367 / 32 : ℝ) * (t ^ (5 : ℕ) * l * (l - t)) + (36367 / 32 : ℝ) * (t ^ (6 : ℕ) * (l - t)) + (36367 / 500000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (16915 / 64 : ℝ) * (t ^ (6 : ℕ) * l * (l - t)) + (3383 / 4000000000 : ℝ) * (t ^ (6 : ℕ) * l ^ (2 : ℕ) * (t ^ (5 : ℕ) - 50 ^ (5 : ℕ))) + (1253 / 160000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (639 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) + (3151 / 8 : ℝ) * (t ^ (7 : ℕ) * l * (l - t)) + (3151 / 8 : ℝ) * (t ^ (8 : ℕ) * (l - t)) + (3151 / 50000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2259 / 8 : ℝ) * (t ^ (8 : ℕ) * l * (l - t)) + (2259 / 1000000 : ℝ) * (t ^ (8 : ℕ) * l ^ (2 : ℕ) * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ))) + (943 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (46 : ℝ) * (t ^ (11 : ℕ) * l ^ (0 : ℕ)) + (443 / 8 : ℝ) * (t ^ (10 : ℕ) * l * (l - t)) + (443 / 400 : ℝ) * (t ^ (10 : ℕ) * l ^ (2 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (36 : ℝ) * (t ^ (13 : ℕ) * l ^ (0 : ℕ)) + (29 / 2 : ℝ) * (t ^ (12 : ℕ) * l * (l - t)) + (29 / 100 : ℝ) * (t ^ (12 : ℕ) * l ^ (2 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (29 / 100 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (8 : ℝ) * (t ^ (15 : ℕ) * l ^ (0 : ℕ)) + (7189222876393271432280191 / 1562500000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ) * l) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ)) + (102217 / 800 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (4091 / 16 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) * (2 * (t - 50) * (t + 50) + 4998)) + (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48) h49) h50) h51) h52) h53) h54) h55) h56) h57) h58) h59) h60) h61) h62) h63)
  rw [key]
  exact hP

theorem skewPlateauLineForm_bound_A_minus (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : t ≤ l) (h2 : l ≤ 2 * t ^ 2) :
    0 ≤ t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) - skewPlateauLineForm t l := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hT : (0 : ℝ) ≤ t - 50 := by linarith
  have hp : (0 : ℝ) ≤ t + 50 := by linarith
  have hs2 : (0 : ℝ) ≤ l + 2 := by linarith
  have hg : (0 : ℝ) ≤ l - t := by linarith
  have hh : (0 : ℝ) ≤ 2 * t ^ (2 : ℕ) - l := by linarith
  have hQ : (0 : ℝ) ≤ 2 * (t - 50) * (t + 50) + 4998 := by nlinarith
  have key : t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) - skewPlateauLineForm t l = (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (74655 / 2048 : ℝ) * (t * l ^ (0 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (238617 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (226443 / 16384 : ℝ) * (t * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (226443 / 8192 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (226443 / 64000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ) * l ^ (0 : ℕ)) + (728753 / 2048 : ℝ) * (t ^ (2 : ℕ) * l * (l - t)) + (728753 / 4000000000000000000 : ℝ) * (t ^ (2 : ℕ) * l ^ (2 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ))) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (11623 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (11623 / 1600000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (0 : ℕ)) + (402363 / 512 : ℝ) * (t ^ (4 : ℕ) * l * (l - t)) + (402363 / 400000000000000 : ℝ) * (t ^ (4 : ℕ) * l ^ (2 : ℕ) * (t ^ (7 : ℕ) - 50 ^ (7 : ℕ))) + (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (2249 / 256 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (2249 / 320000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ) * l ^ (0 : ℕ)) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (31 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (0 : ℕ)) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (46 : ℝ) * (t ^ (9 : ℕ) * l * (l - t)) + (46 : ℝ) * (t ^ (10 : ℕ) * (l - t)) + (23 / 1250 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (36 : ℝ) * (t ^ (11 : ℕ) * l * (l - t)) + (36 : ℝ) * (t ^ (12 : ℕ) * (l - t)) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (8 : ℝ) * (t ^ (13 : ℕ) * l * (l - t)) + (8 : ℝ) * (t ^ (14 : ℕ) * (l - t)) + (8 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (364087965168200264761391 / 80000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18432 : ℝ) * (t ^ (11 : ℕ) * l) + (18432 : ℝ) * (t ^ (11 : ℕ)) + (126 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (512 : ℝ) * (t ^ (9 : ℕ) * l * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (512 : ℝ) * (t ^ (9 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (256 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) * (2 * (t - 50) * (t + 50) + 4998)) + (128 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have m0 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sq_nonneg (4 * t ^ (2 : ℕ) - l)))
  have m1 : 0 ≤ t * l ^ (0 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 0))
  have m2 : 0 ≤ t * l := (mul_nonneg ht0 hl0)
  have m3 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m4 : 0 ≤ t * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) hh)
  have m5 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m6 : 0 ≤ t * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 3)) hh)
  have m7 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) hh)
  have m8 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m9 : 0 ≤ t ^ (3 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 0))
  have m10 : 0 ≤ t ^ (2 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 2) hl0) hg)
  have m11 : 0 ≤ t ^ (2 : ℕ) * l ^ (2 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 2) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 9)))
  have m12 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2))
  have m13 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3))
  have m14 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3)) hh)
  have m15 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) hh)
  have m16 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m17 : 0 ≤ t ^ (5 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 0))
  have m18 : 0 ≤ t ^ (4 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 4) hl0) hg)
  have m19 : 0 ≤ t ^ (4 : ℕ) * l ^ (2 : ℕ) * (t ^ (7 : ℕ) - 50 ^ (7 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 4) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 7)))
  have m20 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m21 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3))
  have m22 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3)) hh)
  have m23 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) hh)
  have m24 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m25 : 0 ≤ t ^ (7 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 0))
  have m26 : 0 ≤ t ^ (7 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 7) hl0)
  have m27 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2))
  have m28 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3))
  have m29 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3)) hh)
  have m30 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) hh)
  have m31 : 0 ≤ t ^ (9 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 0))
  have m32 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m33 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m34 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3))
  have m35 : 0 ≤ t ^ (9 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) hg)
  have m36 : 0 ≤ t ^ (10 : ℕ) * (l - t) := (mul_nonneg (pow_nonneg ht0 10) hg)
  have m37 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m38 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m39 : 0 ≤ t ^ (11 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) hl0) hg)
  have m40 : 0 ≤ t ^ (12 : ℕ) * (l - t) := (mul_nonneg (pow_nonneg ht0 12) hg)
  have m41 : 0 ≤ t ^ (13 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 13) hl0)
  have m42 : 0 ≤ t ^ (13 : ℕ) * l * (l - t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 13) hl0) hg)
  have m43 : 0 ≤ t ^ (14 : ℕ) * (l - t) := (mul_nonneg (pow_nonneg ht0 14) hg)
  have m44 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m45 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have m46 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m47 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m48 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (pow_nonneg hQ 2))
  have m49 : 0 ≤ t ^ (9 : ℕ) * l * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) (pow_nonneg hQ 2))
  have m50 : 0 ≤ t ^ (9 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hQ 2))
  have m51 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) * (2 * (t - 50) * (t + 50) + 4998) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) hh) hQ)
  have m52 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) (pow_nonneg hh 2))
  have h0 : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (74655 / 2048 : ℝ) * (t * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (95169 / 4096 : ℝ) * (t * l) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (238617 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (226443 / 16384 : ℝ) * (t * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (226443 / 8192 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (226443 / 64000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (58863 / 256 : ℝ) * (t ^ (3 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (728753 / 2048 : ℝ) * (t ^ (2 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (728753 / 4000000000000000000 : ℝ) * (t ^ (2 : ℕ) * l ^ (2 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ))) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (11623 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (11623 / 1600000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (19053 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (402363 / 512 : ℝ) * (t ^ (4 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (402363 / 400000000000000 : ℝ) * (t ^ (4 : ℕ) * l ^ (2 : ℕ) * (t ^ (7 : ℕ) - 50 ^ (7 : ℕ))) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (2249 / 256 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (2249 / 320000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (36367 / 32 : ℝ) * (t ^ (7 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (31 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (3151 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (46 : ℝ) * (t ^ (9 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (46 : ℝ) * (t ^ (10 : ℕ) * (l - t)) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (23 / 1250 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (36 : ℝ) * (t ^ (11 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (36 : ℝ) * (t ^ (12 : ℕ) * (l - t)) := mul_nonneg (by norm_num) m40
  have h41 : 0 ≤ (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) := mul_nonneg (by norm_num) m41
  have h42 : 0 ≤ (8 : ℝ) * (t ^ (13 : ℕ) * l * (l - t)) := mul_nonneg (by norm_num) m42
  have h43 : 0 ≤ (8 : ℝ) * (t ^ (14 : ℕ) * (l - t)) := mul_nonneg (by norm_num) m43
  have h44 : 0 ≤ (8 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m44
  have h45 : 0 ≤ (364087965168200264761391 / 80000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m45
  have h46 : 0 ≤ (18432 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m46
  have h47 : 0 ≤ (18432 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m47
  have h48 : 0 ≤ (126 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m48
  have h49 : 0 ≤ (512 : ℝ) * (t ^ (9 : ℕ) * l * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m49
  have h50 : 0 ≤ (512 : ℝ) * (t ^ (9 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m50
  have h51 : 0 ≤ (256 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) * (2 * (t - 50) * (t + 50) + 4998)) := mul_nonneg (by norm_num) m51
  have h52 : 0 ≤ (128 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m52
  have hP : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (74655 / 2048 : ℝ) * (t * l ^ (0 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (238617 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (226443 / 16384 : ℝ) * (t * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (226443 / 8192 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (226443 / 64000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ) * l ^ (0 : ℕ)) + (728753 / 2048 : ℝ) * (t ^ (2 : ℕ) * l * (l - t)) + (728753 / 4000000000000000000 : ℝ) * (t ^ (2 : ℕ) * l ^ (2 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ))) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (11623 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (11623 / 1600000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (0 : ℕ)) + (402363 / 512 : ℝ) * (t ^ (4 : ℕ) * l * (l - t)) + (402363 / 400000000000000 : ℝ) * (t ^ (4 : ℕ) * l ^ (2 : ℕ) * (t ^ (7 : ℕ) - 50 ^ (7 : ℕ))) + (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (2249 / 256 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (2249 / 320000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ) * l ^ (0 : ℕ)) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (31 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (0 : ℕ)) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (46 : ℝ) * (t ^ (9 : ℕ) * l * (l - t)) + (46 : ℝ) * (t ^ (10 : ℕ) * (l - t)) + (23 / 1250 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (36 : ℝ) * (t ^ (11 : ℕ) * l * (l - t)) + (36 : ℝ) * (t ^ (12 : ℕ) * (l - t)) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (8 : ℝ) * (t ^ (13 : ℕ) * l * (l - t)) + (8 : ℝ) * (t ^ (14 : ℕ) * (l - t)) + (8 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (364087965168200264761391 / 80000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18432 : ℝ) * (t ^ (11 : ℕ) * l) + (18432 : ℝ) * (t ^ (11 : ℕ)) + (126 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (512 : ℝ) * (t ^ (9 : ℕ) * l * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (512 : ℝ) * (t ^ (9 : ℕ) * (2 * (t - 50) * (t + 50) + 4998) ^ (2 : ℕ)) + (256 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) * (2 * (t - 50) * (t + 50) + 4998)) + (128 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48) h49) h50) h51) h52)
  rw [key]
  exact hP

theorem skewPlateauLineForm_bound_B1_plus (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : 2 * t ^ 2 ≤ l) (h2 : l ≤ 8 * t ^ 2) :
    0 ≤ t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) + skewPlateauLineForm t l := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hT : (0 : ℝ) ≤ t - 50 := by linarith
  have hp : (0 : ℝ) ≤ t + 50 := by linarith
  have hs2 : (0 : ℝ) ≤ l + 2 := by linarith
  have hv : (0 : ℝ) ≤ l - 2 * t ^ (2 : ℕ) := by linarith
  have hw : (0 : ℝ) ≤ 8 * t ^ (2 : ℕ) - l := by linarith
  have key : t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) + skewPlateauLineForm t l = (1 / 4000 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ) * l) + (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ)) + (14931 / 51200000 : ℝ) * (t * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ))) + (14931 / 204800000 : ℝ) * (l * (l - 2 * t ^ (2 : ℕ))) + (14931 / 102400000 : ℝ) * (t ^ (2 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (14931 / 1000000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (95169 / 204800 : ℝ) * (t * l * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (95169 / 409600 : ℝ) * (l * (l - 2 * t ^ (2 : ℕ))) + (95169 / 2000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) + (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (58863 / 12800 : ℝ) * (t ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (58863 / 51200 : ℝ) * (l * (l - 2 * t ^ (2 : ℕ))) + (58863 / 25600 : ℝ) * (t ^ (2 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (58863 / 250000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) + (896173 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (76823 / 4000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (19053 / 128 : ℝ) * (t * l * (l - 2 * t ^ (2 : ℕ))) + (19053 / 64 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (19053 / 12500000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) + (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (2667 / 200000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (36367 / 128 : ℝ) * (t ^ (3 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (36367 / 64 : ℝ) * (t ^ (5 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (36367 / 5000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (16915 / 128 : ℝ) * (t ^ (5 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (3383 / 400000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (1253 / 160000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (639 / 20000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) + (3151 / 32 : ℝ) * (t ^ (5 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (3151 / 16 : ℝ) * (t ^ (7 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (3151 / 500000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2259 / 16 : ℝ) * (t ^ (7 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (2259 / 100000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (943 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (46 : ℝ) * (t ^ (11 : ℕ) * l ^ (0 : ℕ)) + (443 / 16 : ℝ) * (t ^ (9 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (443 / 40000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (36 : ℝ) * (t ^ (13 : ℕ) * l ^ (0 : ℕ)) + (29 / 4 : ℝ) * (t ^ (11 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (8 : ℝ) * (t ^ (15 : ℕ) * l ^ (0 : ℕ)) + (4579944893709771873994226948569 / 1000000000000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ) * l) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ)) + (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have m0 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) hT) hp)
  have m1 : 0 ≤ t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (sq_nonneg (4 * t ^ (2 : ℕ) - 2 - l)))
  have m2 : 0 ≤ t ^ (9 : ℕ) := (pow_nonneg ht0 9)
  have m3 : 0 ≤ t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) (sq_nonneg (4 * t ^ (2 : ℕ) - 2 - l)))
  have m4 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m5 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sq_nonneg (4 * t ^ (2 : ℕ) - 4 - l)))
  have m6 : 0 ≤ t * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 3)))
  have m7 : 0 ≤ l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg hl0 hv)
  have m8 : 0 ≤ t ^ (2 : ℕ) * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 2) hv)
  have m9 : 0 ≤ t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 0) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 11)))
  have m10 : 0 ≤ t * l * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ)) := (mul_nonneg (mul_nonneg ht0 hl0) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 1)))
  have m11 : 0 ≤ l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg hl0 hv)
  have m12 : 0 ≤ t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 0) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 11)))
  have m13 : 0 ≤ t * l ^ (2 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 2))
  have m14 : 0 ≤ t * l ^ (3 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 3))
  have m15 : 0 ≤ t * l ^ (4 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 4))
  have m16 : 0 ≤ t ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 1)))
  have m17 : 0 ≤ l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg hl0 hv)
  have m18 : 0 ≤ t ^ (2 : ℕ) * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 2) hv)
  have m19 : 0 ≤ t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 0) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 11)))
  have m20 : 0 ≤ t ^ (3 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 3) hl0)
  have m21 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m22 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) hw)
  have m23 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m24 : 0 ≤ t ^ (3 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 4))
  have m25 : 0 ≤ t * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg ht0 hl0) hv)
  have m26 : 0 ≤ t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) hv)
  have m27 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m28 : 0 ≤ t ^ (5 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 5) hl0)
  have m29 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2))
  have m30 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) hw)
  have m31 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m32 : 0 ≤ t ^ (5 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 4))
  have m33 : 0 ≤ t ^ (3 : ℕ) * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) hl0) hv)
  have m34 : 0 ≤ t ^ (5 : ℕ) * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) hv)
  have m35 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m36 : 0 ≤ t ^ (5 : ℕ) * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) hl0) hv)
  have m37 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m38 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m39 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) hw)
  have m40 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m41 : 0 ≤ t ^ (7 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 4))
  have m42 : 0 ≤ t ^ (5 : ℕ) * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) hl0) hv)
  have m43 : 0 ≤ t ^ (7 : ℕ) * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) hv)
  have m44 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m45 : 0 ≤ t ^ (7 : ℕ) * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) hl0) hv)
  have m46 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m47 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m48 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) hw)
  have m49 : 0 ≤ t ^ (11 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 0))
  have m50 : 0 ≤ t ^ (9 : ℕ) * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) hv)
  have m51 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m52 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have m53 : 0 ≤ t ^ (13 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 13) (pow_nonneg hl0 0))
  have m54 : 0 ≤ t ^ (11 : ℕ) * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) hl0) hv)
  have m55 : 0 ≤ t ^ (15 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 15) (pow_nonneg hl0 0))
  have m56 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have m57 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m58 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m59 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) (sq_nonneg (4 * t ^ (2 : ℕ) - 2 - l)))
  have h0 : 0 ≤ (1 / 4000 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (5 / 8 : ℝ) * (t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (5 / 2 : ℝ) * (t ^ (9 : ℕ)) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (5 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (5 / 2 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (14931 / 51200000 : ℝ) * (t * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ))) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (14931 / 204800000 : ℝ) * (l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (14931 / 102400000 : ℝ) * (t ^ (2 : ℕ) * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (14931 / 1000000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (95169 / 204800 : ℝ) * (t * l * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (95169 / 409600 : ℝ) * (l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (95169 / 2000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (58863 / 12800 : ℝ) * (t ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (58863 / 51200 : ℝ) * (l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (58863 / 25600 : ℝ) * (t ^ (2 : ℕ) * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (58863 / 250000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (896173 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (76823 / 4000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (19053 / 128 : ℝ) * (t * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (19053 / 64 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (19053 / 12500000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (2667 / 200000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (36367 / 128 : ℝ) * (t ^ (3 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (36367 / 64 : ℝ) * (t ^ (5 : ℕ) * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (36367 / 5000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (16915 / 128 : ℝ) * (t ^ (5 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (3383 / 400000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (1253 / 160000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (639 / 20000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m40
  have h41 : 0 ≤ (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m41
  have h42 : 0 ≤ (3151 / 32 : ℝ) * (t ^ (5 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m42
  have h43 : 0 ≤ (3151 / 16 : ℝ) * (t ^ (7 : ℕ) * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m43
  have h44 : 0 ≤ (3151 / 500000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m44
  have h45 : 0 ≤ (2259 / 16 : ℝ) * (t ^ (7 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m45
  have h46 : 0 ≤ (2259 / 100000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m46
  have h47 : 0 ≤ (943 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m47
  have h48 : 0 ≤ (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m48
  have h49 : 0 ≤ (46 : ℝ) * (t ^ (11 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m49
  have h50 : 0 ≤ (443 / 16 : ℝ) * (t ^ (9 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m50
  have h51 : 0 ≤ (443 / 40000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m51
  have h52 : 0 ≤ (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m52
  have h53 : 0 ≤ (36 : ℝ) * (t ^ (13 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m53
  have h54 : 0 ≤ (29 / 4 : ℝ) * (t ^ (11 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m54
  have h55 : 0 ≤ (8 : ℝ) * (t ^ (15 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m55
  have h56 : 0 ≤ (4579944893709771873994226948569 / 1000000000000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m56
  have h57 : 0 ≤ (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m57
  have h58 : 0 ≤ (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m58
  have h59 : 0 ≤ (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m59
  have hP : 0 ≤ (1 / 4000 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ) * l) + (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ)) + (14931 / 51200000 : ℝ) * (t * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ))) + (14931 / 204800000 : ℝ) * (l * (l - 2 * t ^ (2 : ℕ))) + (14931 / 102400000 : ℝ) * (t ^ (2 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (14931 / 1000000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (95169 / 204800 : ℝ) * (t * l * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (95169 / 409600 : ℝ) * (l * (l - 2 * t ^ (2 : ℕ))) + (95169 / 2000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) + (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (58863 / 12800 : ℝ) * (t ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (58863 / 51200 : ℝ) * (l * (l - 2 * t ^ (2 : ℕ))) + (58863 / 25600 : ℝ) * (t ^ (2 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (58863 / 250000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) + (896173 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (76823 / 4000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (19053 / 128 : ℝ) * (t * l * (l - 2 * t ^ (2 : ℕ))) + (19053 / 64 : ℝ) * (t ^ (3 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (19053 / 12500000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) + (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (2667 / 200000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (36367 / 128 : ℝ) * (t ^ (3 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (36367 / 64 : ℝ) * (t ^ (5 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (36367 / 5000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (16915 / 128 : ℝ) * (t ^ (5 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (3383 / 400000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (1253 / 160000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (639 / 20000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) + (3151 / 32 : ℝ) * (t ^ (5 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (3151 / 16 : ℝ) * (t ^ (7 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (3151 / 500000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2259 / 16 : ℝ) * (t ^ (7 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (2259 / 100000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (943 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (46 : ℝ) * (t ^ (11 : ℕ) * l ^ (0 : ℕ)) + (443 / 16 : ℝ) * (t ^ (9 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (443 / 40000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (36 : ℝ) * (t ^ (13 : ℕ) * l ^ (0 : ℕ)) + (29 / 4 : ℝ) * (t ^ (11 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (8 : ℝ) * (t ^ (15 : ℕ) * l ^ (0 : ℕ)) + (4579944893709771873994226948569 / 1000000000000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ) * l) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ)) + (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48) h49) h50) h51) h52) h53) h54) h55) h56) h57) h58) h59)
  rw [key]
  exact hP

theorem skewPlateauLineForm_bound_B1_minus (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : 2 * t ^ 2 ≤ l) (h2 : l ≤ 8 * t ^ 2) :
    0 ≤ t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) - skewPlateauLineForm t l := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hT : (0 : ℝ) ≤ t - 50 := by linarith
  have hp : (0 : ℝ) ≤ t + 50 := by linarith
  have hs2 : (0 : ℝ) ≤ l + 2 := by linarith
  have hv : (0 : ℝ) ≤ l - 2 * t ^ (2 : ℕ) := by linarith
  have hw : (0 : ℝ) ≤ 8 * t ^ (2 : ℕ) - l := by linarith
  have key : t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) - skewPlateauLineForm t l = (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (74655 / 2048 : ℝ) * (t * l ^ (0 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (238617 / 40000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (226443 / 16384 : ℝ) * (t * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (226443 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (226443 / 4000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ) * l ^ (0 : ℕ)) + (728753 / 4096 : ℝ) * (t * l * (l - 2 * t ^ (2 : ℕ))) + (728753 / 400000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (11623 / 128 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (11623 / 100000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (0 : ℕ)) + (402363 / 1024 : ℝ) * (t ^ (3 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (402363 / 40000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (2249 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (2249 / 20000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ) * l ^ (0 : ℕ)) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (31 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (0 : ℕ)) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (23 / 2 : ℝ) * (t ^ (7 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (23 : ℝ) * (t ^ (9 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (23 / 12500000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (9 : ℝ) * (t ^ (9 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (18 : ℝ) * (t ^ (11 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (9 / 2500 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (2 : ℝ) * (t ^ (11 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (4 : ℝ) * (t ^ (13 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (914389266373959457223001 / 200000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18432 : ℝ) * (t ^ (11 : ℕ) * l) + (18432 : ℝ) * (t ^ (11 : ℕ)) + (128 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have m0 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sq_nonneg (4 * t ^ (2 : ℕ) - l)))
  have m1 : 0 ≤ t * l ^ (0 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 0))
  have m2 : 0 ≤ t * l := (mul_nonneg ht0 hl0)
  have m3 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m4 : 0 ≤ t * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) hw)
  have m5 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m6 : 0 ≤ t * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 3)) hw)
  have m7 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) hw)
  have m8 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m9 : 0 ≤ t ^ (3 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 0))
  have m10 : 0 ≤ t * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg ht0 hl0) hv)
  have m11 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m12 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2))
  have m13 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3))
  have m14 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3)) hw)
  have m15 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) hw)
  have m16 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m17 : 0 ≤ t ^ (5 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 0))
  have m18 : 0 ≤ t ^ (3 : ℕ) * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) hl0) hv)
  have m19 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m20 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m21 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3))
  have m22 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3)) hw)
  have m23 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) hw)
  have m24 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m25 : 0 ≤ t ^ (7 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 0))
  have m26 : 0 ≤ t ^ (7 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 7) hl0)
  have m27 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2))
  have m28 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3))
  have m29 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3)) hw)
  have m30 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) hw)
  have m31 : 0 ≤ t ^ (9 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 0))
  have m32 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m33 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m34 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3))
  have m35 : 0 ≤ t ^ (7 : ℕ) * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) hl0) hv)
  have m36 : 0 ≤ t ^ (9 : ℕ) * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) hv)
  have m37 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m38 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m39 : 0 ≤ t ^ (9 : ℕ) * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) hv)
  have m40 : 0 ≤ t ^ (11 : ℕ) * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) hv)
  have m41 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m42 : 0 ≤ t ^ (13 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 13) hl0)
  have m43 : 0 ≤ t ^ (11 : ℕ) * l * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) hl0) hv)
  have m44 : 0 ≤ t ^ (13 : ℕ) * (l - 2 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) hv)
  have m45 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have m46 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m47 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m48 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) (sq_nonneg (4 * t ^ (2 : ℕ) - 2 - l)))
  have h0 : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (74655 / 2048 : ℝ) * (t * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (95169 / 4096 : ℝ) * (t * l) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (238617 / 40000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (226443 / 16384 : ℝ) * (t * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (226443 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (226443 / 4000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (58863 / 256 : ℝ) * (t ^ (3 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (728753 / 4096 : ℝ) * (t * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (728753 / 400000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (11623 / 128 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (11623 / 100000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (19053 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (402363 / 1024 : ℝ) * (t ^ (3 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (402363 / 40000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (2249 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (2249 / 20000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (36367 / 32 : ℝ) * (t ^ (7 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (31 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (3151 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (23 / 2 : ℝ) * (t ^ (7 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (23 : ℝ) * (t ^ (9 : ℕ) * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (23 / 12500000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (9 : ℝ) * (t ^ (9 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (18 : ℝ) * (t ^ (11 : ℕ) * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m40
  have h41 : 0 ≤ (9 / 2500 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m41
  have h42 : 0 ≤ (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) := mul_nonneg (by norm_num) m42
  have h43 : 0 ≤ (2 : ℝ) * (t ^ (11 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m43
  have h44 : 0 ≤ (4 : ℝ) * (t ^ (13 : ℕ) * (l - 2 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m44
  have h45 : 0 ≤ (914389266373959457223001 / 200000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m45
  have h46 : 0 ≤ (18432 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m46
  have h47 : 0 ≤ (18432 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m47
  have h48 : 0 ≤ (128 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m48
  have hP : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (74655 / 2048 : ℝ) * (t * l ^ (0 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (238617 / 40000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (226443 / 16384 : ℝ) * (t * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (226443 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (226443 / 4000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ) * l ^ (0 : ℕ)) + (728753 / 4096 : ℝ) * (t * l * (l - 2 * t ^ (2 : ℕ))) + (728753 / 400000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (11623 / 128 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (11623 / 100000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (0 : ℕ)) + (402363 / 1024 : ℝ) * (t ^ (3 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (402363 / 40000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (2249 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (2249 / 20000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ) * l ^ (0 : ℕ)) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (31 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (8 * t ^ (2 : ℕ) - l)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (0 : ℕ)) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (23 / 2 : ℝ) * (t ^ (7 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (23 : ℝ) * (t ^ (9 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (23 / 12500000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (9 : ℝ) * (t ^ (9 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (18 : ℝ) * (t ^ (11 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (9 / 2500 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (2 : ℝ) * (t ^ (11 : ℕ) * l * (l - 2 * t ^ (2 : ℕ))) + (4 : ℝ) * (t ^ (13 : ℕ) * (l - 2 * t ^ (2 : ℕ))) + (914389266373959457223001 / 200000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18432 : ℝ) * (t ^ (11 : ℕ) * l) + (18432 : ℝ) * (t ^ (11 : ℕ)) + (128 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48)
  rw [key]
  exact hP

theorem skewPlateauLineForm_bound_B2_plus (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : 8 * t ^ 2 ≤ l) :
    0 ≤ t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) + skewPlateauLineForm t l := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hT : (0 : ℝ) ≤ t - 50 := by linarith
  have hp : (0 : ℝ) ≤ t + 50 := by linarith
  have hs2 : (0 : ℝ) ≤ l + 2 := by linarith
  have hu : (0 : ℝ) ≤ l - 8 * t ^ (2 : ℕ) := by linarith
  have key : t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) + skewPlateauLineForm t l = (1 / 4000 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ) * l) + (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ)) + (14931 / 51200000 : ℝ) * (t * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ))) + (14931 / 3276800000 : ℝ) * (l * (l - 8 * t ^ (2 : ℕ))) + (14931 / 409600000 : ℝ) * (t ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (14931 / 16000000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (95169 / 204800 : ℝ) * (t * l * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (95169 / 1638400 : ℝ) * (l * (l - 8 * t ^ (2 : ℕ))) + (95169 / 8000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) + (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (58863 / 12800 : ℝ) * (t ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (58863 / 819200 : ℝ) * (l * (l - 8 * t ^ (2 : ℕ))) + (58863 / 102400 : ℝ) * (t ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (58863 / 4000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) + (896173 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (76823 / 16384 : ℝ) * (t * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (76823 / 640000000000000000 : ℝ) * (t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (19053 / 2048 : ℝ) * (t * l * (l - 8 * t ^ (2 : ℕ))) + (19053 / 256 : ℝ) * (t ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (19053 / 200000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) + (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (2667 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (2667 / 32000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (36367 / 2048 : ℝ) * (t ^ (3 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (36367 / 256 : ℝ) * (t ^ (5 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (36367 / 80000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (16915 / 512 : ℝ) * (t ^ (5 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (3383 / 1600000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (1253 / 160000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (639 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (639 / 3200000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) + (3151 / 512 : ℝ) * (t ^ (5 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (3151 / 64 : ℝ) * (t ^ (7 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (3151 / 8000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2259 / 64 : ℝ) * (t ^ (7 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (2259 / 400000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (943 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (83 / 256 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (83 / 640000 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (46 : ℝ) * (t ^ (11 : ℕ) * l ^ (0 : ℕ)) + (443 / 64 : ℝ) * (t ^ (9 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (443 / 160000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (36 : ℝ) * (t ^ (13 : ℕ) * l ^ (0 : ℕ)) + (29 / 16 : ℝ) * (t ^ (11 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (8 : ℝ) * (t ^ (15 : ℕ) * l ^ (0 : ℕ)) + (73698762884299771107775334195069 / 16000000000000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ) * l) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ)) + (20454916872146583177 / 640000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) + (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (12273 / 128 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) ^ (2 : ℕ)) + (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (4091 / 8 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (4091 / 2 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ)) + (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have m0 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) hT) hp)
  have m1 : 0 ≤ t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (sq_nonneg (4 * t ^ (2 : ℕ) - 2 - l)))
  have m2 : 0 ≤ t ^ (9 : ℕ) := (pow_nonneg ht0 9)
  have m3 : 0 ≤ t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) (sq_nonneg (4 * t ^ (2 : ℕ) - 2 - l)))
  have m4 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m5 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sq_nonneg (4 * t ^ (2 : ℕ) - 4 - l)))
  have m6 : 0 ≤ t * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 3)))
  have m7 : 0 ≤ l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg hl0 hu)
  have m8 : 0 ≤ t ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 2) hu)
  have m9 : 0 ≤ t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 0) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 11)))
  have m10 : 0 ≤ t * l * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ)) := (mul_nonneg (mul_nonneg ht0 hl0) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 1)))
  have m11 : 0 ≤ l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg hl0 hu)
  have m12 : 0 ≤ t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 0) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 11)))
  have m13 : 0 ≤ t * l ^ (2 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 2))
  have m14 : 0 ≤ t * l ^ (3 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 3))
  have m15 : 0 ≤ t * l ^ (4 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 4))
  have m16 : 0 ≤ t ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 1)))
  have m17 : 0 ≤ l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg hl0 hu)
  have m18 : 0 ≤ t ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 2) hu)
  have m19 : 0 ≤ t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 0) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 11)))
  have m20 : 0 ≤ t ^ (3 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 3) hl0)
  have m21 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m22 : 0 ≤ t * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 3)) hu)
  have m23 : 0 ≤ t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m24 : 0 ≤ t ^ (3 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 4))
  have m25 : 0 ≤ t * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg ht0 hl0) hu)
  have m26 : 0 ≤ t ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) hu)
  have m27 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m28 : 0 ≤ t ^ (5 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 5) hl0)
  have m29 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2))
  have m30 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3)) hu)
  have m31 : 0 ≤ t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m32 : 0 ≤ t ^ (5 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 4))
  have m33 : 0 ≤ t ^ (3 : ℕ) * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) hl0) hu)
  have m34 : 0 ≤ t ^ (5 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) hu)
  have m35 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m36 : 0 ≤ t ^ (5 : ℕ) * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) hl0) hu)
  have m37 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m38 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m39 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3)) hu)
  have m40 : 0 ≤ t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m41 : 0 ≤ t ^ (7 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 4))
  have m42 : 0 ≤ t ^ (5 : ℕ) * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) hl0) hu)
  have m43 : 0 ≤ t ^ (7 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) hu)
  have m44 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m45 : 0 ≤ t ^ (7 : ℕ) * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) hl0) hu)
  have m46 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m47 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m48 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3)) hu)
  have m49 : 0 ≤ t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m50 : 0 ≤ t ^ (11 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 0))
  have m51 : 0 ≤ t ^ (9 : ℕ) * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) hu)
  have m52 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m53 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have m54 : 0 ≤ t ^ (13 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 13) (pow_nonneg hl0 0))
  have m55 : 0 ≤ t ^ (11 : ℕ) * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) hl0) hu)
  have m56 : 0 ≤ t ^ (15 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 15) (pow_nonneg hl0 0))
  have m57 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have m58 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m59 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m60 : 0 ≤ t ^ (9 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 4))
  have m61 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3))
  have m62 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m63 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) (pow_nonneg hu 2))
  have m64 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) hu)
  have m65 : 0 ≤ t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hs2 2)) hu)
  have m66 : 0 ≤ t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hs2 2))
  have m67 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2))
  have h0 : 0 ≤ (1 / 4000 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (5 / 8 : ℝ) * (t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (5 / 2 : ℝ) * (t ^ (9 : ℕ)) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (5 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (5 / 2 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (14931 / 51200000 : ℝ) * (t * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ))) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (14931 / 3276800000 : ℝ) * (l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (14931 / 409600000 : ℝ) * (t ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (14931 / 16000000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (95169 / 204800 : ℝ) * (t * l * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (95169 / 1638400 : ℝ) * (l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (95169 / 8000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (58863 / 12800 : ℝ) * (t ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (58863 / 819200 : ℝ) * (l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (58863 / 102400 : ℝ) * (t ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (58863 / 4000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (896173 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (76823 / 16384 : ℝ) * (t * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (76823 / 640000000000000000 : ℝ) * (t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (19053 / 2048 : ℝ) * (t * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (19053 / 256 : ℝ) * (t ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (19053 / 200000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (2667 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (2667 / 32000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (36367 / 2048 : ℝ) * (t ^ (3 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (36367 / 256 : ℝ) * (t ^ (5 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (36367 / 80000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (16915 / 512 : ℝ) * (t ^ (5 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (3383 / 1600000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (1253 / 160000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (639 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (639 / 3200000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m40
  have h41 : 0 ≤ (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m41
  have h42 : 0 ≤ (3151 / 512 : ℝ) * (t ^ (5 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m42
  have h43 : 0 ≤ (3151 / 64 : ℝ) * (t ^ (7 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m43
  have h44 : 0 ≤ (3151 / 8000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m44
  have h45 : 0 ≤ (2259 / 64 : ℝ) * (t ^ (7 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m45
  have h46 : 0 ≤ (2259 / 400000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m46
  have h47 : 0 ≤ (943 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m47
  have h48 : 0 ≤ (83 / 256 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m48
  have h49 : 0 ≤ (83 / 640000 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m49
  have h50 : 0 ≤ (46 : ℝ) * (t ^ (11 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m50
  have h51 : 0 ≤ (443 / 64 : ℝ) * (t ^ (9 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m51
  have h52 : 0 ≤ (443 / 160000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m52
  have h53 : 0 ≤ (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m53
  have h54 : 0 ≤ (36 : ℝ) * (t ^ (13 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m54
  have h55 : 0 ≤ (29 / 16 : ℝ) * (t ^ (11 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m55
  have h56 : 0 ≤ (8 : ℝ) * (t ^ (15 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m56
  have h57 : 0 ≤ (73698762884299771107775334195069 / 16000000000000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m57
  have h58 : 0 ≤ (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m58
  have h59 : 0 ≤ (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m59
  have h60 : 0 ≤ (20454916872146583177 / 640000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m60
  have h61 : 0 ≤ (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m61
  have h62 : 0 ≤ (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m62
  have h63 : 0 ≤ (12273 / 128 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m63
  have h64 : 0 ≤ (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m64
  have h65 : 0 ≤ (4091 / 8 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m65
  have h66 : 0 ≤ (4091 / 2 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m66
  have h67 : 0 ≤ (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m67
  have hP : 0 ≤ (1 / 4000 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (t - 50) * (t + 50)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ)) + (5 / 8 : ℝ) * (t ^ (9 : ℕ) * l * (4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ)) + (5 / 2 : ℝ) * (t ^ (9 : ℕ) * l) + (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - 4 - l) ^ (2 : ℕ)) + (14931 / 51200000 : ℝ) * (t * (t ^ (3 : ℕ) - 50 ^ (3 : ℕ))) + (14931 / 3276800000 : ℝ) * (l * (l - 8 * t ^ (2 : ℕ))) + (14931 / 409600000 : ℝ) * (t ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (14931 / 16000000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (95169 / 204800 : ℝ) * (t * l * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (95169 / 1638400 : ℝ) * (l * (l - 8 * t ^ (2 : ℕ))) + (95169 / 8000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (25245 / 4096 : ℝ) * (t * l ^ (2 : ℕ)) + (238617 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (226443 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (58863 / 12800 : ℝ) * (t ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (58863 / 819200 : ℝ) * (l * (l - 8 * t ^ (2 : ℕ))) + (58863 / 102400 : ℝ) * (t ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (58863 / 4000000000000000000000000 : ℝ) * (t ^ (0 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * l) + (896173 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (76823 / 16384 : ℝ) * (t * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (76823 / 640000000000000000 : ℝ) * (t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (19053 / 2048 : ℝ) * (t * l * (l - 8 * t ^ (2 : ℕ))) + (19053 / 256 : ℝ) * (t ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (19053 / 200000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * l) + (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (2667 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (2667 / 32000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (36367 / 2048 : ℝ) * (t ^ (3 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (36367 / 256 : ℝ) * (t ^ (5 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (36367 / 80000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (16915 / 512 : ℝ) * (t ^ (5 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (3383 / 1600000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (1253 / 160000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (639 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (639 / 3200000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ)) + (3151 / 512 : ℝ) * (t ^ (5 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (3151 / 64 : ℝ) * (t ^ (7 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (3151 / 8000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2259 / 64 : ℝ) * (t ^ (7 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (2259 / 400000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (943 / 80000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (83 / 256 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (83 / 640000 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (46 : ℝ) * (t ^ (11 : ℕ) * l ^ (0 : ℕ)) + (443 / 64 : ℝ) * (t ^ (9 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (443 / 160000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (47 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (36 : ℝ) * (t ^ (13 : ℕ) * l ^ (0 : ℕ)) + (29 / 16 : ℝ) * (t ^ (11 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (8 : ℝ) * (t ^ (15 : ℕ) * l ^ (0 : ℕ)) + (73698762884299771107775334195069 / 16000000000000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ) * l) + (18431999 / 1000 : ℝ) * (t ^ (11 : ℕ)) + (20454916872146583177 / 640000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) + (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (4091 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (12273 / 128 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) ^ (2 : ℕ)) + (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (4091 / 8 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (4091 / 2 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ)) + (4091 / 8 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ)) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48) h49) h50) h51) h52) h53) h54) h55) h56) h57) h58) h59) h60) h61) h62) h63) h64) h65) h66) h67)
  rw [key]
  exact hP

theorem skewPlateauLineForm_bound_B2_minus (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : 8 * t ^ 2 ≤ l) :
    0 ≤ t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) - skewPlateauLineForm t l := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hT : (0 : ℝ) ≤ t - 50 := by linarith
  have hp : (0 : ℝ) ≤ t + 50 := by linarith
  have hs2 : (0 : ℝ) ≤ l + 2 := by linarith
  have hu : (0 : ℝ) ≤ l - 8 * t ^ (2 : ℕ) := by linarith
  have key : t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) - skewPlateauLineForm t l = (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (74655 / 2048 : ℝ) * (t * l ^ (0 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (238617 / 409600 : ℝ) * (t * l ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (238617 / 3276800 : ℝ) * (l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (238617 / 6400000000000000000000 : ℝ) * (l ^ (4 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ))) + (226443 / 640000000000000000 : ℝ) * (t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ) * l ^ (0 : ℕ)) + (728753 / 16384 : ℝ) * (t * l * (l - 8 * t ^ (2 : ℕ))) + (728753 / 1600000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (11623 / 16000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (0 : ℕ)) + (402363 / 4096 : ℝ) * (t ^ (3 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (402363 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (2249 / 3200000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ) * l ^ (0 : ℕ)) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (31 / 160000 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (0 : ℕ)) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (23 / 32 : ℝ) * (t ^ (7 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (23 / 4 : ℝ) * (t ^ (9 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (23 / 200000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (9 / 16 : ℝ) * (t ^ (9 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (9 / 2 : ℝ) * (t ^ (11 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (9 / 40000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (1 / 8 : ℝ) * (t ^ (11 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (1 : ℝ) * (t ^ (13 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (7367899639810274475540267 / 1600000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18432 : ℝ) * (t ^ (11 : ℕ) * l) + (18432 : ℝ) * (t ^ (11 : ℕ)) + (204798755497348535331383 / 6400000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) + (128 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (128 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (96 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) ^ (2 : ℕ)) + (512 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (512 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (2048 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ)) + (512 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have m0 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sq_nonneg (4 * t ^ (2 : ℕ) - l)))
  have m1 : 0 ≤ t * l ^ (0 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 0))
  have m2 : 0 ≤ t * l := (mul_nonneg ht0 hl0)
  have m3 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m4 : 0 ≤ t * l ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 3)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 1)))
  have m5 : 0 ≤ l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg hl0 3) hu)
  have m6 : 0 ≤ l ^ (4 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ)) := (mul_nonneg (pow_nonneg hl0 4) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 9)))
  have m7 : 0 ≤ t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m8 : 0 ≤ t ^ (3 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 0))
  have m9 : 0 ≤ t * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg ht0 hl0) hu)
  have m10 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m11 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2))
  have m12 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3))
  have m13 : 0 ≤ t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m14 : 0 ≤ t ^ (5 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 0))
  have m15 : 0 ≤ t ^ (3 : ℕ) * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) hl0) hu)
  have m16 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m17 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m18 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3))
  have m19 : 0 ≤ t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m20 : 0 ≤ t ^ (7 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 0))
  have m21 : 0 ≤ t ^ (7 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 7) hl0)
  have m22 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2))
  have m23 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3))
  have m24 : 0 ≤ t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m25 : 0 ≤ t ^ (9 : ℕ) * l ^ (0 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 0))
  have m26 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m27 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m28 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3))
  have m29 : 0 ≤ t ^ (7 : ℕ) * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) hl0) hu)
  have m30 : 0 ≤ t ^ (9 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) hu)
  have m31 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m32 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m33 : 0 ≤ t ^ (9 : ℕ) * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) hu)
  have m34 : 0 ≤ t ^ (11 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) hu)
  have m35 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m36 : 0 ≤ t ^ (13 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 13) hl0)
  have m37 : 0 ≤ t ^ (11 : ℕ) * l * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) hl0) hu)
  have m38 : 0 ≤ t ^ (13 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) hu)
  have m39 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2))
  have m40 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m41 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m42 : 0 ≤ t ^ (9 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 4))
  have m43 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3))
  have m44 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m45 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) (pow_nonneg hu 2))
  have m46 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2)) hu)
  have m47 : 0 ≤ t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hs2 2)) hu)
  have m48 : 0 ≤ t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hs2 2))
  have m49 : 0 ≤ t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hs2 2))
  have h0 : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (74655 / 2048 : ℝ) * (t * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (95169 / 4096 : ℝ) * (t * l) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (238617 / 409600 : ℝ) * (t * l ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (238617 / 3276800 : ℝ) * (l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (238617 / 6400000000000000000000 : ℝ) * (l ^ (4 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ))) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (226443 / 640000000000000000 : ℝ) * (t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (58863 / 256 : ℝ) * (t ^ (3 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (728753 / 16384 : ℝ) * (t * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (728753 / 1600000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (11623 / 16000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (19053 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (402363 / 4096 : ℝ) * (t ^ (3 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (402363 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (2249 / 3200000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (36367 / 32 : ℝ) * (t ^ (7 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (31 / 160000 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (3151 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (0 : ℕ)) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (23 / 32 : ℝ) * (t ^ (7 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (23 / 4 : ℝ) * (t ^ (9 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (23 / 200000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (9 / 16 : ℝ) * (t ^ (9 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (9 / 2 : ℝ) * (t ^ (11 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (9 / 40000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (1 / 8 : ℝ) * (t ^ (11 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (1 : ℝ) * (t ^ (13 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (7367899639810274475540267 / 1600000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (18432 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m40
  have h41 : 0 ≤ (18432 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m41
  have h42 : 0 ≤ (204798755497348535331383 / 6400000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m42
  have h43 : 0 ≤ (128 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m43
  have h44 : 0 ≤ (128 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m44
  have h45 : 0 ≤ (96 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m45
  have h46 : 0 ≤ (512 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m46
  have h47 : 0 ≤ (512 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m47
  have h48 : 0 ≤ (2048 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m48
  have h49 : 0 ≤ (512 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m49
  have hP : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (4 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (74655 / 2048 : ℝ) * (t * l ^ (0 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (5049 / 80000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (238617 / 409600 : ℝ) * (t * l ^ (3 : ℕ) * (t ^ (1 : ℕ) - 50 ^ (1 : ℕ))) + (238617 / 3276800 : ℝ) * (l ^ (3 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (238617 / 6400000000000000000000 : ℝ) * (l ^ (4 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ))) + (226443 / 640000000000000000 : ℝ) * (t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ) * l ^ (0 : ℕ)) + (728753 / 16384 : ℝ) * (t * l * (l - 8 * t ^ (2 : ℕ))) + (728753 / 1600000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (11623 / 16000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (0 : ℕ)) + (402363 / 4096 : ℝ) * (t ^ (3 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (402363 / 160000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (11443 / 3200000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (2249 / 3200000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ) * l ^ (0 : ℕ)) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (31 / 160000 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ) * l ^ (0 : ℕ)) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (23 / 32 : ℝ) * (t ^ (7 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (23 / 4 : ℝ) * (t ^ (9 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (23 / 200000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (9 / 16 : ℝ) * (t ^ (9 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (9 / 2 : ℝ) * (t ^ (11 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (9 / 40000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (1 / 8 : ℝ) * (t ^ (11 : ℕ) * l * (l - 8 * t ^ (2 : ℕ))) + (1 : ℝ) * (t ^ (13 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (7367899639810274475540267 / 1600000000000000000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ)) + (18432 : ℝ) * (t ^ (11 : ℕ) * l) + (18432 : ℝ) * (t ^ (11 : ℕ)) + (204798755497348535331383 / 6400000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) + (128 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (128 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (96 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ)) ^ (2 : ℕ)) + (512 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (512 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ) * (l - 8 * t ^ (2 : ℕ))) + (2048 : ℝ) * (t ^ (11 : ℕ) * (l + 2) ^ (2 : ℕ)) + (512 : ℝ) * (t ^ (9 : ℕ) * (l + 2) ^ (2 : ℕ)) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48) h49)
  rw [key]
  exact hP

/-- `t⁹·D + Form ≥ 0` for every harmonic `l ≥ t`, `t ≥ 50`. -/
theorem skewPlateauLineForm_bound_plus (t l : ℝ) (ht : (50 : ℝ) ≤ t) (hl : t ≤ l) :
    0 ≤ t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) + skewPlateauLineForm t l := by
  rcases le_or_gt l (2 * t ^ 2) with h | h
  · exact skewPlateauLineForm_bound_A_plus t l ht hl h
  · rcases le_or_gt l (8 * t ^ 2) with h' | h'
    · exact skewPlateauLineForm_bound_B1_plus t l ht h.le h'
    · exact skewPlateauLineForm_bound_B2_plus t l ht h'.le

/-- `t⁹·D − Form ≥ 0` for every harmonic `l ≥ t`, `t ≥ 50`. -/
theorem skewPlateauLineForm_bound_minus (t l : ℝ) (ht : (50 : ℝ) ≤ t) (hl : t ≤ l) :
    0 ≤ t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) - skewPlateauLineForm t l := by
  rcases le_or_gt l (2 * t ^ 2) with h | h
  · exact skewPlateauLineForm_bound_A_minus t l ht hl h
  · rcases le_or_gt l (8 * t ^ 2) with h' | h'
    · exact skewPlateauLineForm_bound_B1_minus t l ht h.le h'
    · exact skewPlateauLineForm_bound_B2_minus t l ht h'.le

/-- **Uniform kernel bound above the low band.**  On the critical line, at every harmonic `l ≥ t`
with `t ≥ 50`, the plateau kernel has `|Im K| ≤ t⁹`. -/
theorem skewPlateauMu_line_abs_im_le (t l : ℝ) (ht : (50 : ℝ) ≤ t) (hl : t ≤ l) :
    |(skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im| ≤ t ^ 9 := by
  have hl0 : (0 : ℝ) ≤ l := by linarith
  have h := congrArg Complex.im (skewPlateauMu_line t l hl0)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_add, one_mul] at h
  have hden := skewPlateauLineDen_pos t l hl0
  have hP := skewPlateauLineForm_bound_plus t l ht hl
  have hM := skewPlateauLineForm_bound_minus t l ht hl
  rw [abs_le]
  constructor
  · have hmul : (-t ^ 9) * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) ≤ (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) := by
      rw [h]; linarith
    exact le_of_mul_le_mul_right hmul hden
  · have hmul : (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) ≤ t ^ 9 * (128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2)) := by
      rw [h]; linarith
    exact le_of_mul_le_mul_right hmul hden

end

end RHTower.D4BMScalarStream
