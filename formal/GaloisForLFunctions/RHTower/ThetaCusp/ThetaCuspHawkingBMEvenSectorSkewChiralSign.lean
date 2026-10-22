import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorSkewSectorForm

/-!
# The chiral excitation: one sign at every harmonic

The Xi excitation of the route is chiral: rows 2–5 work with a single gravitational helicity,
`scalar ± i·vector` (`d4GravitationalHelicityPlus/Minus`), the vector mode being the Hodge partner of
the scalar mode with the same radial function. For such an excitation the sector amplitudes satisfy
`aV = ± i·aS`, and since the two branches of the two-rate pairing carry `aS₊²aS₋²`, `aS₊²aV₋²`,
`aV₊²aS₋²`, `aV₊²aV₋²` in front of the four scalar-sector kernels, the quartic form collapses to
`aS₊²aS₋²·(P_SS − P_X + P_VV)`: the chiral kernel `skewPlateauMuChiral`.

On the critical line at the real harmonic `μ = −l` its line form has the exact leading part
`(1/64)·t⁵·l²·(l − 4t²)²·(51t⁴ + 56t²l − 16l²)` (`skewPlateauMuChiralLine_leading`), positive for
every harmonic below `l = (17/4)t²`, i.e. on the whole spectral support of the square of the
angular profile, with the constant mode positive as well (weight-fifteen coefficient `1352·t¹⁵`).
Certified: `skewPlateauMuChiralLine_pos` and `skewPlateauMuChiral_line_im_pos` — for `t ≥ 50` the
chiral kernel has positive imaginary part at every harmonic `0 ≤ l ≤ 2t²`, by an exact identity
`chiral line form = (polynomial with nonnegative coefficients in t, l, 2t²−l, t^e−50^e, (2t²)^m−l^m)`
with two strictly positive budget terms `(51/16 − …)·t¹³l²` and `(1352 − …)·t¹⁵`. The sign is
therefore uniform across the low band, the bulk and (paper, from the leading part) up to the edge:
for a chiral excitation the on-line sign of the scalar-sector clock coefficient is the same at every
harmonic, so it holds for every positive spectral measure of the square of the angular profile.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

/-- The chiral kernel `P_SS − P_X + P_VV`. -/
noncomputable def skewPlateauMuChiral (s μ : ℂ) : ℂ :=
  skewPlateauMu s μ - skewPlateauMuCross s μ + skewPlateauMuVV s μ

/-- Its line form. -/
noncomputable def skewPlateauMuChiralLine (t l : ℝ) : ℝ :=
  skewPlateauLineForm t l - skewPlateauMuCrossLine t l + skewPlateauMuVVLine t l

noncomputable def skewPlateauMuChiralLineLower (t l : ℝ) : ℝ := (-23263191 / 2048 : ℝ) * t + (-46446921 / 4096 : ℝ) * t * l + (-11719707 / 4096 : ℝ) * t * l ^ (2 : ℕ) + (2002689 / 8192 : ℝ) * t * l ^ (3 : ℕ) + (1504899 / 16384 : ℝ) * t * l ^ (4 : ℕ) + (-7791 / 512 : ℝ) * t * l ^ (5 : ℕ) + (-81 / 64 : ℝ) * t * l ^ (6 : ℕ) + (-18458023 / 256 : ℝ) * t ^ (3 : ℕ) + (-70833639 / 2048 : ℝ) * t ^ (3 : ℕ) * l + (-18409589 / 4096 : ℝ) * t ^ (3 : ℕ) * l ^ (2 : ℕ) + (82657 / 2048 : ℝ) * t ^ (3 : ℕ) * l ^ (3 : ℕ) + (135679 / 1024 : ℝ) * t ^ (3 : ℕ) * l ^ (4 : ℕ) + (-231 / 128 : ℝ) * t ^ (3 : ℕ) * l ^ (5 : ℕ) + (-9 / 8 : ℝ) * t ^ (3 : ℕ) * l ^ (6 : ℕ) + (-4034501 / 32 : ℝ) * t ^ (5 : ℕ) + (-21512269 / 512 : ℝ) * t ^ (5 : ℕ) * l + (715991 / 1024 : ℝ) * t ^ (5 : ℕ) * l ^ (2 : ℕ) + (94637 / 256 : ℝ) * t ^ (5 : ℕ) * l ^ (3 : ℕ) + (26353 / 512 : ℝ) * t ^ (5 : ℕ) * l ^ (4 : ℕ) + (287 / 32 : ℝ) * t ^ (5 : ℕ) * l ^ (5 : ℕ) + (-2482407 / 32 : ℝ) * t ^ (7 : ℕ) + (-2083147 / 64 : ℝ) * t ^ (7 : ℕ) * l + (-33633 / 128 : ℝ) * t ^ (7 : ℕ) * l ^ (2 : ℕ) + (19753 / 64 : ℝ) * t ^ (7 : ℕ) * l ^ (3 : ℕ) + (-1417 / 64 : ℝ) * t ^ (7 : ℕ) * l ^ (4 : ℕ) + (51449 / 8 : ℝ) * t ^ (9 : ℕ) + (-105371 / 8 : ℝ) * t ^ (9 : ℕ) * l + (-45511 / 32 : ℝ) * t ^ (9 : ℕ) * l ^ (2 : ℕ) + (2837 / 32 : ℝ) * t ^ (9 : ℕ) * l ^ (3 : ℕ) + (26942 : ℝ) * t ^ (11 : ℕ) + (-14387 / 8 : ℝ) * t ^ (11 : ℕ) * l + (-6073 / 16 : ℝ) * t ^ (11 : ℕ) * l ^ (2 : ℕ) + (10692 : ℝ) * t ^ (13 : ℕ) + (155 / 2 : ℝ) * t ^ (13 : ℕ) * l + (1352 : ℝ) * t ^ (15 : ℕ)

theorem skewPlateauMuChiralLine_leading (t l : ℝ) :
    skewPlateauMuChiralLine t l =
      (1 / 64) * t ^ (5 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) * (51 * t ^ (4 : ℕ) + 56 * t ^ (2 : ℕ) * l - 16 * l ^ (2 : ℕ)) + skewPlateauMuChiralLineLower t l := by
  unfold skewPlateauMuChiralLine skewPlateauLineForm skewPlateauMuCrossLine skewPlateauMuVVLine skewPlateauMuChiralLineLower
  ring

/-- The chiral line form is positive on `0 ≤ l ≤ 2t²` for `t ≥ 50`. -/
theorem skewPlateauMuChiralLine_pos (t l : ℝ) (ht : (50 : ℝ) ≤ t) (hl0 : 0 ≤ l) (h2 : l ≤ 2 * t ^ (2 : ℕ)) :
    0 < skewPlateauMuChiralLine t l := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hg3 : (0 : ℝ) ≤ t - 50 := by linarith
  have hg8 : (0 : ℝ) ≤ 2 * t ^ (2 : ℕ) - l := by linarith
  have hpos_t : (0 : ℝ) < t := by linarith
  have key : skewPlateauMuChiralLine t l = (3 / 2 : ℝ) * (t ^ (11 : ℕ) * l ^ (3 : ℕ)) + (1 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (51 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (3 / 2 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (1 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (51 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (3 / 8 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (1 / 4 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (3 : ℕ)) + (23263191 / 1250000000000000000000000000 : ℝ) * (t * (t ^ (14 : ℕ) - 50 ^ (14 : ℕ))) + (18458023 / 62500000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (4034501 / 3125000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (2482407 / 1250000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (51449 / 8 : ℝ) * (t ^ (9 : ℕ)) + (26942 : ℝ) * (t ^ (11 : ℕ)) + (10692 : ℝ) * (t ^ (13 : ℕ)) + (46446921 / 4096 : ℝ) * (t * (2 * t ^ (2 : ℕ) - l)) + (46446921 / 500000000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (70833639 / 2048 : ℝ) * (t ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (70833639 / 100000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (21512269 / 512 : ℝ) * (t ^ (5 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (21512269 / 10000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (2083147 / 64 : ℝ) * (t ^ (7 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (2083147 / 500000000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (105371 / 8 : ℝ) * (t ^ (9 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (105371 / 25000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (14387 / 8 : ℝ) * (t ^ (11 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (14387 / 10000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (155 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (11719707 / 1000000000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (18409589 / 400000000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (715991 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (33633 / 2000000000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (45511 / 200000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (6073 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (2002689 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (82657 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (94637 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (19753 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (2837 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (1504899 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (135679 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (26353 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (1417 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (1417 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (7791 / 512 : ℝ) * (t * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ))) + (7791 / 1000000000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (231 / 128 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ))) + (231 / 100000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (287 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (5 : ℕ)) + (81 / 64 : ℝ) * (t * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) + (81 / 25000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (9 / 8 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) + (9 / 1250 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (2992816870392453964307793 / 1000000000000000000000000 : ℝ) * (t ^ (13 : ℕ) * l ^ (2 : ℕ)) + (1688196351236958559668811474309 / 1250000000000000000000000000 : ℝ) * (t ^ (15 : ℕ)) := by
    unfold skewPlateauMuChiralLine skewPlateauLineForm skewPlateauMuCrossLine skewPlateauMuVVLine
    ring
  have mpos : 0 < t ^ (15 : ℕ) := pow_pos hpos_t 15
  have m0 : 0 ≤ t ^ (11 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 3))
  have m1 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3)) hg8)
  have m2 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) hg8)
  have m3 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3)) hg8)
  have m4 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3)) (pow_nonneg hg8 2))
  have m5 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (pow_nonneg hg8 2))
  have m6 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3)) (pow_nonneg hg8 2))
  have m7 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (3 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3)) (pow_nonneg hg8 3))
  have m8 : 0 ≤ t * (t ^ (14 : ℕ) - 50 ^ (14 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 14)))
  have m9 : 0 ≤ t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 12)))
  have m10 : 0 ≤ t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m11 : 0 ≤ t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m12 : 0 ≤ t ^ (9 : ℕ) := (pow_nonneg ht0 9)
  have m13 : 0 ≤ t ^ (11 : ℕ) := (pow_nonneg ht0 11)
  have m14 : 0 ≤ t ^ (13 : ℕ) := (pow_nonneg ht0 13)
  have m15 : 0 ≤ t * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg ht0 hg8)
  have m16 : 0 ≤ t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 12)))
  have m17 : 0 ≤ t ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (pow_nonneg ht0 3) hg8)
  have m18 : 0 ≤ t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m19 : 0 ≤ t ^ (5 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (pow_nonneg ht0 5) hg8)
  have m20 : 0 ≤ t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m21 : 0 ≤ t ^ (7 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (pow_nonneg ht0 7) hg8)
  have m22 : 0 ≤ t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m23 : 0 ≤ t ^ (9 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (pow_nonneg ht0 9) hg8)
  have m24 : 0 ≤ t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m25 : 0 ≤ t ^ (11 : ℕ) * (2 * t ^ (2 : ℕ) - l) := (mul_nonneg (pow_nonneg ht0 11) hg8)
  have m26 : 0 ≤ t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m27 : 0 ≤ t ^ (13 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 13) hl0)
  have m28 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 12)))
  have m29 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m30 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2))
  have m31 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m32 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m33 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m34 : 0 ≤ t * l ^ (3 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 3))
  have m35 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3))
  have m36 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3))
  have m37 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3))
  have m38 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3))
  have m39 : 0 ≤ t * l ^ (4 : ℕ) := (mul_nonneg ht0 (pow_nonneg hl0 4))
  have m40 : 0 ≤ t ^ (3 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 4))
  have m41 : 0 ≤ t ^ (5 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 4))
  have m42 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m43 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m44 : 0 ≤ t * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 3)))
  have m45 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m46 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 3)))
  have m47 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m48 : 0 ≤ t ^ (5 : ℕ) * l ^ (5 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 5))
  have m49 : 0 ≤ t * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 4)))
  have m50 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m51 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 4)))
  have m52 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m53 : 0 ≤ t ^ (13 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 13) (pow_nonneg hl0 2))
  have m54 : 0 ≤ t ^ (15 : ℕ) := (pow_nonneg ht0 15)
  have h0 : 0 ≤ (3 / 2 : ℝ) * (t ^ (11 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (1 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (51 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (3 / 2 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (1 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (51 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (3 / 8 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (1 / 4 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (3 : ℕ)) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (23263191 / 1250000000000000000000000000 : ℝ) * (t * (t ^ (14 : ℕ) - 50 ^ (14 : ℕ))) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (18458023 / 62500000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (4034501 / 3125000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (2482407 / 1250000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (51449 / 8 : ℝ) * (t ^ (9 : ℕ)) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (26942 : ℝ) * (t ^ (11 : ℕ)) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (10692 : ℝ) * (t ^ (13 : ℕ)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (46446921 / 4096 : ℝ) * (t * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (46446921 / 500000000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (70833639 / 2048 : ℝ) * (t ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (70833639 / 100000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (21512269 / 512 : ℝ) * (t ^ (5 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (21512269 / 10000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (2083147 / 64 : ℝ) * (t ^ (7 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (2083147 / 500000000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (105371 / 8 : ℝ) * (t ^ (9 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (105371 / 25000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (14387 / 8 : ℝ) * (t ^ (11 : ℕ) * (2 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (14387 / 10000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (155 / 2 : ℝ) * (t ^ (13 : ℕ) * l) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (11719707 / 1000000000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (18409589 / 400000000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (715991 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (33633 / 2000000000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (45511 / 200000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (6073 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (2002689 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (82657 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (94637 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (19753 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (2837 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (1504899 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (135679 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m40
  have h41 : 0 ≤ (26353 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) := mul_nonneg (by norm_num) m41
  have h42 : 0 ≤ (1417 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m42
  have h43 : 0 ≤ (1417 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m43
  have h44 : 0 ≤ (7791 / 512 : ℝ) * (t * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ))) := mul_nonneg (by norm_num) m44
  have h45 : 0 ≤ (7791 / 1000000000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m45
  have h46 : 0 ≤ (231 / 128 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ))) := mul_nonneg (by norm_num) m46
  have h47 : 0 ≤ (231 / 100000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m47
  have h48 : 0 ≤ (287 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (5 : ℕ)) := mul_nonneg (by norm_num) m48
  have h49 : 0 ≤ (81 / 64 : ℝ) * (t * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) := mul_nonneg (by norm_num) m49
  have h50 : 0 ≤ (81 / 25000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m50
  have h51 : 0 ≤ (9 / 8 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) := mul_nonneg (by norm_num) m51
  have h52 : 0 ≤ (9 / 1250 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m52
  have h53 : 0 ≤ (2992816870392453964307793 / 1000000000000000000000000 : ℝ) * (t ^ (13 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m53
  have hlast : 0 < (1688196351236958559668811474309 / 1250000000000000000000000000 : ℝ) * (t ^ (15 : ℕ)) := mul_pos (by norm_num) mpos
  have hP : 0 < (3 / 2 : ℝ) * (t ^ (11 : ℕ) * l ^ (3 : ℕ)) + (1 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (51 / 16 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (3 / 2 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (1 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (51 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (3 / 8 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (1 / 4 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l) ^ (3 : ℕ)) + (23263191 / 1250000000000000000000000000 : ℝ) * (t * (t ^ (14 : ℕ) - 50 ^ (14 : ℕ))) + (18458023 / 62500000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (4034501 / 3125000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (2482407 / 1250000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (51449 / 8 : ℝ) * (t ^ (9 : ℕ)) + (26942 : ℝ) * (t ^ (11 : ℕ)) + (10692 : ℝ) * (t ^ (13 : ℕ)) + (46446921 / 4096 : ℝ) * (t * (2 * t ^ (2 : ℕ) - l)) + (46446921 / 500000000000000000000000 : ℝ) * (t ^ (3 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (70833639 / 2048 : ℝ) * (t ^ (3 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (70833639 / 100000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (21512269 / 512 : ℝ) * (t ^ (5 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (21512269 / 10000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (2083147 / 64 : ℝ) * (t ^ (7 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (2083147 / 500000000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (105371 / 8 : ℝ) * (t ^ (9 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (105371 / 25000000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (14387 / 8 : ℝ) * (t ^ (11 : ℕ) * (2 * t ^ (2 : ℕ) - l)) + (14387 / 10000 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (155 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (11719707 / 1000000000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (18409589 / 400000000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (715991 / 1024 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ)) + (33633 / 2000000000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (45511 / 200000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (6073 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (2002689 / 8192 : ℝ) * (t * l ^ (3 : ℕ)) + (82657 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (94637 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (19753 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (2837 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (1504899 / 16384 : ℝ) * (t * l ^ (4 : ℕ)) + (135679 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ)) + (26353 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ)) + (1417 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (1417 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (7791 / 512 : ℝ) * (t * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ))) + (7791 / 1000000000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (231 / 128 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ))) + (231 / 100000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (287 / 32 : ℝ) * (t ^ (5 : ℕ) * l ^ (5 : ℕ)) + (81 / 64 : ℝ) * (t * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) + (81 / 25000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (9 / 8 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((2 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) + (9 / 1250 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (2992816870392453964307793 / 1000000000000000000000000 : ℝ) * (t ^ (13 : ℕ) * l ^ (2 : ℕ)) + (1688196351236958559668811474309 / 1250000000000000000000000000 : ℝ) * (t ^ (15 : ℕ)) := add_pos_of_nonneg_of_pos (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48) h49) h50) h51) h52) h53) hlast
  rw [key]
  exact hP

/-- The chiral kernel on the line is purely imaginary. -/
theorem skewPlateauMuChiral_line (t l : ℝ) (hl : 0 ≤ l) :
    skewPlateauMuChiral ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ)) * ((128 * (2 + l) ^ (2 : ℕ) * ((4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ)) : ℝ) : ℂ) =
      Complex.I * (skewPlateauMuChiralLine t l : ℂ) := by
  have hden : ((128 * (2 + l) ^ (2 : ℕ) * ((4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (skewPlateauLineDen_pos t l hl).ne'
  have hS := skewPlateauMu_line t l hl
  have hV := skewPlateauMuVV_line t l hl
  have hX : skewPlateauMuCross ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ)) * ((128 * (2 + l) ^ (2 : ℕ) * ((4 * t ^ (2 : ℕ) - 2 - l) ^ (2 : ℕ) + 36 * t ^ (2 : ℕ)) : ℝ) : ℂ) =
      Complex.I * (skewPlateauMuCrossLine t l : ℂ) := by
    unfold skewPlateauMuCross
    rw [← skewPlateauMu_line_denominator t l, div_mul_cancel₀ _ (by rw [skewPlateauMu_line_denominator t l]; exact hden)]
    exact skewPlateauMuCrossNumerator_line t l
  unfold skewPlateauMuChiral skewPlateauMuChiralLine
  push_cast at hS hX hV ⊢
  linear_combination hS - hX + hV

/-- For `t ≥ 50` the chiral kernel has positive imaginary part at every harmonic `0 ≤ l ≤ 2t²`. -/
theorem skewPlateauMuChiral_line_im_pos (t l : ℝ) (ht : (50 : ℝ) ≤ t) (hl0 : 0 ≤ l) (h2 : l ≤ 2 * t ^ (2 : ℕ)) :
    0 < (skewPlateauMuChiral ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im := by
  have h := congrArg Complex.im (skewPlateauMuChiral_line t l hl0)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
  have hden := skewPlateauLineDen_pos t l hl0
  have hF := skewPlateauMuChiralLine_pos t l ht hl0 h2
  nlinarith

end RHTower.D4BMScalarStream
