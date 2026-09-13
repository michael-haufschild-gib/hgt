import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewHorizonPlateau

/-!
# The horizon plateau of the two-rate current at every angular harmonic

`skewPlateauMu s μ` is the horizon value of the dressed ingoing time component
`e^{6r_*} z^{−3} r² (Ω^t + Ω^r/(r²−1))` of the two-rate current built from the Laurent particulars
`r + A(μ)/r + B(μ)/r³` at rates `s` and `−3−s` and at a general angular harmonic `μ` (the harmonic
enters through the Laurent coefficients `laurentMasterA/B` and through the angular Laplacian in the
current; the horizon poles cancel at every `μ`, and the plateau is the derivative of the pole-free
combination at the horizon). It is an explicit rational function with denominator
`128·(2−μ)²·(μ−(2s+1)(2s+2))·(μ−(2s+4)(2s+5))` and numerator `skewPlateauMuNumerator` of degree
fifteen in `s` and four in `μ`; at the fundamental harmonic `μ = (s+1)(s+2)` it is the certified
`skewHorizonPlateau` (`skewPlateauMu_fundamental`).

On the critical line `s = −3/2 + i t` with a real harmonic `μ = −l` (`l` the Laplace eigenvalue) the
plateau is purely imaginary: its numerator is `i·skewPlateauLineForm t l`
(`skewPlateauMuNumerator_line`) and its denominator is the positive real
`128·(2+l)²·((4t²−2−l)² + 36t²)` (`skewPlateauMu_line_denominator`). The line form has leading part
`−(5/64)·t⁹·l²·(l − 4t²)²` (`skewPlateauLineForm_leading`), negative semidefinite with double zeros at
the constant mode `l = 0` and at the doubled-frequency edge `l = 4t²`; the lower-weight terms are
dominated on the three regions `40t ≤ l ≤ 3t²`, `3t² ≤ l ≤ 5t²`, `l ≥ 5t²` by explicit identities
`−skewPlateauLineForm t l = (polynomial with nonnegative coefficients in t, l and the region slacks)`
(`skewPlateauLineForm_neg_low/_edge/_high`), so for `t ≥ 50` the plateau has negative imaginary part
at every harmonic `l ≥ 40 t` (`skewPlateauMu_line_im_neg`): the on-line sign of the scalar-sector
plateau is pointwise in the harmonic outside the low band `l < 40t`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

/-- Numerator of the general-harmonic horizon plateau. -/
noncomputable def skewPlateauMuNumerator (s μ : ℂ) : ℂ := (-360 : ℂ) * μ + (378 : ℂ) * μ ^ 2 + (-108 : ℂ) * μ ^ 3 + (9 / 2 : ℂ) * μ ^ 4 + (-17280 : ℂ) * s + (15924 : ℂ) * s * μ + (-3969 : ℂ) * s * μ ^ 2 + (180 : ℂ) * s * μ ^ 3 + (-33 / 4 : ℂ) * s * μ ^ 4 + (-97956 : ℂ) * s ^ 2 + (87363 : ℂ) * s ^ 2 * μ + (-22095 : ℂ) * s ^ 2 * μ ^ 2 + (3015 / 2 : ℂ) * s ^ 2 * μ ^ 3 + (-225 / 8 : ℂ) * s ^ 2 * μ ^ 4 + (-261744 : ℂ) * s ^ 3 + (421985 / 2 : ℂ) * s ^ 3 * μ + (-408679 / 8 : ℂ) * s ^ 3 * μ ^ 2 + (7105 / 2 : ℂ) * s ^ 3 * μ ^ 3 + (-2339 / 32 : ℂ) * s ^ 3 * μ ^ 4 + (-922941 / 2 : ℂ) * s ^ 4 + (1277613 / 4 : ℂ) * s ^ 4 * μ + (-2333337 / 32 : ℂ) * s ^ 4 * μ ^ 2 + (78471 / 16 : ℂ) * s ^ 4 * μ ^ 3 + (-12675 / 128 : ℂ) * s ^ 4 * μ ^ 4 + (-2552481 / 4 : ℂ) * s ^ 5 + (5659371 / 16 : ℂ) * s ^ 5 * μ + (-2339771 / 32 : ℂ) * s ^ 5 * μ ^ 2 + (71715 / 16 : ℂ) * s ^ 5 * μ ^ 3 + (-4373 / 64 : ℂ) * s ^ 5 * μ ^ 4 + (-2979537 / 4 : ℂ) * s ^ 6 + (4930203 / 16 : ℂ) * s ^ 6 * μ + (-1753455 / 32 : ℂ) * s ^ 6 * μ ^ 2 + (45171 / 16 : ℂ) * s ^ 6 * μ ^ 3 + (-1743 / 64 : ℂ) * s ^ 6 * μ ^ 4 + (-723325 : ℂ) * s ^ 7 + (854075 / 4 : ℂ) * s ^ 7 * μ + (-253427 / 8 : ℂ) * s ^ 7 * μ ^ 2 + (4977 / 4 : ℂ) * s ^ 7 * μ ^ 3 + (-109 / 16 : ℂ) * s ^ 7 * μ ^ 4 + (-558684 : ℂ) * s ^ 8 + (917487 / 8 : ℂ) * s ^ 8 * μ + (-456003 / 32 : ℂ) * s ^ 8 * μ ^ 2 + (6129 / 16 : ℂ) * s ^ 8 * μ ^ 3 + (-135 / 128 : ℂ) * s ^ 8 * μ ^ 4 + (-1327433 / 4 : ℂ) * s ^ 9 + (734643 / 16 : ℂ) * s ^ 9 * μ + (-157363 / 32 : ℂ) * s ^ 9 * μ ^ 2 + (1279 / 16 : ℂ) * s ^ 9 * μ ^ 3 + (-5 / 64 : ℂ) * s ^ 9 * μ ^ 4 + (-593769 / 4 : ℂ) * s ^ 10 + (209319 / 16 : ℂ) * s ^ 10 * μ + (-40161 / 32 : ℂ) * s ^ 10 * μ ^ 2 + (165 / 16 : ℂ) * s ^ 10 * μ ^ 3 + (-98021 / 2 : ℂ) * s ^ 11 + (19915 / 8 : ℂ) * s ^ 11 * μ + (-3557 / 16 : ℂ) * s ^ 11 * μ ^ 2 + (5 / 8 : ℂ) * s ^ 11 * μ ^ 3 + (-11583 : ℂ) * s ^ 12 + (1131 / 4 : ℂ) * s ^ 12 * μ + (-195 / 8 : ℂ) * s ^ 12 * μ ^ 2 + (-1854 : ℂ) * s ^ 13 + (29 / 2 : ℂ) * s ^ 13 * μ + (-5 / 4 : ℂ) * s ^ 13 * μ ^ 2 + (-180 : ℂ) * s ^ 14 + (-8 : ℂ) * s ^ 15

/-- The general-harmonic horizon plateau of the two-rate current. -/
noncomputable def skewPlateauMu (s μ : ℂ) : ℂ :=
  skewPlateauMuNumerator s μ / (128 * (2 - μ) ^ 2 * (μ - (2 * s + 1) * (2 * s + 2)) * (μ - (2 * s + 4) * (2 * s + 5)))

/-- At the fundamental harmonic the general plateau is the certified horizon plateau. -/
theorem skewPlateauMu_fundamental (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0) :
    skewPlateauMu s ((s + 1) * (s + 2)) = skewHorizonPlateau s := by
  rw [skewHorizonPlateau_eq s hs hs3]
  unfold skewPlateauMu skewPlateauMuNumerator
  have h1 : (2 : ℂ) - (s + 1) * (s + 2) = -(s * (s + 3)) := by ring
  have h2 : (s + 1) * (s + 2) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) := by ring
  have h3 : (s + 1) * (s + 2) - (2 * s + 4) * (2 * s + 5) = -(3 * ((s + 2) * (s + 3))) := by ring
  rw [h1, h2, h3]
  field_simp
  ring

/-- Imaginary part of the plateau numerator on the critical line at the real harmonic `μ = −l`. -/
noncomputable def skewPlateauLineForm (t l : ℝ) : ℝ := (-74655 / 2048 : ℝ) * t + (-95169 / 4096 : ℝ) * t * l + (25245 / 4096 : ℝ) * t * l ^ 2 + (238617 / 8192 : ℝ) * t * l ^ 3 + (226443 / 16384 : ℝ) * t * l ^ 4 + (-58863 / 256 : ℝ) * t ^ 3 + (728753 / 2048 : ℝ) * t ^ 3 * l + (-896173 / 4096 : ℝ) * t ^ 3 * l ^ 2 + (-76823 / 2048 : ℝ) * t ^ 3 * l ^ 3 + (11623 / 1024 : ℝ) * t ^ 3 * l ^ 4 + (-19053 / 32 : ℝ) * t ^ 5 + (402363 / 512 : ℝ) * t ^ 5 * l + (57215 / 1024 : ℝ) * t ^ 5 * l ^ 2 + (-2667 / 256 : ℝ) * t ^ 5 * l ^ 3 + (2249 / 512 : ℝ) * t ^ 5 * l ^ 4 + (-36367 / 32 : ℝ) * t ^ 7 + (-16915 / 64 : ℝ) * t ^ 7 * l + (-6265 / 128 : ℝ) * t ^ 7 * l ^ 2 + (-639 / 64 : ℝ) * t ^ 7 * l ^ 3 + (31 / 64 : ℝ) * t ^ 7 * l ^ 4 + (-3151 / 8 : ℝ) * t ^ 9 + (-2259 / 8 : ℝ) * t ^ 9 * l + (-943 / 32 : ℝ) * t ^ 9 * l ^ 2 + (-83 / 32 : ℝ) * t ^ 9 * l ^ 3 + (-5 / 64 : ℝ) * t ^ 9 * l ^ 4 + (46 : ℝ) * t ^ 11 + (-443 / 8 : ℝ) * t ^ 11 * l + (47 / 16 : ℝ) * t ^ 11 * l ^ 2 + (5 / 8 : ℝ) * t ^ 11 * l ^ 3 + (36 : ℝ) * t ^ 13 + (-29 / 2 : ℝ) * t ^ 13 * l + (-5 / 4 : ℝ) * t ^ 13 * l ^ 2 + (8 : ℝ) * t ^ 15

theorem skewPlateauMuNumerator_line (t l : ℝ) :
    skewPlateauMuNumerator ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ)) = Complex.I * (skewPlateauLineForm t l : ℂ) := by
  unfold skewPlateauMuNumerator skewPlateauLineForm
  push_cast
  linear_combination ((58863 / 256 : ℂ) * (t : ℂ) ^ 3 * Complex.I + (-728753 / 2048 : ℂ) * (t : ℂ) ^ 3 * (l : ℂ) * Complex.I + (896173 / 4096 : ℂ) * (t : ℂ) ^ 3 * (l : ℂ) ^ 2 * Complex.I + (76823 / 2048 : ℂ) * (t : ℂ) ^ 3 * (l : ℂ) ^ 3 * Complex.I + (-11623 / 1024 : ℂ) * (t : ℂ) ^ 3 * (l : ℂ) ^ 4 * Complex.I + (19053 / 32 : ℂ) * (t : ℂ) ^ 5 * Complex.I + (-19053 / 32 : ℂ) * (t : ℂ) ^ 5 * Complex.I ^ 3 + (-402363 / 512 : ℂ) * (t : ℂ) ^ 5 * (l : ℂ) * Complex.I + (402363 / 512 : ℂ) * (t : ℂ) ^ 5 * (l : ℂ) * Complex.I ^ 3 + (-57215 / 1024 : ℂ) * (t : ℂ) ^ 5 * (l : ℂ) ^ 2 * Complex.I + (57215 / 1024 : ℂ) * (t : ℂ) ^ 5 * (l : ℂ) ^ 2 * Complex.I ^ 3 + (2667 / 256 : ℂ) * (t : ℂ) ^ 5 * (l : ℂ) ^ 3 * Complex.I + (-2667 / 256 : ℂ) * (t : ℂ) ^ 5 * (l : ℂ) ^ 3 * Complex.I ^ 3 + (-2249 / 512 : ℂ) * (t : ℂ) ^ 5 * (l : ℂ) ^ 4 * Complex.I + (2249 / 512 : ℂ) * (t : ℂ) ^ 5 * (l : ℂ) ^ 4 * Complex.I ^ 3 + (36367 / 32 : ℂ) * (t : ℂ) ^ 7 * Complex.I + (-36367 / 32 : ℂ) * (t : ℂ) ^ 7 * Complex.I ^ 3 + (36367 / 32 : ℂ) * (t : ℂ) ^ 7 * Complex.I ^ 5 + (16915 / 64 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) * Complex.I + (-16915 / 64 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) * Complex.I ^ 3 + (16915 / 64 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) * Complex.I ^ 5 + (6265 / 128 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) ^ 2 * Complex.I + (-6265 / 128 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) ^ 2 * Complex.I ^ 3 + (6265 / 128 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) ^ 2 * Complex.I ^ 5 + (639 / 64 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) ^ 3 * Complex.I + (-639 / 64 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) ^ 3 * Complex.I ^ 3 + (639 / 64 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) ^ 3 * Complex.I ^ 5 + (-31 / 64 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) ^ 4 * Complex.I + (31 / 64 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) ^ 4 * Complex.I ^ 3 + (-31 / 64 : ℂ) * (t : ℂ) ^ 7 * (l : ℂ) ^ 4 * Complex.I ^ 5 + (3151 / 8 : ℂ) * (t : ℂ) ^ 9 * Complex.I + (-3151 / 8 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 3 + (3151 / 8 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 5 + (-3151 / 8 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 7 + (2259 / 8 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) * Complex.I + (-2259 / 8 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) * Complex.I ^ 3 + (2259 / 8 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) * Complex.I ^ 5 + (-2259 / 8 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) * Complex.I ^ 7 + (943 / 32 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 2 * Complex.I + (-943 / 32 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 2 * Complex.I ^ 3 + (943 / 32 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 2 * Complex.I ^ 5 + (-943 / 32 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 2 * Complex.I ^ 7 + (83 / 32 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 3 * Complex.I + (-83 / 32 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 3 * Complex.I ^ 3 + (83 / 32 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 3 * Complex.I ^ 5 + (-83 / 32 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 3 * Complex.I ^ 7 + (5 / 64 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 4 * Complex.I + (-5 / 64 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 4 * Complex.I ^ 3 + (5 / 64 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 4 * Complex.I ^ 5 + (-5 / 64 : ℂ) * (t : ℂ) ^ 9 * (l : ℂ) ^ 4 * Complex.I ^ 7 + (-46 : ℂ) * (t : ℂ) ^ 11 * Complex.I + (46 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 3 + (-46 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 5 + (46 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 7 + (-46 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 9 + (443 / 8 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) * Complex.I + (-443 / 8 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) * Complex.I ^ 3 + (443 / 8 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) * Complex.I ^ 5 + (-443 / 8 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) * Complex.I ^ 7 + (443 / 8 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) * Complex.I ^ 9 + (-47 / 16 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) ^ 2 * Complex.I + (47 / 16 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) ^ 2 * Complex.I ^ 3 + (-47 / 16 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) ^ 2 * Complex.I ^ 5 + (47 / 16 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) ^ 2 * Complex.I ^ 7 + (-47 / 16 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) ^ 2 * Complex.I ^ 9 + (-5 / 8 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) ^ 3 * Complex.I + (5 / 8 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) ^ 3 * Complex.I ^ 3 + (-5 / 8 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) ^ 3 * Complex.I ^ 5 + (5 / 8 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) ^ 3 * Complex.I ^ 7 + (-5 / 8 : ℂ) * (t : ℂ) ^ 11 * (l : ℂ) ^ 3 * Complex.I ^ 9 + (-36 : ℂ) * (t : ℂ) ^ 13 * Complex.I + (36 : ℂ) * (t : ℂ) ^ 13 * Complex.I ^ 3 + (-36 : ℂ) * (t : ℂ) ^ 13 * Complex.I ^ 5 + (36 : ℂ) * (t : ℂ) ^ 13 * Complex.I ^ 7 + (-36 : ℂ) * (t : ℂ) ^ 13 * Complex.I ^ 9 + (36 : ℂ) * (t : ℂ) ^ 13 * Complex.I ^ 11 + (29 / 2 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) * Complex.I + (-29 / 2 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) * Complex.I ^ 3 + (29 / 2 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) * Complex.I ^ 5 + (-29 / 2 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) * Complex.I ^ 7 + (29 / 2 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) * Complex.I ^ 9 + (-29 / 2 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) * Complex.I ^ 11 + (5 / 4 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) ^ 2 * Complex.I + (-5 / 4 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) ^ 2 * Complex.I ^ 3 + (5 / 4 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) ^ 2 * Complex.I ^ 5 + (-5 / 4 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) ^ 2 * Complex.I ^ 7 + (5 / 4 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) ^ 2 * Complex.I ^ 9 + (-5 / 4 : ℂ) * (t : ℂ) ^ 13 * (l : ℂ) ^ 2 * Complex.I ^ 11 + (-8 : ℂ) * (t : ℂ) ^ 15 * Complex.I + (8 : ℂ) * (t : ℂ) ^ 15 * Complex.I ^ 3 + (-8 : ℂ) * (t : ℂ) ^ 15 * Complex.I ^ 5 + (8 : ℂ) * (t : ℂ) ^ 15 * Complex.I ^ 7 + (-8 : ℂ) * (t : ℂ) ^ 15 * Complex.I ^ 9 + (8 : ℂ) * (t : ℂ) ^ 15 * Complex.I ^ 11 + (-8 : ℂ) * (t : ℂ) ^ 15 * Complex.I ^ 13) * Complex.I_sq

theorem skewPlateauMu_line_denominator (t l : ℝ) :
    128 * (2 - (-(l : ℂ))) ^ 2 * ((-(l : ℂ)) - (2 * ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 1) * (2 * ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 2)) *
        ((-(l : ℂ)) - (2 * ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 4) * (2 * ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 5)) =
      ((128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination ((-10240 : ℂ) * (t : ℂ) ^ 2 + (-6144 : ℂ) * (t : ℂ) ^ 2 * (l : ℂ) + (1536 : ℂ) * (t : ℂ) ^ 2 * (l : ℂ) ^ 2 + (1024 : ℂ) * (t : ℂ) ^ 2 * (l : ℂ) ^ 3 + (-8192 : ℂ) * (t : ℂ) ^ 4 + (8192 : ℂ) * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-8192 : ℂ) * (t : ℂ) ^ 4 * (l : ℂ) + (8192 : ℂ) * (t : ℂ) ^ 4 * (l : ℂ) * Complex.I ^ 2 + (-2048 : ℂ) * (t : ℂ) ^ 4 * (l : ℂ) ^ 2 + (2048 : ℂ) * (t : ℂ) ^ 4 * (l : ℂ) ^ 2 * Complex.I ^ 2) * Complex.I_sq

/-- The real denominator of the plateau on the line is positive. -/
theorem skewPlateauLineDen_pos (t l : ℝ) (hl : 0 ≤ l) :
    (0 : ℝ) < 128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2) := by
  have h6 : (0 : ℝ) < 2 + l := by linarith
  have h5 : (0 : ℝ) < (4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2 := by
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      nlinarith [mul_pos h6 h6]
    · have h7 : (0 : ℝ) < t ^ 2 := by positivity
      nlinarith [sq_nonneg (4 * t ^ 2 - 2 - l)]
  exact mul_pos (mul_pos (by norm_num) (pow_pos h6 2)) h5

/-- The plateau is purely imaginary on the line, with the sign of the line form. -/
theorem skewPlateauMu_line (t l : ℝ) (hl : 0 ≤ l) :
    skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ)) * ((128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2) : ℝ) : ℂ) =
      Complex.I * (skewPlateauLineForm t l : ℂ) := by
  have hden : ((128 * (2 + l) ^ 2 * ((4 * t ^ 2 - 2 - l) ^ 2 + 36 * t ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (skewPlateauLineDen_pos t l hl).ne'
  unfold skewPlateauMu
  rw [← skewPlateauMu_line_denominator t l, div_mul_cancel₀ _ (by rw [skewPlateauMu_line_denominator t l]; exact hden)]
  exact skewPlateauMuNumerator_line t l

theorem skewPlateauMu_line_re (t l : ℝ) (hl : 0 ≤ l) :
    (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).re = 0 := by
  have h := congrArg Complex.re (skewPlateauMu_line t l hl)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · exact absurd h' (skewPlateauLineDen_pos t l hl).ne'

/-- The leading part of the line form: negative semidefinite with double zeros at `l = 0` and `l = 4t²`. -/
noncomputable def skewPlateauLineLower (t l : ℝ) : ℝ := (-74655 / 2048 : ℝ) * t + (-95169 / 4096 : ℝ) * t * l + (25245 / 4096 : ℝ) * t * l ^ 2 + (238617 / 8192 : ℝ) * t * l ^ 3 + (226443 / 16384 : ℝ) * t * l ^ 4 + (-58863 / 256 : ℝ) * t ^ 3 + (728753 / 2048 : ℝ) * t ^ 3 * l + (-896173 / 4096 : ℝ) * t ^ 3 * l ^ 2 + (-76823 / 2048 : ℝ) * t ^ 3 * l ^ 3 + (11623 / 1024 : ℝ) * t ^ 3 * l ^ 4 + (-19053 / 32 : ℝ) * t ^ 5 + (402363 / 512 : ℝ) * t ^ 5 * l + (57215 / 1024 : ℝ) * t ^ 5 * l ^ 2 + (-2667 / 256 : ℝ) * t ^ 5 * l ^ 3 + (2249 / 512 : ℝ) * t ^ 5 * l ^ 4 + (-36367 / 32 : ℝ) * t ^ 7 + (-16915 / 64 : ℝ) * t ^ 7 * l + (-6265 / 128 : ℝ) * t ^ 7 * l ^ 2 + (-639 / 64 : ℝ) * t ^ 7 * l ^ 3 + (31 / 64 : ℝ) * t ^ 7 * l ^ 4 + (-3151 / 8 : ℝ) * t ^ 9 + (-2259 / 8 : ℝ) * t ^ 9 * l + (-943 / 32 : ℝ) * t ^ 9 * l ^ 2 + (-83 / 32 : ℝ) * t ^ 9 * l ^ 3 + (46 : ℝ) * t ^ 11 + (-443 / 8 : ℝ) * t ^ 11 * l + (47 / 16 : ℝ) * t ^ 11 * l ^ 2 + (36 : ℝ) * t ^ 13 + (-29 / 2 : ℝ) * t ^ 13 * l + (8 : ℝ) * t ^ 15

theorem skewPlateauLineForm_leading (t l : ℝ) :
    skewPlateauLineForm t l = -(5 / 64) * t ^ 9 * l ^ 2 * (l - 4 * t ^ 2) ^ 2 + skewPlateauLineLower t l := by
  unfold skewPlateauLineForm skewPlateauLineLower
  ring

theorem skewPlateauLineForm_neg_low (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : 40 * t ≤ l) (h2 : l ≤ 3 * t ^ 2) : skewPlateauLineForm t l < 0 := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hg3 : (0 : ℝ) ≤ t - 50 := by linarith
  have hg1 : (0 : ℝ) ≤ l - 40 * t := by linarith
  have hg2 : (0 : ℝ) ≤ 3 * t ^ (2 : ℕ) - l := by linarith
  have hp1 : (0 : ℝ) ≤ l + 40 * t := by linarith
  have hpos_t : (0 : ℝ) < t := by linarith
  have hpos_l : (0 : ℝ) < l := by nlinarith
  have key : -skewPlateauLineForm t l = (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (5 / 32 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l)) + (74655 / 2048 : ℝ) * (t) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (23 / 5000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (23 / 800 : ℝ) * (t ^ (9 : ℕ) * (l - 40 * t) * (l + 40 * t)) + (9 / 1000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (9 / 400 : ℝ) * (t ^ (11 : ℕ) * (l - 40 * t) * (l + 40 * t)) + (1 / 200 : ℝ) * (t ^ (13 : ℕ) * (l - 40 * t) * (l + 40 * t)) + (728753 / 400000000000000000000000 : ℝ) * (t ^ (2 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (728753 / 81920 : ℝ) * (t ^ (2 : ℕ) * l * (l - 40 * t)) + (402363 / 40000000000000000000 : ℝ) * (t ^ (4 : ℕ) * l ^ (2 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ))) + (402363 / 20480 : ℝ) * (t ^ (4 : ℕ) * l * (l - 40 * t)) + (5049 / 200000000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (11443 / 8000000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (47 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (715851 / 800000000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (2037987 / 640000000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (226443 / 16384 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (104607 / 16000000000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (20241 / 3200000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (279 / 160000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (28076365417974725830649 / 400000000000000000000000 : ℝ) * (t ^ (13 : ℕ) * l ^ (2 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have mpos : 0 < t ^ (13 : ℕ) * l ^ (2 : ℕ) := (mul_pos (pow_pos hpos_t 13) (pow_pos hpos_l 2))
  have m0 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (pow_nonneg hg2 2))
  have m1 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) hg2)
  have m2 : 0 ≤ t := ht0
  have m3 : 0 ≤ t ^ (3 : ℕ) := (pow_nonneg ht0 3)
  have m4 : 0 ≤ t ^ (5 : ℕ) := (pow_nonneg ht0 5)
  have m5 : 0 ≤ t ^ (7 : ℕ) := (pow_nonneg ht0 7)
  have m6 : 0 ≤ t ^ (9 : ℕ) := (pow_nonneg ht0 9)
  have m7 : 0 ≤ t * l := (mul_nonneg ht0 hl0)
  have m8 : 0 ≤ t ^ (7 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 7) hl0)
  have m9 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m10 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m11 : 0 ≤ t ^ (13 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 13) hl0)
  have m12 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2))
  have m13 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2))
  have m14 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m15 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3))
  have m16 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3))
  have m17 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3))
  have m18 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3))
  have m19 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m20 : 0 ≤ t ^ (9 : ℕ) * (l - 40 * t) * (l + 40 * t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hg1) hp1)
  have m21 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m22 : 0 ≤ t ^ (11 : ℕ) * (l - 40 * t) * (l + 40 * t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) hg1) hp1)
  have m23 : 0 ≤ t ^ (13 : ℕ) * (l - 40 * t) * (l + 40 * t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 13) hg1) hp1)
  have m24 : 0 ≤ t ^ (2 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 2) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 11)))
  have m25 : 0 ≤ t ^ (2 : ℕ) * l * (l - 40 * t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 2) hl0) hg1)
  have m26 : 0 ≤ t ^ (4 : ℕ) * l ^ (2 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 4) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 9)))
  have m27 : 0 ≤ t ^ (4 : ℕ) * l * (l - 40 * t) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 4) hl0) hg1)
  have m28 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 12)))
  have m29 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m30 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m31 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m32 : 0 ≤ t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 1)))
  have m33 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m34 : 0 ≤ t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m35 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m36 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m37 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m38 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m39 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m40 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m41 : 0 ≤ t ^ (13 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 13) (pow_nonneg hl0 2))
  have h0 : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (5 / 32 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (74655 / 2048 : ℝ) * (t) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (95169 / 4096 : ℝ) * (t * l) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (23 / 5000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (23 / 800 : ℝ) * (t ^ (9 : ℕ) * (l - 40 * t) * (l + 40 * t)) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (9 / 1000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (9 / 400 : ℝ) * (t ^ (11 : ℕ) * (l - 40 * t) * (l + 40 * t)) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (1 / 200 : ℝ) * (t ^ (13 : ℕ) * (l - 40 * t) * (l + 40 * t)) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (728753 / 400000000000000000000000 : ℝ) * (t ^ (2 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (728753 / 81920 : ℝ) * (t ^ (2 : ℕ) * l * (l - 40 * t)) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (402363 / 40000000000000000000 : ℝ) * (t ^ (4 : ℕ) * l ^ (2 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ))) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (402363 / 20480 : ℝ) * (t ^ (4 : ℕ) * l * (l - 40 * t)) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (5049 / 200000000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (11443 / 8000000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (47 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (715851 / 800000000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (2037987 / 640000000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (226443 / 16384 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (104607 / 16000000000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (20241 / 3200000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (279 / 160000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m40
  have hlast : 0 < (28076365417974725830649 / 400000000000000000000000 : ℝ) * (t ^ (13 : ℕ) * l ^ (2 : ℕ)) := mul_pos (by norm_num) mpos
  have hP : 0 < (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l) ^ (2 : ℕ)) + (5 / 32 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (3 * t ^ (2 : ℕ) - l)) + (74655 / 2048 : ℝ) * (t) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (23 / 5000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (23 / 800 : ℝ) * (t ^ (9 : ℕ) * (l - 40 * t) * (l + 40 * t)) + (9 / 1000000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (9 / 400 : ℝ) * (t ^ (11 : ℕ) * (l - 40 * t) * (l + 40 * t)) + (1 / 200 : ℝ) * (t ^ (13 : ℕ) * (l - 40 * t) * (l + 40 * t)) + (728753 / 400000000000000000000000 : ℝ) * (t ^ (2 : ℕ) * l ^ (2 : ℕ) * (t ^ (11 : ℕ) - 50 ^ (11 : ℕ))) + (728753 / 81920 : ℝ) * (t ^ (2 : ℕ) * l * (l - 40 * t)) + (402363 / 40000000000000000000 : ℝ) * (t ^ (4 : ℕ) * l ^ (2 : ℕ) * (t ^ (9 : ℕ) - 50 ^ (9 : ℕ))) + (402363 / 20480 : ℝ) * (t ^ (4 : ℕ) * l * (l - 40 * t)) + (5049 / 200000000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (11443 / 8000000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (47 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (715851 / 800000000000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (238617 / 8192 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (2037987 / 640000000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (226443 / 16384 : ℝ) * (t * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (104607 / 16000000000000 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (20241 / 3200000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (279 / 160000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * ((3 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (28076365417974725830649 / 400000000000000000000000 : ℝ) * (t ^ (13 : ℕ) * l ^ (2 : ℕ)) := add_pos_of_nonneg_of_pos (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) hlast
  rw [← key] at hP
  exact neg_pos.mp hP

theorem skewPlateauLineForm_neg_edge (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : 3 * t ^ 2 ≤ l) (h2 : l ≤ 5 * t ^ 2) : skewPlateauLineForm t l < 0 := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hg3 : (0 : ℝ) ≤ t - 50 := by linarith
  have hg5 : (0 : ℝ) ≤ l - 3 * t ^ (2 : ℕ) := by linarith
  have hg6 : (0 : ℝ) ≤ 5 * t ^ (2 : ℕ) - l := by linarith
  have hpos_t : (0 : ℝ) < t := by linarith
  have hpos_l : (0 : ℝ) < l := by nlinarith
  have key : -skewPlateauLineForm t l = (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ)) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l)) + (41 / 32 : ℝ) * (t ^ (9 : ℕ) * l * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l)) + (379 / 64 : ℝ) * (t ^ (11 : ℕ) * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l)) + (437 / 32 : ℝ) * (t ^ (13 : ℕ) * (5 * t ^ (2 : ℕ) - l)) + (74655 / 2048 : ℝ) * (t) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (23 / 3125000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (9 / 625 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (728753 / 40000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (402363 / 4000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (25245 / 4096 : ℝ) * (t * ((5 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (5049 / 3200000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (11443 / 128000000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (238617 / 8192 : ℝ) * (t * ((5 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ))) + (238617 / 2560000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (226443 / 16384 : ℝ) * (t * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) + (226443 / 409600000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) + (11623 / 10240000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) + (2249 / 2048 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (914654992617970937519 / 80000000000000000000 : ℝ) * (t ^ (15 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have mpos : 0 < t ^ (15 : ℕ) := (pow_pos hpos_t 15)
  have m0 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sq_nonneg (l - 4 * t ^ (2 : ℕ))))
  have m1 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2)) hg5) hg6)
  have m2 : 0 ≤ t ^ (9 : ℕ) * l * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) hg5) hg6)
  have m3 : 0 ≤ t ^ (11 : ℕ) * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) hg5) hg6)
  have m4 : 0 ≤ t ^ (13 : ℕ) * (5 * t ^ (2 : ℕ) - l) := (mul_nonneg (pow_nonneg ht0 13) hg6)
  have m5 : 0 ≤ t := ht0
  have m6 : 0 ≤ t ^ (3 : ℕ) := (pow_nonneg ht0 3)
  have m7 : 0 ≤ t ^ (5 : ℕ) := (pow_nonneg ht0 5)
  have m8 : 0 ≤ t ^ (7 : ℕ) := (pow_nonneg ht0 7)
  have m9 : 0 ≤ t ^ (9 : ℕ) := (pow_nonneg ht0 9)
  have m10 : 0 ≤ t * l := (mul_nonneg ht0 hl0)
  have m11 : 0 ≤ t ^ (7 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 7) hl0)
  have m12 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m13 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m14 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2))
  have m15 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2))
  have m16 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m17 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3))
  have m18 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3))
  have m19 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3))
  have m20 : 0 ≤ t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m21 : 0 ≤ t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m22 : 0 ≤ t ^ (3 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 1)))
  have m23 : 0 ≤ t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m24 : 0 ≤ t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 1)))
  have m25 : 0 ≤ t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m26 : 0 ≤ t * ((5 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m27 : 0 ≤ t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m28 : 0 ≤ t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 2)))
  have m29 : 0 ≤ t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m30 : 0 ≤ t * ((5 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 3)))
  have m31 : 0 ≤ t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (pow_nonneg ht0 7) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m32 : 0 ≤ t * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ)) := (mul_nonneg ht0 (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 4)))
  have m33 : 0 ≤ t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m34 : 0 ≤ t ^ (3 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 4)))
  have m35 : 0 ≤ t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m36 : 0 ≤ t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 5) (sub_nonneg.mpr (pow_le_pow_left₀ hl0 h2 4)))
  have m37 : 0 ≤ t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m38 : 0 ≤ t ^ (15 : ℕ) := (pow_nonneg ht0 15)
  have h0 : 0 ≤ (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (41 / 32 : ℝ) * (t ^ (9 : ℕ) * l * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (379 / 64 : ℝ) * (t ^ (11 : ℕ) * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (437 / 32 : ℝ) * (t ^ (13 : ℕ) * (5 * t ^ (2 : ℕ) - l)) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (74655 / 2048 : ℝ) * (t) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (95169 / 4096 : ℝ) * (t * l) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (23 / 3125000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (9 / 625 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (728753 / 40000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (402363 / 4000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (25245 / 4096 : ℝ) * (t * ((5 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (5049 / 3200000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (11443 / 128000000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (238617 / 8192 : ℝ) * (t * ((5 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ))) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (238617 / 2560000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (226443 / 16384 : ℝ) * (t * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (226443 / 409600000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (11623 / 10240000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (2249 / 2048 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m37
  have hlast : 0 < (914654992617970937519 / 80000000000000000000 : ℝ) * (t ^ (15 : ℕ)) := mul_pos (by norm_num) mpos
  have hP : 0 < (5 / 64 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 4 * t ^ (2 : ℕ)) ^ (2 : ℕ)) + (31 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ) * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l)) + (41 / 32 : ℝ) * (t ^ (9 : ℕ) * l * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l)) + (379 / 64 : ℝ) * (t ^ (11 : ℕ) * (l - 3 * t ^ (2 : ℕ)) * (5 * t ^ (2 : ℕ) - l)) + (437 / 32 : ℝ) * (t ^ (13 : ℕ) * (5 * t ^ (2 : ℕ) - l)) + (74655 / 2048 : ℝ) * (t) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (23 / 3125000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (9 / 625 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (728753 / 2048 : ℝ) * (t ^ (3 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (728753 / 40000000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (402363 / 512 : ℝ) * (t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (1 : ℕ) - l ^ (1 : ℕ))) + (402363 / 4000000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (25245 / 4096 : ℝ) * (t * ((5 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (5049 / 3200000000000000000 : ℝ) * (t ^ (5 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (57215 / 1024 : ℝ) * (t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (2 : ℕ) - l ^ (2 : ℕ))) + (11443 / 128000000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (238617 / 8192 : ℝ) * (t * ((5 * t ^ (2 : ℕ)) ^ (3 : ℕ) - l ^ (3 : ℕ))) + (238617 / 2560000000000000 : ℝ) * (t ^ (7 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (226443 / 16384 : ℝ) * (t * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) + (226443 / 409600000000 : ℝ) * (t ^ (9 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (11623 / 1024 : ℝ) * (t ^ (3 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) + (11623 / 10240000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2249 / 512 : ℝ) * (t ^ (5 : ℕ) * ((5 * t ^ (2 : ℕ)) ^ (4 : ℕ) - l ^ (4 : ℕ))) + (2249 / 2048 : ℝ) * (t ^ (13 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (914654992617970937519 / 80000000000000000000 : ℝ) * (t ^ (15 : ℕ)) := add_pos_of_nonneg_of_pos (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) hlast
  rw [← key] at hP
  exact neg_pos.mp hP

theorem skewPlateauLineForm_neg_high (t l : ℝ) (ht : (50 : ℝ) ≤ t) (h1 : 5 * t ^ 2 ≤ l) : skewPlateauLineForm t l < 0 := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have hg3 : (0 : ℝ) ≤ t - 50 := by linarith
  have hg4 : (0 : ℝ) ≤ l - 5 * t ^ (2 : ℕ) := by linarith
  have hpos_t : (0 : ℝ) < t := by linarith
  have hpos_l : (0 : ℝ) < l := by nlinarith
  have key : -skewPlateauLineForm t l = (3 / 40 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 5 * t ^ (2 : ℕ)) ^ (2 : ℕ)) + (1 / 8 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (l - 5 * t ^ (2 : ℕ))) + (74655 / 2048 : ℝ) * (t) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (23 / 4882812500000 : ℝ) * (t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ))) + (23 / 7812500000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (9 / 976562500 : ℝ) * (t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ))) + (9 / 1562500 : ℝ) * (t ^ (13 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2 / 390625 : ℝ) * (t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ))) + (2 / 625 : ℝ) * (t ^ (15 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (728753 / 62500000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l * (l ^ (3 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (3 : ℕ))) + (728753 / 500000000000000000000000 : ℝ) * (t ^ (3 : ℕ) * l * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (402363 / 6250000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l * (l ^ (3 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (3 : ℕ))) + (402363 / 50000000000000000000 : ℝ) * (t ^ (5 : ℕ) * l * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (5049 / 5000000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ))) + (5049 / 200000000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (11443 / 200000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ))) + (11443 / 8000000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (47 / 1000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ))) + (47 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (238617 / 4000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ) * (l ^ (1 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (1 : ℕ))) + (238617 / 800000000000000000000 : ℝ) * (t * l ^ (3 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (226443 / 640000000000000000 : ℝ) * (t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (11623 / 16000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2249 / 3200000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (31 / 160000 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (359802154992617970937519 / 125000000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) := by
    unfold skewPlateauLineForm
    ring
  have mpos : 0 < t ^ (9 : ℕ) * l ^ (4 : ℕ) := (mul_pos (pow_pos hpos_t 9) (pow_pos hpos_l 4))
  have m0 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 5 * t ^ (2 : ℕ)) ^ (2 : ℕ) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (pow_nonneg hg4 2))
  have m1 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (l - 5 * t ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) hg4)
  have m2 : 0 ≤ t := ht0
  have m3 : 0 ≤ t ^ (3 : ℕ) := (pow_nonneg ht0 3)
  have m4 : 0 ≤ t ^ (5 : ℕ) := (pow_nonneg ht0 5)
  have m5 : 0 ≤ t ^ (7 : ℕ) := (pow_nonneg ht0 7)
  have m6 : 0 ≤ t ^ (9 : ℕ) := (pow_nonneg ht0 9)
  have m7 : 0 ≤ t * l := (mul_nonneg ht0 hl0)
  have m8 : 0 ≤ t ^ (7 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 7) hl0)
  have m9 : 0 ≤ t ^ (9 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 9) hl0)
  have m10 : 0 ≤ t ^ (11 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 11) hl0)
  have m11 : 0 ≤ t ^ (13 : ℕ) * l := (mul_nonneg (pow_nonneg ht0 13) hl0)
  have m12 : 0 ≤ t ^ (3 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 2))
  have m13 : 0 ≤ t ^ (7 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 2))
  have m14 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2))
  have m15 : 0 ≤ t ^ (3 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 3))
  have m16 : 0 ≤ t ^ (5 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 3))
  have m17 : 0 ≤ t ^ (7 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 3))
  have m18 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3))
  have m19 : 0 ≤ t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) h1 4)))
  have m20 : 0 ≤ t ^ (11 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (pow_nonneg ht0 11) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m21 : 0 ≤ t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) h1 4)))
  have m22 : 0 ≤ t ^ (13 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 13) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m23 : 0 ≤ t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ)) := (mul_nonneg (pow_nonneg ht0 9) (sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) h1 4)))
  have m24 : 0 ≤ t ^ (15 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (pow_nonneg ht0 15) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m25 : 0 ≤ t ^ (9 : ℕ) * l * (l ^ (3 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (3 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) (sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) h1 3)))
  have m26 : 0 ≤ t ^ (3 : ℕ) * l * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) hl0) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 12)))
  have m27 : 0 ≤ t ^ (9 : ℕ) * l * (l ^ (3 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (3 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) hl0) (sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) h1 3)))
  have m28 : 0 ≤ t ^ (5 : ℕ) * l * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) hl0) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m29 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) h1 2)))
  have m30 : 0 ≤ t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 12)))
  have m31 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) h1 2)))
  have m32 : 0 ≤ t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m33 : 0 ≤ t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) h1 2)))
  have m34 : 0 ≤ t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 11) (pow_nonneg hl0 2)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m35 : 0 ≤ t ^ (9 : ℕ) * l ^ (3 : ℕ) * (l ^ (1 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (1 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 3)) (sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) h1 1)))
  have m36 : 0 ≤ t * l ^ (3 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 3)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 10)))
  have m37 : 0 ≤ t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ)) := (mul_nonneg (mul_nonneg ht0 (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 8)))
  have m38 : 0 ≤ t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 6)))
  have m39 : 0 ≤ t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 4)))
  have m40 : 0 ≤ t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ)) := (mul_nonneg (mul_nonneg (pow_nonneg ht0 7) (pow_nonneg hl0 4)) (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) ht 2)))
  have m41 : 0 ≤ t ^ (9 : ℕ) * l ^ (4 : ℕ) := (mul_nonneg (pow_nonneg ht0 9) (pow_nonneg hl0 4))
  have h0 : 0 ≤ (3 / 40 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 5 * t ^ (2 : ℕ)) ^ (2 : ℕ)) := mul_nonneg (by norm_num) m0
  have h1 : 0 ≤ (1 / 8 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (l - 5 * t ^ (2 : ℕ))) := mul_nonneg (by norm_num) m1
  have h2 : 0 ≤ (74655 / 2048 : ℝ) * (t) := mul_nonneg (by norm_num) m2
  have h3 : 0 ≤ (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) := mul_nonneg (by norm_num) m3
  have h4 : 0 ≤ (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) := mul_nonneg (by norm_num) m4
  have h5 : 0 ≤ (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) := mul_nonneg (by norm_num) m5
  have h6 : 0 ≤ (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) := mul_nonneg (by norm_num) m6
  have h7 : 0 ≤ (95169 / 4096 : ℝ) * (t * l) := mul_nonneg (by norm_num) m7
  have h8 : 0 ≤ (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) := mul_nonneg (by norm_num) m8
  have h9 : 0 ≤ (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) := mul_nonneg (by norm_num) m9
  have h10 : 0 ≤ (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) := mul_nonneg (by norm_num) m10
  have h11 : 0 ≤ (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) := mul_nonneg (by norm_num) m11
  have h12 : 0 ≤ (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m12
  have h13 : 0 ≤ (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m13
  have h14 : 0 ≤ (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) := mul_nonneg (by norm_num) m14
  have h15 : 0 ≤ (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m15
  have h16 : 0 ≤ (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m16
  have h17 : 0 ≤ (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m17
  have h18 : 0 ≤ (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) := mul_nonneg (by norm_num) m18
  have h19 : 0 ≤ (23 / 4882812500000 : ℝ) * (t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ))) := mul_nonneg (by norm_num) m19
  have h20 : 0 ≤ (23 / 7812500000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m20
  have h21 : 0 ≤ (9 / 976562500 : ℝ) * (t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ))) := mul_nonneg (by norm_num) m21
  have h22 : 0 ≤ (9 / 1562500 : ℝ) * (t ^ (13 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m22
  have h23 : 0 ≤ (2 / 390625 : ℝ) * (t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ))) := mul_nonneg (by norm_num) m23
  have h24 : 0 ≤ (2 / 625 : ℝ) * (t ^ (15 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m24
  have h25 : 0 ≤ (728753 / 62500000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l * (l ^ (3 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (3 : ℕ))) := mul_nonneg (by norm_num) m25
  have h26 : 0 ≤ (728753 / 500000000000000000000000 : ℝ) * (t ^ (3 : ℕ) * l * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) := mul_nonneg (by norm_num) m26
  have h27 : 0 ≤ (402363 / 6250000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l * (l ^ (3 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (3 : ℕ))) := mul_nonneg (by norm_num) m27
  have h28 : 0 ≤ (402363 / 50000000000000000000 : ℝ) * (t ^ (5 : ℕ) * l * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m28
  have h29 : 0 ≤ (5049 / 5000000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ))) := mul_nonneg (by norm_num) m29
  have h30 : 0 ≤ (5049 / 200000000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) := mul_nonneg (by norm_num) m30
  have h31 : 0 ≤ (11443 / 200000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ))) := mul_nonneg (by norm_num) m31
  have h32 : 0 ≤ (11443 / 8000000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m32
  have h33 : 0 ≤ (47 / 1000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ))) := mul_nonneg (by norm_num) m33
  have h34 : 0 ≤ (47 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m34
  have h35 : 0 ≤ (238617 / 4000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ) * (l ^ (1 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (1 : ℕ))) := mul_nonneg (by norm_num) m35
  have h36 : 0 ≤ (238617 / 800000000000000000000 : ℝ) * (t * l ^ (3 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) := mul_nonneg (by norm_num) m36
  have h37 : 0 ≤ (226443 / 640000000000000000 : ℝ) * (t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) := mul_nonneg (by norm_num) m37
  have h38 : 0 ≤ (11623 / 16000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) := mul_nonneg (by norm_num) m38
  have h39 : 0 ≤ (2249 / 3200000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) := mul_nonneg (by norm_num) m39
  have h40 : 0 ≤ (31 / 160000 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) := mul_nonneg (by norm_num) m40
  have hlast : 0 < (359802154992617970937519 / 125000000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) := mul_pos (by norm_num) mpos
  have hP : 0 < (3 / 40 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l - 5 * t ^ (2 : ℕ)) ^ (2 : ℕ)) + (1 / 8 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (l - 5 * t ^ (2 : ℕ))) + (74655 / 2048 : ℝ) * (t) + (58863 / 256 : ℝ) * (t ^ (3 : ℕ)) + (19053 / 32 : ℝ) * (t ^ (5 : ℕ)) + (36367 / 32 : ℝ) * (t ^ (7 : ℕ)) + (3151 / 8 : ℝ) * (t ^ (9 : ℕ)) + (95169 / 4096 : ℝ) * (t * l) + (16915 / 64 : ℝ) * (t ^ (7 : ℕ) * l) + (2259 / 8 : ℝ) * (t ^ (9 : ℕ) * l) + (443 / 8 : ℝ) * (t ^ (11 : ℕ) * l) + (29 / 2 : ℝ) * (t ^ (13 : ℕ) * l) + (896173 / 4096 : ℝ) * (t ^ (3 : ℕ) * l ^ (2 : ℕ)) + (6265 / 128 : ℝ) * (t ^ (7 : ℕ) * l ^ (2 : ℕ)) + (943 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ)) + (76823 / 2048 : ℝ) * (t ^ (3 : ℕ) * l ^ (3 : ℕ)) + (2667 / 256 : ℝ) * (t ^ (5 : ℕ) * l ^ (3 : ℕ)) + (639 / 64 : ℝ) * (t ^ (7 : ℕ) * l ^ (3 : ℕ)) + (83 / 32 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ)) + (23 / 4882812500000 : ℝ) * (t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ))) + (23 / 7812500000 : ℝ) * (t ^ (11 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (9 / 976562500 : ℝ) * (t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ))) + (9 / 1562500 : ℝ) * (t ^ (13 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (2 / 390625 : ℝ) * (t ^ (9 : ℕ) * (l ^ (4 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (4 : ℕ))) + (2 / 625 : ℝ) * (t ^ (15 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (728753 / 62500000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l * (l ^ (3 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (3 : ℕ))) + (728753 / 500000000000000000000000 : ℝ) * (t ^ (3 : ℕ) * l * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (402363 / 6250000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l * (l ^ (3 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (3 : ℕ))) + (402363 / 50000000000000000000 : ℝ) * (t ^ (5 : ℕ) * l * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (5049 / 5000000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ))) + (5049 / 200000000000000000000000 : ℝ) * (t * l ^ (2 : ℕ) * (t ^ (12 : ℕ) - 50 ^ (12 : ℕ))) + (11443 / 200000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ))) + (11443 / 8000000000000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (2 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (47 / 1000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (2 : ℕ) * (l ^ (2 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (2 : ℕ))) + (47 / 40000 : ℝ) * (t ^ (11 : ℕ) * l ^ (2 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (238617 / 4000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (3 : ℕ) * (l ^ (1 : ℕ) - (5 * t ^ (2 : ℕ)) ^ (1 : ℕ))) + (238617 / 800000000000000000000 : ℝ) * (t * l ^ (3 : ℕ) * (t ^ (10 : ℕ) - 50 ^ (10 : ℕ))) + (226443 / 640000000000000000 : ℝ) * (t * l ^ (4 : ℕ) * (t ^ (8 : ℕ) - 50 ^ (8 : ℕ))) + (11623 / 16000000000000 : ℝ) * (t ^ (3 : ℕ) * l ^ (4 : ℕ) * (t ^ (6 : ℕ) - 50 ^ (6 : ℕ))) + (2249 / 3200000000 : ℝ) * (t ^ (5 : ℕ) * l ^ (4 : ℕ) * (t ^ (4 : ℕ) - 50 ^ (4 : ℕ))) + (31 / 160000 : ℝ) * (t ^ (7 : ℕ) * l ^ (4 : ℕ) * (t ^ (2 : ℕ) - 50 ^ (2 : ℕ))) + (359802154992617970937519 / 125000000000000000000000000 : ℝ) * (t ^ (9 : ℕ) * l ^ (4 : ℕ)) := add_pos_of_nonneg_of_pos (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) hlast
  rw [← key] at hP
  exact neg_pos.mp hP

/-- For `t ≥ 50` the line form is negative at every harmonic `l ≥ 40 t`. -/
theorem skewPlateauLineForm_neg (t l : ℝ) (ht : (50 : ℝ) ≤ t) (hl : 40 * t ≤ l) : skewPlateauLineForm t l < 0 := by
  rcases le_or_gt l (3 * t ^ 2) with h3 | h3
  · exact skewPlateauLineForm_neg_low t l ht hl h3
  · rcases le_or_gt l (5 * t ^ 2) with h5 | h5
    · exact skewPlateauLineForm_neg_edge t l ht h3.le h5
    · exact skewPlateauLineForm_neg_high t l ht h5.le

/-- On the critical line at height `t ≥ 50` the general-harmonic plateau has negative imaginary part
at every harmonic `l ≥ 40 t`. -/
theorem skewPlateauMu_line_im_neg (t l : ℝ) (ht : (50 : ℝ) ≤ t) (hl : 40 * t ≤ l) :
    (skewPlateauMu ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) (-(l : ℂ))).im < 0 := by
  have hl0 : (0 : ℝ) ≤ l := by nlinarith
  have h := congrArg Complex.im (skewPlateauMu_line t l hl0)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
  have hden := skewPlateauLineDen_pos t l hl0
  have hF := skewPlateauLineForm_neg t l ht hl
  nlinarith

end RHTower.D4BMScalarStream
