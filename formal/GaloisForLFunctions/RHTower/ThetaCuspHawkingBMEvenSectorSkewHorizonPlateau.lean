import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewFullTilt
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewLineSign

/-!
# The horizon plateau of the two-rate current in the ingoing clock

In ingoing coordinates `v = t + r_*` the stationary two-rate current `e^{−6t}·Ω_static(r)` is regular
at the future horizon. Its time component is `Ω^v = Ω^t + Ω^r/(r²−1)`, and on the slice `v = 0` the
dressed density `e^{6r_*}·z^{−3}·r²·Ω^v` in the variable `w = 1/r` is
`skewIngoingTimeComponent s w = skewIngoingNumerator s w / (1+w)⁷`, where the polynomial numerator
satisfies `(1−w)·skewIngoingNumerator s w = w²·(2w·skewLaurentSS s w + skewRadLaurent s w)`
(`skewIngoingNumerator_spec`): the horizon poles of the static time component and of the radial flux
cancel exactly (`2·skewLaurentSS s 1 + skewRadLaurent s 1 = 0`). Its horizon value
`skewHorizonPlateau s = skewIngoingNumerator s 1 / 128` and the horizon value of the dressed radial
flux `skewHorizonFlux s = skewRadLaurent s 1 / 64` are the plateau values that a translation moment at
rate `−6` in the ingoing clock reads off the post-onset current; both are explicit (`_eq`), odd under
the rate swap `s ↦ −3−s` (`_reflect`), and purely imaginary on the critical line (`_line`).

Sign laws. On the line the plateau has negative imaginary part for every height `t ≥ 1`
(`skewHorizonPlateau_line_im_neg`) and the flux has positive imaginary part for `t ≥ 5`
(`skewHorizonFlux_line_im_pos`). Off the line the reflected-pair difference quotient gives
`2·Re(plateau)·|s(s+3)|² = (2σ−1)·skewPlateauTiltCofactor σ t` with leading term `−(45/8192)·t¹²`
and `2·Re(flux) = (2σ−1)·skewFluxTiltCofactor σ t` with leading term `(45/4096)·t⁸`; on the strip
the cofactors have these signs for `t ≥ 44` and `t ≥ 17` respectively, so the real parts vanish
exactly on the critical line there (`skewHorizonPlateau_re_eq_zero_iff`, `skewHorizonFlux_re_eq_zero_iff`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

/-- Polynomial numerator of the dressed ingoing time component in `w = 1/r`. -/
noncomputable def skewIngoingNumerator (s w : ℂ) : ℂ := (((3 : ℂ) + (-5 / 2 : ℂ) * s + (-9 / 2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) / (s * (s + 3))) + (((15 / 2 : ℂ) + (-13 : ℂ) * s + (-18 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 3) / (s * (s + 3))) * w + (((-45 : ℂ) * s + (-261 / 4 : ℂ) * s ^ 2 + (-37 : ℂ) * s ^ 3 + (-45 / 4 : ℂ) * s ^ 4 + (-3 / 2 : ℂ) * s ^ 5) / (s * (s + 3))) * w ^ 2 + (((6 : ℂ) + (143 / 2 : ℂ) * s + (1161 / 8 : ℂ) * s ^ 2 + (237 / 2 : ℂ) * s ^ 3 + (345 / 8 : ℂ) * s ^ 4 + (23 / 4 : ℂ) * s ^ 5) / (s * (s + 3))) * w ^ 3 + (((21 / 2 : ℂ) + (-71 / 4 : ℂ) * s + (-387 / 2 : ℂ) * s ^ 2 + (-352 : ℂ) * s ^ 3 + (-1185 / 4 : ℂ) * s ^ 4 + (-134 : ℂ) * s ^ 5 + (-63 / 2 : ℂ) * s ^ 6 + (-3 : ℂ) * s ^ 7) / (s * (s + 3))) * w ^ 4 + (((-171 / 4 : ℂ) * s + (-3519 / 16 : ℂ) * s ^ 2 + (-11509 / 32 : ℂ) * s ^ 3 + (-9225 / 32 : ℂ) * s ^ 4 + (-4065 / 32 : ℂ) * s ^ 5 + (-945 / 32 : ℂ) * s ^ 6 + (-45 / 16 : ℂ) * s ^ 7) / (s * (s + 3))) * w ^ 5 + (((9 / 2 : ℂ) * s + (-261 / 8 : ℂ) * s ^ 2 + (-1441 / 8 : ℂ) * s ^ 3 + (-11811 / 32 : ℂ) * s ^ 4 + (-6281 / 16 : ℂ) * s ^ 5 + (-3759 / 16 : ℂ) * s ^ 6 + (-319 / 4 : ℂ) * s ^ 7 + (-459 / 32 : ℂ) * s ^ 8 + (-17 / 16 : ℂ) * s ^ 9) / (s * (s + 3))) * w ^ 6 + (((9 / 2 : ℂ) * s + (207 / 4 : ℂ) * s ^ 2 + (1403 / 8 : ℂ) * s ^ 3 + (4605 / 16 : ℂ) * s ^ 4 + (1067 / 4 : ℂ) * s ^ 5 + (147 : ℂ) * s ^ 6 + (191 / 4 : ℂ) * s ^ 7 + (135 / 16 : ℂ) * s ^ 8 + (5 / 8 : ℂ) * s ^ 9) / (s * (s + 3))) * w ^ 7 + (((135 / 16 : ℂ) * s ^ 2 + (765 / 32 : ℂ) * s ^ 3 + (435 / 64 : ℂ) * s ^ 4 + (-6805 / 128 : ℂ) * s ^ 5 + (-11865 / 128 : ℂ) * s ^ 6 + (-2375 / 32 : ℂ) * s ^ 7 + (-135 / 4 : ℂ) * s ^ 8 + (-1145 / 128 : ℂ) * s ^ 9 + (-165 / 128 : ℂ) * s ^ 10 + (-5 / 64 : ℂ) * s ^ 11) / (s * (s + 3))) * w ^ 8

/-- The horizon poles of the static time component and of the radial flux cancel in the ingoing
time component. -/
theorem skewIngoingNumerator_spec (s w : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hw : w ≠ 0) :
    (1 - w) * skewIngoingNumerator s w = w ^ 2 * (2 * w * skewLaurentSS s w + skewRadLaurent s w) := by
  unfold skewIngoingNumerator skewLaurentSS skewRadLaurent
  field_simp
  ring

/-- The dressed ingoing time component `e^{6r_*} z^{−3} r² Ω^v` in the variable `w = 1/r`. -/
noncomputable def skewIngoingTimeComponent (s w : ℂ) : ℂ := skewIngoingNumerator s w / (1 + w) ^ 7

/-- Away from the horizon and the boundary the ingoing time component is the tortoise factor times the
static time component plus the radial flux over `r² − 1`. -/
theorem skewIngoingTimeComponent_eq (s : ℂ) (w : ℝ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hw : (w : ℂ) ≠ 0)
    (hw1 : (1 : ℂ) - w ≠ 0) (hw2 : (1 : ℂ) + w ≠ 0) :
    skewIngoingTimeComponent s w = (w : ℂ) ^ 2 * ((1 - (w : ℂ)) / (1 + (w : ℂ))) ^ 3 *
      (skewBulkIntegrand s w + skewRadLaurent s w / (1 - (w : ℂ) ^ 2) ^ 4) := by
  have hspec := skewIngoingNumerator_spec s w hs hs3 hw
  have hM : skewIngoingNumerator s w = (w : ℂ) ^ 2 * (2 * w * skewLaurentSS s w + skewRadLaurent s w) / (1 - w) := by
    rw [eq_div_iff hw1]; linear_combination hspec
  unfold skewIngoingTimeComponent skewBulkIntegrand
  rw [hM, show (1 - (w : ℂ) ^ 2) ^ 4 = (1 - w) ^ 4 * (1 + w) ^ 4 by ring]
  field_simp

/-- Horizon value of the dressed ingoing time component. -/
noncomputable def skewHorizonPlateau (s : ℂ) : ℂ := skewIngoingNumerator s 1 / 128

/-- Horizon value of the dressed radial flux. -/
noncomputable def skewHorizonFlux (s : ℂ) : ℂ := skewRadLaurent s 1 / 64

theorem skewHorizonPlateau_eq_component (s : ℂ) : skewHorizonPlateau s = skewIngoingTimeComponent s 1 := by
  unfold skewHorizonPlateau skewIngoingTimeComponent
  norm_num

theorem skewHorizonPlateau_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewHorizonPlateau s = (((27 / 128 : ℂ) + (-81 / 256 : ℂ) * s + (-657 / 256 : ℂ) * s ^ 2 + (-77 / 16 : ℂ) * s ^ 3 + (-40137 / 8192 : ℂ) * s ^ 4 + (-55777 / 16384 : ℂ) * s ^ 5 + (-30933 / 16384 : ℂ) * s ^ 6 + (-3585 / 4096 : ℂ) * s ^ 7 + (-1269 / 4096 : ℂ) * s ^ 8 + (-1201 / 16384 : ℂ) * s ^ 9 + (-165 / 16384 : ℂ) * s ^ 10 + (-5 / 8192 : ℂ) * s ^ 11) / (s * (s + 3))) := by
  unfold skewHorizonPlateau skewIngoingNumerator
  field_simp
  ring

theorem skewHorizonFlux_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewHorizonFlux s = (27 / 64 : ℂ) + (585 / 512 : ℂ) * s + (2151 / 1024 : ℂ) * s ^ 2 + (12331 / 4096 : ℂ) * s ^ 3 + (22785 / 8192 : ℂ) * s ^ 4 + (3185 / 2048 : ℂ) * s ^ 5 + (273 / 512 : ℂ) * s ^ 6 + (239 / 2048 : ℂ) * s ^ 7 + (135 / 8192 : ℂ) * s ^ 8 + (5 / 4096 : ℂ) * s ^ 9 := by
  unfold skewHorizonFlux skewRadLaurent
  field_simp
  ring

theorem skewHorizonPlateau_reflect (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewHorizonPlateau (-3 - s) = -skewHorizonPlateau s := by
  have hs' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  have hs3' : (-3 : ℂ) - s + 3 ≠ 0 := by intro h; apply hs; linear_combination -h
  rw [skewHorizonPlateau_eq _ hs' hs3', skewHorizonPlateau_eq s hs hs3]
  field_simp
  ring

theorem skewHorizonFlux_reflect (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewHorizonFlux (-3 - s) = -skewHorizonFlux s := by
  have hs' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  have hs3' : (-3 : ℂ) - s + 3 ≠ 0 := by intro h; apply hs; linear_combination -h
  rw [skewHorizonFlux_eq _ hs' hs3', skewHorizonFlux_eq s hs hs3]
  ring

/-- Imaginary part of the plateau's numerator on the critical line, an odd polynomial. -/
noncomputable def skewPlateauLineNumerator (t : ℝ) : ℝ := (238005 / 8388608 : ℝ) * t + (-47783 / 2097152 : ℝ) * t ^ 3 + (23273 / 262144 : ℝ) * t ^ 5 + (2361 / 65536 : ℝ) * t ^ 7 + (73 / 32768 : ℝ) * t ^ 9 + (5 / 8192 : ℝ) * t ^ 11

noncomputable def skewPlateauLineEven (u : ℝ) : ℝ := (238005 / 8388608 : ℝ) + (-47783 / 2097152 : ℝ) * u + (23273 / 262144 : ℝ) * u ^ 2 + (2361 / 65536 : ℝ) * u ^ 3 + (73 / 32768 : ℝ) * u ^ 4 + (5 / 8192 : ℝ) * u ^ 5

theorem skewPlateauLineNumerator_eq (t : ℝ) : skewPlateauLineNumerator t = t * skewPlateauLineEven (t ^ 2) := by
  unfold skewPlateauLineNumerator skewPlateauLineEven
  ring

/-- On the critical line the plateau is purely imaginary. -/
theorem skewHorizonPlateau_line (t : ℝ) :
    skewHorizonPlateau ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) * (-(9 / 4 + (t : ℂ) ^ 2)) =
      Complex.I * (skewPlateauLineNumerator t : ℂ) := by
  have hne : ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) * (((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 3) ≠ 0 := by
    rw [line_denominator]
    intro h
    rw [show (-(9 / 4 + (t : ℂ) ^ 2)) = ((-(9 / 4 + t ^ 2) : ℝ) : ℂ) by push_cast; ring] at h
    have h' : -(9 / 4 + t ^ 2) = (0 : ℝ) := by exact_mod_cast h
    nlinarith [sq_nonneg t]
  have hs : ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := left_ne_zero_of_mul hne
  have hs3 : ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 3 ≠ 0 := right_ne_zero_of_mul hne
  rw [← line_denominator, skewHorizonPlateau_eq _ hs hs3, div_mul_cancel₀ _ hne]
  unfold skewPlateauLineNumerator
  push_cast
  linear_combination ((47783 / 2097152 : ℂ) * (t : ℂ) ^ 3 * Complex.I + (-23273 / 262144 : ℂ) * (t : ℂ) ^ 5 * Complex.I + (23273 / 262144 : ℂ) * (t : ℂ) ^ 5 * Complex.I ^ 3 + (-2361 / 65536 : ℂ) * (t : ℂ) ^ 7 * Complex.I + (2361 / 65536 : ℂ) * (t : ℂ) ^ 7 * Complex.I ^ 3 + (-2361 / 65536 : ℂ) * (t : ℂ) ^ 7 * Complex.I ^ 5 + (-73 / 32768 : ℂ) * (t : ℂ) ^ 9 * Complex.I + (73 / 32768 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 3 + (-73 / 32768 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 5 + (73 / 32768 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 7 + (-5 / 8192 : ℂ) * (t : ℂ) ^ 11 * Complex.I + (5 / 8192 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 3 + (-5 / 8192 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 5 + (5 / 8192 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 7 + (-5 / 8192 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 9) * Complex.I_sq

theorem skewPlateauLineEven_pos (u : ℝ) (hu : 1 ≤ u) : 0 < skewPlateauLineEven u := by
  unfold skewPlateauLineEven
  have h2 : u ≤ u ^ 2 := by nlinarith
  have h3 : u ^ 2 ≤ u ^ 3 := by nlinarith
  have h4 : u ^ 3 ≤ u ^ 4 := by nlinarith
  have h5 : u ^ 4 ≤ u ^ 5 := by nlinarith
  nlinarith

/-- On the critical line the plateau has negative imaginary part at every height `t ≥ 1`. -/
theorem skewHorizonPlateau_line_im_neg (t : ℝ) (ht : 1 ≤ t) :
    (skewHorizonPlateau ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im < 0 := by
  have h := congrArg Complex.im (skewHorizonPlateau_line t)
  have hd : (0 : ℝ) < 9 / 4 + t ^ 2 := by positivity
  have h' : (skewHorizonPlateau ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im * (-(9 / 4 + t ^ 2)) = skewPlateauLineNumerator t := by
    have e1 : (-(9 / 4 + (t : ℂ) ^ 2)) = ((-(9 / 4 + t ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [e1] at h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
    exact h
  have hP : 0 < skewPlateauLineNumerator t := by
    rw [skewPlateauLineNumerator_eq]
    exact mul_pos (by linarith) (skewPlateauLineEven_pos (t ^ 2) (by nlinarith))
  nlinarith

theorem skewHorizonPlateau_line_re (t : ℝ) : (skewHorizonPlateau ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).re = 0 := by
  have h := congrArg Complex.re (skewHorizonPlateau_line t)
  have hd : (9 / 4 + t ^ 2) ≠ (0 : ℝ) := by positivity
  have e1 : (-(9 / 4 + (t : ℂ) ^ 2)) = ((-(9 / 4 + t ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  simp at h
  rcases h with h | h
  · exact h
  · nlinarith [sq_nonneg t]

/-- Imaginary part of the flux on the critical line, an odd polynomial. -/
noncomputable def skewFluxLineNumerator (t : ℝ) : ℝ := (19341 / 1048576 : ℝ) * t + (-10501 / 65536 : ℝ) * t ^ 3 + (-2149 / 32768 : ℝ) * t ^ 5 + (-73 / 4096 : ℝ) * t ^ 7 + (5 / 4096 : ℝ) * t ^ 9

noncomputable def skewFluxLineEven (u : ℝ) : ℝ := (19341 / 1048576 : ℝ) + (-10501 / 65536 : ℝ) * u + (-2149 / 32768 : ℝ) * u ^ 2 + (-73 / 4096 : ℝ) * u ^ 3 + (5 / 4096 : ℝ) * u ^ 4

theorem skewFluxLineNumerator_eq (t : ℝ) : skewFluxLineNumerator t = t * skewFluxLineEven (t ^ 2) := by
  unfold skewFluxLineNumerator skewFluxLineEven
  ring

/-- On the critical line the flux is purely imaginary. -/
theorem skewHorizonFlux_line (t : ℝ) :
    skewHorizonFlux ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) = Complex.I * (skewFluxLineNumerator t : ℂ) := by
  have hs : ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hs3 : ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 3 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [skewHorizonFlux_eq _ hs hs3]
  unfold skewFluxLineNumerator
  push_cast
  linear_combination ((10501 / 65536 : ℂ) * (t : ℂ) ^ 3 * Complex.I + (2149 / 32768 : ℂ) * (t : ℂ) ^ 5 * Complex.I + (-2149 / 32768 : ℂ) * (t : ℂ) ^ 5 * Complex.I ^ 3 + (73 / 4096 : ℂ) * (t : ℂ) ^ 7 * Complex.I + (-73 / 4096 : ℂ) * (t : ℂ) ^ 7 * Complex.I ^ 3 + (73 / 4096 : ℂ) * (t : ℂ) ^ 7 * Complex.I ^ 5 + (-5 / 4096 : ℂ) * (t : ℂ) ^ 9 * Complex.I + (5 / 4096 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 3 + (-5 / 4096 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 5 + (5 / 4096 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 7) * Complex.I_sq

theorem skewFluxLineEven_pos (u : ℝ) (hu : 25 ≤ u) : 0 < skewFluxLineEven u := by
  unfold skewFluxLineEven
  have h2 : 25 * u ≤ u ^ 2 := by nlinarith
  have h3 : 25 * u ^ 2 ≤ u ^ 3 := by nlinarith
  have h4 : 25 * u ^ 3 ≤ u ^ 4 := by nlinarith
  nlinarith

/-- On the critical line the flux has positive imaginary part for `t ≥ 5`. -/
theorem skewHorizonFlux_line_im_pos (t : ℝ) (ht : 5 ≤ t) :
    0 < (skewHorizonFlux ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im := by
  have h' : (skewHorizonFlux ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = skewFluxLineNumerator t := by
    rw [skewHorizonFlux_line]; simp
  rw [h', skewFluxLineNumerator_eq]
  exact mul_pos (by linarith) (skewFluxLineEven_pos (t ^ 2) (by nlinarith))

theorem skewHorizonFlux_line_re (t : ℝ) : (skewHorizonFlux ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).re = 0 := by
  rw [skewHorizonFlux_line]
  simp

/-- Difference-quotient cofactor of the plateau. -/
noncomputable def skewPlateauCofactor (s w : ℂ) : ℂ := (-81 / 128 : ℂ) + (-27 / 128 : ℂ) * w + (-27 / 128 : ℂ) * s + (-945 / 128 : ℂ) * s * w + (-231 / 16 : ℂ) * s * w ^ 2 + (-120411 / 8192 : ℂ) * s * w ^ 3 + (-167331 / 16384 : ℂ) * s * w ^ 4 + (-92799 / 16384 : ℂ) * s * w ^ 5 + (-10755 / 4096 : ℂ) * s * w ^ 6 + (-3807 / 4096 : ℂ) * s * w ^ 7 + (-3603 / 16384 : ℂ) * s * w ^ 8 + (-495 / 16384 : ℂ) * s * w ^ 9 + (-15 / 8192 : ℂ) * s * w ^ 10 + (-231 / 16 : ℂ) * s ^ 2 * w + (-159835 / 8192 : ℂ) * s ^ 2 * w ^ 2 + (-247605 / 16384 : ℂ) * s ^ 2 * w ^ 3 + (-4643 / 512 : ℂ) * s ^ 2 * w ^ 4 + (-73953 / 16384 : ℂ) * s ^ 2 * w ^ 5 + (-231 / 128 : ℂ) * s ^ 2 * w ^ 6 + (-8679 / 16384 : ℂ) * s ^ 2 * w ^ 7 + (-53 / 512 : ℂ) * s ^ 2 * w ^ 8 + (-195 / 16384 : ℂ) * s ^ 2 * w ^ 9 + (-5 / 8192 : ℂ) * s ^ 2 * w ^ 10 + (-120411 / 8192 : ℂ) * s ^ 3 * w + (-247605 / 16384 : ℂ) * s ^ 3 * w ^ 2 + (-4643 / 512 : ℂ) * s ^ 3 * w ^ 3 + (-73953 / 16384 : ℂ) * s ^ 3 * w ^ 4 + (-231 / 128 : ℂ) * s ^ 3 * w ^ 5 + (-8679 / 16384 : ℂ) * s ^ 3 * w ^ 6 + (-53 / 512 : ℂ) * s ^ 3 * w ^ 7 + (-195 / 16384 : ℂ) * s ^ 3 * w ^ 8 + (-5 / 8192 : ℂ) * s ^ 3 * w ^ 9 + (-167331 / 16384 : ℂ) * s ^ 4 * w + (-4643 / 512 : ℂ) * s ^ 4 * w ^ 2 + (-73953 / 16384 : ℂ) * s ^ 4 * w ^ 3 + (-231 / 128 : ℂ) * s ^ 4 * w ^ 4 + (-8679 / 16384 : ℂ) * s ^ 4 * w ^ 5 + (-53 / 512 : ℂ) * s ^ 4 * w ^ 6 + (-195 / 16384 : ℂ) * s ^ 4 * w ^ 7 + (-5 / 8192 : ℂ) * s ^ 4 * w ^ 8 + (-92799 / 16384 : ℂ) * s ^ 5 * w + (-73953 / 16384 : ℂ) * s ^ 5 * w ^ 2 + (-231 / 128 : ℂ) * s ^ 5 * w ^ 3 + (-8679 / 16384 : ℂ) * s ^ 5 * w ^ 4 + (-53 / 512 : ℂ) * s ^ 5 * w ^ 5 + (-195 / 16384 : ℂ) * s ^ 5 * w ^ 6 + (-5 / 8192 : ℂ) * s ^ 5 * w ^ 7 + (-10755 / 4096 : ℂ) * s ^ 6 * w + (-231 / 128 : ℂ) * s ^ 6 * w ^ 2 + (-8679 / 16384 : ℂ) * s ^ 6 * w ^ 3 + (-53 / 512 : ℂ) * s ^ 6 * w ^ 4 + (-195 / 16384 : ℂ) * s ^ 6 * w ^ 5 + (-5 / 8192 : ℂ) * s ^ 6 * w ^ 6 + (-3807 / 4096 : ℂ) * s ^ 7 * w + (-8679 / 16384 : ℂ) * s ^ 7 * w ^ 2 + (-53 / 512 : ℂ) * s ^ 7 * w ^ 3 + (-195 / 16384 : ℂ) * s ^ 7 * w ^ 4 + (-5 / 8192 : ℂ) * s ^ 7 * w ^ 5 + (-3603 / 16384 : ℂ) * s ^ 8 * w + (-53 / 512 : ℂ) * s ^ 8 * w ^ 2 + (-195 / 16384 : ℂ) * s ^ 8 * w ^ 3 + (-5 / 8192 : ℂ) * s ^ 8 * w ^ 4 + (-495 / 16384 : ℂ) * s ^ 9 * w + (-195 / 16384 : ℂ) * s ^ 9 * w ^ 2 + (-5 / 8192 : ℂ) * s ^ 9 * w ^ 3 + (-15 / 8192 : ℂ) * s ^ 10 * w + (-5 / 8192 : ℂ) * s ^ 10 * w ^ 2

theorem skewHorizonPlateau_sub (s w : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hw : w ≠ 0) (hw3 : w + 3 ≠ 0) :
    skewHorizonPlateau s - skewHorizonPlateau w = (s - w) * skewPlateauCofactor s w / (s * (s + 3) * (w * (w + 3))) := by
  rw [skewHorizonPlateau_eq s hs hs3, skewHorizonPlateau_eq w hw hw3]
  unfold skewPlateauCofactor
  field_simp
  ring

/-- The plateau's cofactor at the reflected pair, as a real polynomial. -/
noncomputable def skewPlateauTiltCofactor (σ t : ℝ) : ℝ := (-5 / 64 : ℝ) + (301 / 512 : ℝ) * t ^ 2 + (-97 / 256 : ℝ) * t ^ 4 + (-6255 / 8192 : ℝ) * t ^ 6 + (-1275 / 8192 : ℝ) * t ^ 8 + (-169 / 8192 : ℝ) * t ^ 10 + (-45 / 8192 : ℝ) * t ^ 12 + (21 / 256 : ℝ) * σ + (-629 / 512 : ℝ) * σ * t ^ 2 + (-9871 / 4096 : ℝ) * σ * t ^ 4 + (-555 / 4096 : ℝ) * σ * t ^ 6 + (-1161 / 4096 : ℝ) * σ * t ^ 8 + (-165 / 4096 : ℝ) * σ * t ^ 10 + (-75 / 512 : ℝ) * σ ^ 2 + (-129 / 512 : ℝ) * σ ^ 2 * t ^ 2 + (21299 / 8192 : ℝ) * σ ^ 2 * t ^ 4 + (-477 / 1024 : ℝ) * σ ^ 2 * t ^ 6 + (2487 / 8192 : ℝ) * σ ^ 2 * t ^ 8 + (165 / 4096 : ℝ) * σ ^ 2 * t ^ 10 + (-1 / 512 : ℝ) * σ ^ 3 + (5319 / 2048 : ℝ) * σ ^ 3 * t ^ 2 + (-3221 / 4096 : ℝ) * σ ^ 3 * t ^ 4 + (657 / 512 : ℝ) * σ ^ 3 * t ^ 6 + (-165 / 4096 : ℝ) * σ ^ 3 * t ^ 8 + (149 / 512 : ℝ) * σ ^ 4 + (-3941 / 8192 : ℝ) * σ ^ 4 * t ^ 2 + (5633 / 4096 : ℝ) * σ ^ 4 * t ^ 4 + (-3453 / 4096 : ℝ) * σ ^ 4 * t ^ 6 + (165 / 8192 : ℝ) * σ ^ 4 * t ^ 8 + (-1011 / 4096 : ℝ) * σ ^ 5 + (-3049 / 4096 : ℝ) * σ ^ 5 * t ^ 2 + (-2221 / 2048 : ℝ) * σ ^ 5 * t ^ 4 + (495 / 2048 : ℝ) * σ ^ 5 * t ^ 6 + (-647 / 8192 : ℝ) * σ ^ 6 + (-43 / 512 : ℝ) * σ ^ 6 * t ^ 2 + (839 / 4096 : ℝ) * σ ^ 6 * t ^ 4 + (-165 / 2048 : ℝ) * σ ^ 6 * t ^ 6 + (513 / 4096 : ℝ) * σ ^ 7 + (41 / 256 : ℝ) * σ ^ 7 * t ^ 2 + (275 / 2048 : ℝ) * σ ^ 7 * t ^ 4 + (-159 / 8192 : ℝ) * σ ^ 8 + (947 / 8192 : ℝ) * σ ^ 8 * t ^ 2 + (-275 / 8192 : ℝ) * σ ^ 8 * t ^ 4 + (-5 / 4096 : ℝ) * σ ^ 9 + (-425 / 4096 : ℝ) * σ ^ 9 * t ^ 2 + (-53 / 8192 : ℝ) * σ ^ 10 + (85 / 4096 : ℝ) * σ ^ 10 * t ^ 2 + (15 / 4096 : ℝ) * σ ^ 11 + (-5 / 8192 : ℝ) * σ ^ 12

theorem skewPlateauCofactor_reflected (σ t : ℝ) :
    skewPlateauCofactor ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) (-1 - (σ : ℂ) + (t : ℂ) * Complex.I) = (skewPlateauTiltCofactor σ t : ℂ) := by
  unfold skewPlateauCofactor skewPlateauTiltCofactor
  push_cast
  linear_combination ((-301 / 512 : ℂ) * (t : ℂ) ^ 2 + (97 / 256 : ℂ) * (t : ℂ) ^ 4 + (-97 / 256 : ℂ) * (t : ℂ) ^ 4 * Complex.I ^ 2 + (6255 / 8192 : ℂ) * (t : ℂ) ^ 6 + (-6255 / 8192 : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 2 + (6255 / 8192 : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 4 + (1275 / 8192 : ℂ) * (t : ℂ) ^ 8 + (-1275 / 8192 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 2 + (1275 / 8192 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 4 + (-1275 / 8192 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 6 + (169 / 8192 : ℂ) * (t : ℂ) ^ 10 + (-169 / 8192 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 2 + (169 / 8192 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 4 + (-169 / 8192 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 6 + (169 / 8192 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 8 + (45 / 8192 : ℂ) * (t : ℂ) ^ 12 + (-45 / 8192 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 2 + (45 / 8192 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 4 + (-45 / 8192 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 6 + (45 / 8192 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 8 + (-45 / 8192 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 10 + (629 / 512 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 2 + (9871 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 4 + (-9871 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 4 * Complex.I ^ 2 + (555 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 + (-555 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 2 + (555 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 4 + (1161 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 + (-1161 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 2 + (1161 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 4 + (-1161 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 6 + (165 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 + (-165 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 2 + (165 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 4 + (-165 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 6 + (165 / 4096 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 8 + (129 / 512 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 2 + (-21299 / 8192 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 4 + (21299 / 8192 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (477 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 + (-477 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (477 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-2487 / 8192 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 + (2487 / 8192 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 * Complex.I ^ 2 + (-2487 / 8192 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 * Complex.I ^ 4 + (2487 / 8192 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 * Complex.I ^ 6 + (-165 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 + (165 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 2 + (-165 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 4 + (165 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 6 + (-165 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 8 + (-5319 / 2048 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 2 + (3221 / 4096 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 4 + (-3221 / 4096 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-657 / 512 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 6 + (657 / 512 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (-657 / 512 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (165 / 4096 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 + (-165 / 4096 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 * Complex.I ^ 2 + (165 / 4096 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 * Complex.I ^ 4 + (-165 / 4096 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 * Complex.I ^ 6 + (3941 / 8192 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 2 + (-5633 / 4096 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 4 + (5633 / 4096 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (3453 / 4096 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 6 + (-3453 / 4096 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (3453 / 4096 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-165 / 8192 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 + (165 / 8192 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 * Complex.I ^ 2 + (-165 / 8192 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 * Complex.I ^ 4 + (165 / 8192 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 * Complex.I ^ 6 + (3049 / 4096 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 2 + (2221 / 2048 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 4 + (-2221 / 2048 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-495 / 2048 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 6 + (495 / 2048 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (-495 / 2048 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (43 / 512 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 2 + (-839 / 4096 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 4 + (839 / 4096 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (165 / 2048 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 6 + (-165 / 2048 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (165 / 2048 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-41 / 256 : ℂ) * (σ : ℂ) ^ 7 * (t : ℂ) ^ 2 + (-275 / 2048 : ℂ) * (σ : ℂ) ^ 7 * (t : ℂ) ^ 4 + (275 / 2048 : ℂ) * (σ : ℂ) ^ 7 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-947 / 8192 : ℂ) * (σ : ℂ) ^ 8 * (t : ℂ) ^ 2 + (275 / 8192 : ℂ) * (σ : ℂ) ^ 8 * (t : ℂ) ^ 4 + (-275 / 8192 : ℂ) * (σ : ℂ) ^ 8 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (425 / 4096 : ℂ) * (σ : ℂ) ^ 9 * (t : ℂ) ^ 2 + (-85 / 4096 : ℂ) * (σ : ℂ) ^ 10 * (t : ℂ) ^ 2) * Complex.I_sq

theorem skewHorizonPlateau_conj (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewHorizonPlateau (starRingEnd ℂ s) = starRingEnd ℂ (skewHorizonPlateau s) := by
  have hs' : starRingEnd ℂ s ≠ 0 := by simpa using hs
  have hs3' : starRingEnd ℂ s + 3 ≠ 0 := by
    intro h; apply hs3
    have := congrArg (starRingEnd ℂ) h
    simp only [map_add, map_zero, Complex.conj_conj, map_ofNat] at this
    exact this
  rw [skewHorizonPlateau_eq _ hs' hs3', skewHorizonPlateau_eq s hs hs3]
  simp only [map_div₀, map_add, map_mul, map_pow, map_neg, map_ofNat]

/-- The real part of the plateau is the tilt times its cofactor. -/
theorem skewHorizonPlateau_re_tilt (σ t : ℝ) (hs : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ≠ 0)
    (hs3 : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 ≠ 0) :
    2 * (skewHorizonPlateau ((σ : ℂ) - 2 + (t : ℂ) * Complex.I)).re *
        Complex.normSq (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) * (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3)) =
      (2 * σ - 1) * skewPlateauTiltCofactor σ t := by
  set s : ℂ := (σ : ℂ) - 2 + (t : ℂ) * Complex.I with hsdef
  set w : ℂ := -1 - (σ : ℂ) + (t : ℂ) * Complex.I with hwdef
  have hw : w ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
    simp [hwdef] at h1 h2
    apply hs3; apply Complex.ext <;> simp [hsdef] <;> linarith
  have hw3 : w + 3 ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
    simp [hwdef] at h1 h2
    apply hs; apply Complex.ext <;> simp [hsdef] <;> linarith
  have hconj : starRingEnd ℂ s = -3 - w := by
    apply Complex.ext <;> simp [hsdef, hwdef]
    ring
  have hodd : skewHorizonPlateau w = -(starRingEnd ℂ (skewHorizonPlateau s)) := by
    have hc := skewHorizonPlateau_conj s hs hs3
    rw [hconj, skewHorizonPlateau_reflect w hw hw3] at hc
    rw [← hc]; ring
  have hsum : skewHorizonPlateau s - skewHorizonPlateau w = (2 * (skewHorizonPlateau s).re : ℂ) := by
    rw [hodd, sub_neg_eq_add, Complex.add_conj]; push_cast; ring
  have hsub := skewHorizonPlateau_sub s w hs hs3 hw hw3
  have hsw : s - w = ((2 * σ - 1 : ℝ) : ℂ) := by rw [hsdef, hwdef]; push_cast; ring
  have hden : s * (s + 3) * (w * (w + 3)) = (Complex.normSq (s * (s + 3)) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    have : starRingEnd ℂ (s * (s + 3)) = w * (w + 3) := by
      apply Complex.ext <;> simp [hsdef, hwdef] <;> ring
    rw [this]; ring
  have hcof : skewPlateauCofactor s w = (skewPlateauTiltCofactor σ t : ℂ) := by
    rw [hsdef, hwdef]; exact skewPlateauCofactor_reflected σ t
  rw [hsw, hden, hcof] at hsub
  have hns : (Complex.normSq (s * (s + 3)) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr (mul_ne_zero hs hs3)).ne'
  have key : (2 * (skewHorizonPlateau s).re : ℂ) * (Complex.normSq (s * (s + 3)) : ℂ) = ((2 * σ - 1 : ℝ) : ℂ) * (skewPlateauTiltCofactor σ t : ℂ) := by
    rw [← hsum, hsub]; field_simp
  have key' : (2 * (skewHorizonPlateau s).re * Complex.normSq (s * (s + 3)) : ℝ) = (2 * σ - 1) * skewPlateauTiltCofactor σ t := by
    exact_mod_cast key
  exact key'

/-- Group 1 of the lower-order monomials of the cofactor. -/
noncomputable def skewPlateauTiltPart1 (σ t : ℝ) : ℝ := (-5 / 64 : ℝ) * (σ ^ 0 * t ^ 0) + (-1275 / 8192 : ℝ) * (σ ^ 0 * t ^ 8) + (-9871 / 4096 : ℝ) * (σ ^ 1 * t ^ 4) + (-75 / 512 : ℝ) * (σ ^ 2 * t ^ 0) + (2487 / 8192 : ℝ) * (σ ^ 2 * t ^ 8) + (-3221 / 4096 : ℝ) * (σ ^ 3 * t ^ 4) + (-3941 / 8192 : ℝ) * (σ ^ 4 * t ^ 2) + (-1011 / 4096 : ℝ) * (σ ^ 5 * t ^ 0) + (-647 / 8192 : ℝ) * (σ ^ 6 * t ^ 0) + (513 / 4096 : ℝ) * (σ ^ 7 * t ^ 0) + (947 / 8192 : ℝ) * (σ ^ 8 * t ^ 2) + (-53 / 8192 : ℝ) * (σ ^ 10 * t ^ 0)

theorem skewPlateauTiltPart1_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewPlateauTiltPart1 σ t ≤ (1115 / 2048 : ℝ) * t ^ 10 := by
  unfold skewPlateauTiltPart1
  have hb_0_0 : (-5 / 64 : ℝ) * (σ ^ 0 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-5 / 64 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 0)
    rw [zero_mul] at this
    exact this
  have hb_0_8 : (-1275 / 8192 : ℝ) * (σ ^ 0 * t ^ 8) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1275 / 8192 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 8)
    rw [zero_mul] at this
    exact this
  have hb_1_4 : (-9871 / 4096 : ℝ) * (σ ^ 1 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-9871 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 4)
    rw [zero_mul] at this
    exact this
  have hb_2_0 : (-75 / 512 : ℝ) * (σ ^ 2 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-75 / 512 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 0)
    rw [zero_mul] at this
    exact this
  have hb_2_8 : (2487 / 8192 : ℝ) * (σ ^ 2 * t ^ 8) ≤ (2487 / 8192 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 8 (by norm_num)) (show (0 : ℝ) ≤ (2487 / 8192 : ℝ) by norm_num)
  have hb_3_4 : (-3221 / 4096 : ℝ) * (σ ^ 3 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-3221 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 4)
    rw [zero_mul] at this
    exact this
  have hb_4_2 : (-3941 / 8192 : ℝ) * (σ ^ 4 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-3941 / 8192 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 2)
    rw [zero_mul] at this
    exact this
  have hb_5_0 : (-1011 / 4096 : ℝ) * (σ ^ 5 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1011 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 0)
    rw [zero_mul] at this
    exact this
  have hb_6_0 : (-647 / 8192 : ℝ) * (σ ^ 6 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-647 / 8192 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 0)
    rw [zero_mul] at this
    exact this
  have hb_7_0 : (513 / 4096 : ℝ) * (σ ^ 7 * t ^ 0) ≤ (513 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 7 0 (by norm_num)) (show (0 : ℝ) ≤ (513 / 4096 : ℝ) by norm_num)
  have hb_8_2 : (947 / 8192 : ℝ) * (σ ^ 8 * t ^ 2) ≤ (947 / 8192 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 8 2 (by norm_num)) (show (0 : ℝ) ≤ (947 / 8192 : ℝ) by norm_num)
  have hb_10_0 : (-53 / 8192 : ℝ) * (σ ^ 10 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-53 / 8192 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 10 0)
    rw [zero_mul] at this
    exact this
  linarith

/-- Group 2 of the lower-order monomials of the cofactor. -/
noncomputable def skewPlateauTiltPart2 (σ t : ℝ) : ℝ := (301 / 512 : ℝ) * (σ ^ 0 * t ^ 2) + (-169 / 8192 : ℝ) * (σ ^ 0 * t ^ 10) + (-555 / 4096 : ℝ) * (σ ^ 1 * t ^ 6) + (-129 / 512 : ℝ) * (σ ^ 2 * t ^ 2) + (165 / 4096 : ℝ) * (σ ^ 2 * t ^ 10) + (657 / 512 : ℝ) * (σ ^ 3 * t ^ 6) + (5633 / 4096 : ℝ) * (σ ^ 4 * t ^ 4) + (-3049 / 4096 : ℝ) * (σ ^ 5 * t ^ 2) + (-43 / 512 : ℝ) * (σ ^ 6 * t ^ 2) + (41 / 256 : ℝ) * (σ ^ 7 * t ^ 2) + (-275 / 8192 : ℝ) * (σ ^ 8 * t ^ 4) + (85 / 4096 : ℝ) * (σ ^ 10 * t ^ 2)

theorem skewPlateauTiltPart2_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewPlateauTiltPart2 σ t ≤ (14203 / 4096 : ℝ) * t ^ 10 := by
  unfold skewPlateauTiltPart2
  have hb_0_2 : (301 / 512 : ℝ) * (σ ^ 0 * t ^ 2) ≤ (301 / 512 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 0 2 (by norm_num)) (show (0 : ℝ) ≤ (301 / 512 : ℝ) by norm_num)
  have hb_0_10 : (-169 / 8192 : ℝ) * (σ ^ 0 * t ^ 10) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-169 / 8192 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 10)
    rw [zero_mul] at this
    exact this
  have hb_1_6 : (-555 / 4096 : ℝ) * (σ ^ 1 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-555 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 6)
    rw [zero_mul] at this
    exact this
  have hb_2_2 : (-129 / 512 : ℝ) * (σ ^ 2 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-129 / 512 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 2)
    rw [zero_mul] at this
    exact this
  have hb_2_10 : (165 / 4096 : ℝ) * (σ ^ 2 * t ^ 10) ≤ (165 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 10 (by norm_num)) (show (0 : ℝ) ≤ (165 / 4096 : ℝ) by norm_num)
  have hb_3_6 : (657 / 512 : ℝ) * (σ ^ 3 * t ^ 6) ≤ (657 / 512 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 3 6 (by norm_num)) (show (0 : ℝ) ≤ (657 / 512 : ℝ) by norm_num)
  have hb_4_4 : (5633 / 4096 : ℝ) * (σ ^ 4 * t ^ 4) ≤ (5633 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 4 4 (by norm_num)) (show (0 : ℝ) ≤ (5633 / 4096 : ℝ) by norm_num)
  have hb_5_2 : (-3049 / 4096 : ℝ) * (σ ^ 5 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-3049 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 2)
    rw [zero_mul] at this
    exact this
  have hb_6_2 : (-43 / 512 : ℝ) * (σ ^ 6 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-43 / 512 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 2)
    rw [zero_mul] at this
    exact this
  have hb_7_2 : (41 / 256 : ℝ) * (σ ^ 7 * t ^ 2) ≤ (41 / 256 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 7 2 (by norm_num)) (show (0 : ℝ) ≤ (41 / 256 : ℝ) by norm_num)
  have hb_8_4 : (-275 / 8192 : ℝ) * (σ ^ 8 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-275 / 8192 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 4)
    rw [zero_mul] at this
    exact this
  have hb_10_2 : (85 / 4096 : ℝ) * (σ ^ 10 * t ^ 2) ≤ (85 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 10 2 (by norm_num)) (show (0 : ℝ) ≤ (85 / 4096 : ℝ) by norm_num)
  linarith

/-- Group 3 of the lower-order monomials of the cofactor. -/
noncomputable def skewPlateauTiltPart3 (σ t : ℝ) : ℝ := (-97 / 256 : ℝ) * (σ ^ 0 * t ^ 4) + (21 / 256 : ℝ) * (σ ^ 1 * t ^ 0) + (-1161 / 4096 : ℝ) * (σ ^ 1 * t ^ 8) + (21299 / 8192 : ℝ) * (σ ^ 2 * t ^ 4) + (-1 / 512 : ℝ) * (σ ^ 3 * t ^ 0) + (-165 / 4096 : ℝ) * (σ ^ 3 * t ^ 8) + (-3453 / 4096 : ℝ) * (σ ^ 4 * t ^ 6) + (-2221 / 2048 : ℝ) * (σ ^ 5 * t ^ 4) + (839 / 4096 : ℝ) * (σ ^ 6 * t ^ 4) + (275 / 2048 : ℝ) * (σ ^ 7 * t ^ 4) + (-5 / 4096 : ℝ) * (σ ^ 9 * t ^ 0) + (15 / 4096 : ℝ) * (σ ^ 11 * t ^ 0)

theorem skewPlateauTiltPart3_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewPlateauTiltPart3 σ t ≤ (24779 / 8192 : ℝ) * t ^ 10 := by
  unfold skewPlateauTiltPart3
  have hb_0_4 : (-97 / 256 : ℝ) * (σ ^ 0 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-97 / 256 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 4)
    rw [zero_mul] at this
    exact this
  have hb_1_0 : (21 / 256 : ℝ) * (σ ^ 1 * t ^ 0) ≤ (21 / 256 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 1 0 (by norm_num)) (show (0 : ℝ) ≤ (21 / 256 : ℝ) by norm_num)
  have hb_1_8 : (-1161 / 4096 : ℝ) * (σ ^ 1 * t ^ 8) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1161 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 8)
    rw [zero_mul] at this
    exact this
  have hb_2_4 : (21299 / 8192 : ℝ) * (σ ^ 2 * t ^ 4) ≤ (21299 / 8192 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 4 (by norm_num)) (show (0 : ℝ) ≤ (21299 / 8192 : ℝ) by norm_num)
  have hb_3_0 : (-1 / 512 : ℝ) * (σ ^ 3 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1 / 512 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 0)
    rw [zero_mul] at this
    exact this
  have hb_3_8 : (-165 / 4096 : ℝ) * (σ ^ 3 * t ^ 8) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-165 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 8)
    rw [zero_mul] at this
    exact this
  have hb_4_6 : (-3453 / 4096 : ℝ) * (σ ^ 4 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-3453 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 6)
    rw [zero_mul] at this
    exact this
  have hb_5_4 : (-2221 / 2048 : ℝ) * (σ ^ 5 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2221 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 4)
    rw [zero_mul] at this
    exact this
  have hb_6_4 : (839 / 4096 : ℝ) * (σ ^ 6 * t ^ 4) ≤ (839 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 6 4 (by norm_num)) (show (0 : ℝ) ≤ (839 / 4096 : ℝ) by norm_num)
  have hb_7_4 : (275 / 2048 : ℝ) * (σ ^ 7 * t ^ 4) ≤ (275 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 7 4 (by norm_num)) (show (0 : ℝ) ≤ (275 / 2048 : ℝ) by norm_num)
  have hb_9_0 : (-5 / 4096 : ℝ) * (σ ^ 9 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-5 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 9 0)
    rw [zero_mul] at this
    exact this
  have hb_11_0 : (15 / 4096 : ℝ) * (σ ^ 11 * t ^ 0) ≤ (15 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 11 0 (by norm_num)) (show (0 : ℝ) ≤ (15 / 4096 : ℝ) by norm_num)
  linarith

/-- Group 4 of the lower-order monomials of the cofactor. -/
noncomputable def skewPlateauTiltPart4 (σ t : ℝ) : ℝ := (-6255 / 8192 : ℝ) * (σ ^ 0 * t ^ 6) + (-629 / 512 : ℝ) * (σ ^ 1 * t ^ 2) + (-165 / 4096 : ℝ) * (σ ^ 1 * t ^ 10) + (-477 / 1024 : ℝ) * (σ ^ 2 * t ^ 6) + (5319 / 2048 : ℝ) * (σ ^ 3 * t ^ 2) + (149 / 512 : ℝ) * (σ ^ 4 * t ^ 0) + (165 / 8192 : ℝ) * (σ ^ 4 * t ^ 8) + (495 / 2048 : ℝ) * (σ ^ 5 * t ^ 6) + (-165 / 2048 : ℝ) * (σ ^ 6 * t ^ 6) + (-159 / 8192 : ℝ) * (σ ^ 8 * t ^ 0) + (-425 / 4096 : ℝ) * (σ ^ 9 * t ^ 2) + (-5 / 8192 : ℝ) * (σ ^ 12 * t ^ 0)

theorem skewPlateauTiltPart4_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewPlateauTiltPart4 σ t ≤ (25805 / 8192 : ℝ) * t ^ 10 := by
  unfold skewPlateauTiltPart4
  have hb_0_6 : (-6255 / 8192 : ℝ) * (σ ^ 0 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-6255 / 8192 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 6)
    rw [zero_mul] at this
    exact this
  have hb_1_2 : (-629 / 512 : ℝ) * (σ ^ 1 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-629 / 512 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 2)
    rw [zero_mul] at this
    exact this
  have hb_1_10 : (-165 / 4096 : ℝ) * (σ ^ 1 * t ^ 10) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-165 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 10)
    rw [zero_mul] at this
    exact this
  have hb_2_6 : (-477 / 1024 : ℝ) * (σ ^ 2 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-477 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 6)
    rw [zero_mul] at this
    exact this
  have hb_3_2 : (5319 / 2048 : ℝ) * (σ ^ 3 * t ^ 2) ≤ (5319 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 3 2 (by norm_num)) (show (0 : ℝ) ≤ (5319 / 2048 : ℝ) by norm_num)
  have hb_4_0 : (149 / 512 : ℝ) * (σ ^ 4 * t ^ 0) ≤ (149 / 512 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 4 0 (by norm_num)) (show (0 : ℝ) ≤ (149 / 512 : ℝ) by norm_num)
  have hb_4_8 : (165 / 8192 : ℝ) * (σ ^ 4 * t ^ 8) ≤ (165 / 8192 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 4 8 (by norm_num)) (show (0 : ℝ) ≤ (165 / 8192 : ℝ) by norm_num)
  have hb_5_6 : (495 / 2048 : ℝ) * (σ ^ 5 * t ^ 6) ≤ (495 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 5 6 (by norm_num)) (show (0 : ℝ) ≤ (495 / 2048 : ℝ) by norm_num)
  have hb_6_6 : (-165 / 2048 : ℝ) * (σ ^ 6 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-165 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 6)
    rw [zero_mul] at this
    exact this
  have hb_8_0 : (-159 / 8192 : ℝ) * (σ ^ 8 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-159 / 8192 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 0)
    rw [zero_mul] at this
    exact this
  have hb_9_2 : (-425 / 4096 : ℝ) * (σ ^ 9 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-425 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 9 2)
    rw [zero_mul] at this
    exact this
  have hb_12_0 : (-5 / 8192 : ℝ) * (σ ^ 12 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-5 / 8192 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 12 0)
    rw [zero_mul] at this
    exact this
  linarith

theorem skewPlateauTiltCofactor_split (σ t : ℝ) :
    skewPlateauTiltCofactor σ t = ((-45 / 8192 : ℝ)) * t ^ 12 + skewPlateauTiltPart1 σ t + skewPlateauTiltPart2 σ t + skewPlateauTiltPart3 σ t + skewPlateauTiltPart4 σ t := by
  unfold skewPlateauTiltCofactor skewPlateauTiltPart1 skewPlateauTiltPart2 skewPlateauTiltPart3 skewPlateauTiltPart4
  ring

/-- On the strip and above height 44 the plateau's cofactor is negative. -/
theorem skewPlateauTiltCofactor_neg (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (44 : ℝ) ≤ t) : skewPlateauTiltCofactor σ t < 0 := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  rw [skewPlateauTiltCofactor_split]
  have p1 := skewPlateauTiltPart1_le σ t h0 h1 ht1
  have p2 := skewPlateauTiltPart2_le σ t h0 h1 ht1
  have p3 := skewPlateauTiltPart3_le σ t h0 h1 ht1
  have p4 := skewPlateauTiltPart4_le σ t h0 h1 ht1
  have hbig : (41725 / 4096 : ℝ) * t ^ 10 < ((45 / 8192 : ℝ)) * t ^ 12 := by
    have : t ^ 12 = t ^ 10 * t ^ 2 := by ring
    rw [this]
    have h10 : 0 < t ^ 10 := pow_pos (by linarith) 10
    have hsq : (44 : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith
    nlinarith
  linarith

/-- Above height 44 the real part of the horizon plateau vanishes exactly on the critical line. -/
theorem skewHorizonPlateau_re_eq_zero_iff (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (44 : ℝ) ≤ t) :
    (skewHorizonPlateau ((σ : ℂ) - 2 + (t : ℂ) * Complex.I)).re = 0 ↔ σ = 1 / 2 := by
  have hs : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hs3 : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have key := skewHorizonPlateau_re_tilt σ t hs hs3
  have hpos : 0 < Complex.normSq (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) * (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3)) :=
    Complex.normSq_pos.mpr (mul_ne_zero hs hs3)
  have hneg := skewPlateauTiltCofactor_neg σ t h0 h1 ht
  constructor
  · intro hre
    rw [hre] at key
    have : (2 * σ - 1) * skewPlateauTiltCofactor σ t = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hneg.ne
  · intro hσ
    subst hσ
    have : 2 * (skewHorizonPlateau (((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I)).re * Complex.normSq ((((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I) * ((((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I) + 3)) = 0 := by
      rw [key]; ring
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hpos.ne'

/-- Difference-quotient cofactor of the flux (a polynomial). -/
noncomputable def skewFluxCofactor (s w : ℂ) : ℂ := (585 / 512 : ℂ) + (2151 / 1024 : ℂ) * w + (12331 / 4096 : ℂ) * w ^ 2 + (22785 / 8192 : ℂ) * w ^ 3 + (3185 / 2048 : ℂ) * w ^ 4 + (273 / 512 : ℂ) * w ^ 5 + (239 / 2048 : ℂ) * w ^ 6 + (135 / 8192 : ℂ) * w ^ 7 + (5 / 4096 : ℂ) * w ^ 8 + (2151 / 1024 : ℂ) * s + (12331 / 4096 : ℂ) * s * w + (22785 / 8192 : ℂ) * s * w ^ 2 + (3185 / 2048 : ℂ) * s * w ^ 3 + (273 / 512 : ℂ) * s * w ^ 4 + (239 / 2048 : ℂ) * s * w ^ 5 + (135 / 8192 : ℂ) * s * w ^ 6 + (5 / 4096 : ℂ) * s * w ^ 7 + (12331 / 4096 : ℂ) * s ^ 2 + (22785 / 8192 : ℂ) * s ^ 2 * w + (3185 / 2048 : ℂ) * s ^ 2 * w ^ 2 + (273 / 512 : ℂ) * s ^ 2 * w ^ 3 + (239 / 2048 : ℂ) * s ^ 2 * w ^ 4 + (135 / 8192 : ℂ) * s ^ 2 * w ^ 5 + (5 / 4096 : ℂ) * s ^ 2 * w ^ 6 + (22785 / 8192 : ℂ) * s ^ 3 + (3185 / 2048 : ℂ) * s ^ 3 * w + (273 / 512 : ℂ) * s ^ 3 * w ^ 2 + (239 / 2048 : ℂ) * s ^ 3 * w ^ 3 + (135 / 8192 : ℂ) * s ^ 3 * w ^ 4 + (5 / 4096 : ℂ) * s ^ 3 * w ^ 5 + (3185 / 2048 : ℂ) * s ^ 4 + (273 / 512 : ℂ) * s ^ 4 * w + (239 / 2048 : ℂ) * s ^ 4 * w ^ 2 + (135 / 8192 : ℂ) * s ^ 4 * w ^ 3 + (5 / 4096 : ℂ) * s ^ 4 * w ^ 4 + (273 / 512 : ℂ) * s ^ 5 + (239 / 2048 : ℂ) * s ^ 5 * w + (135 / 8192 : ℂ) * s ^ 5 * w ^ 2 + (5 / 4096 : ℂ) * s ^ 5 * w ^ 3 + (239 / 2048 : ℂ) * s ^ 6 + (135 / 8192 : ℂ) * s ^ 6 * w + (5 / 4096 : ℂ) * s ^ 6 * w ^ 2 + (135 / 8192 : ℂ) * s ^ 7 + (5 / 4096 : ℂ) * s ^ 7 * w + (5 / 4096 : ℂ) * s ^ 8

theorem skewHorizonFlux_sub (s w : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hw : w ≠ 0) (hw3 : w + 3 ≠ 0) :
    skewHorizonFlux s - skewHorizonFlux w = (s - w) * skewFluxCofactor s w := by
  rw [skewHorizonFlux_eq s hs hs3, skewHorizonFlux_eq w hw hw3]
  unfold skewFluxCofactor
  ring

/-- The flux's cofactor at the reflected pair, as a real polynomial. -/
noncomputable def skewFluxTiltCofactor (σ t : ℝ) : ℝ := (7 / 128 : ℝ) + (-349 / 1024 : ℝ) * t ^ 2 + (-665 / 4096 : ℝ) * t ^ 4 + (-77 / 512 : ℝ) * t ^ 6 + (45 / 4096 : ℝ) * t ^ 8 + (-67 / 512 : ℝ) * σ + (-943 / 2048 : ℝ) * σ * t ^ 2 + (-1435 / 2048 : ℝ) * σ * t ^ 4 + (105 / 1024 : ℝ) * σ * t ^ 6 + (81 / 1024 : ℝ) * σ ^ 2 + (109 / 2048 : ℝ) * σ ^ 2 * t ^ 2 + (875 / 1024 : ℝ) * σ ^ 2 * t ^ 4 + (-105 / 1024 : ℝ) * σ ^ 2 * t ^ 6 + (173 / 2048 : ℝ) * σ ^ 3 + (879 / 1024 : ℝ) * σ ^ 3 * t ^ 2 + (-315 / 1024 : ℝ) * σ ^ 3 * t ^ 4 + (27 / 4096 : ℝ) * σ ^ 4 + (-69 / 128 : ℝ) * σ ^ 4 * t ^ 2 + (315 / 2048 : ℝ) * σ ^ 4 * t ^ 4 + (-127 / 2048 : ℝ) * σ ^ 5 + (135 / 1024 : ℝ) * σ ^ 5 * t ^ 2 + (27 / 1024 : ℝ) * σ ^ 6 + (-45 / 1024 : ℝ) * σ ^ 6 * t ^ 2 + (-5 / 1024 : ℝ) * σ ^ 7 + (5 / 4096 : ℝ) * σ ^ 8

theorem skewFluxCofactor_reflected (σ t : ℝ) :
    skewFluxCofactor ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) (-1 - (σ : ℂ) + (t : ℂ) * Complex.I) = (skewFluxTiltCofactor σ t : ℂ) := by
  unfold skewFluxCofactor skewFluxTiltCofactor
  push_cast
  linear_combination ((349 / 1024 : ℂ) * (t : ℂ) ^ 2 + (665 / 4096 : ℂ) * (t : ℂ) ^ 4 + (-665 / 4096 : ℂ) * (t : ℂ) ^ 4 * Complex.I ^ 2 + (77 / 512 : ℂ) * (t : ℂ) ^ 6 + (-77 / 512 : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 2 + (77 / 512 : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-45 / 4096 : ℂ) * (t : ℂ) ^ 8 + (45 / 4096 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 2 + (-45 / 4096 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 4 + (45 / 4096 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 6 + (943 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 2 + (1435 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 4 + (-1435 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-105 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 + (105 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 2 + (-105 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-109 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 2 + (-875 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 4 + (875 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (105 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 + (-105 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (105 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-879 / 1024 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 2 + (315 / 1024 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 4 + (-315 / 1024 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (69 / 128 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 2 + (-315 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 4 + (315 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-135 / 1024 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 2 + (45 / 1024 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 2) * Complex.I_sq

theorem skewHorizonFlux_conj (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewHorizonFlux (starRingEnd ℂ s) = starRingEnd ℂ (skewHorizonFlux s) := by
  have hs' : starRingEnd ℂ s ≠ 0 := by simpa using hs
  have hs3' : starRingEnd ℂ s + 3 ≠ 0 := by
    intro h; apply hs3
    have := congrArg (starRingEnd ℂ) h
    simp only [map_add, map_zero, Complex.conj_conj, map_ofNat] at this
    exact this
  rw [skewHorizonFlux_eq _ hs' hs3', skewHorizonFlux_eq s hs hs3]
  simp only [map_div₀, map_add, map_mul, map_pow, map_ofNat]

/-- The real part of the flux is the tilt times its cofactor. -/
theorem skewHorizonFlux_re_tilt (σ t : ℝ) (hs : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ≠ 0)
    (hs3 : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 ≠ 0) :
    2 * (skewHorizonFlux ((σ : ℂ) - 2 + (t : ℂ) * Complex.I)).re = (2 * σ - 1) * skewFluxTiltCofactor σ t := by
  set s : ℂ := (σ : ℂ) - 2 + (t : ℂ) * Complex.I with hsdef
  set w : ℂ := -1 - (σ : ℂ) + (t : ℂ) * Complex.I with hwdef
  have hw : w ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
    simp [hwdef] at h1 h2
    apply hs3; apply Complex.ext <;> simp [hsdef] <;> linarith
  have hw3 : w + 3 ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
    simp [hwdef] at h1 h2
    apply hs; apply Complex.ext <;> simp [hsdef] <;> linarith
  have hconj : starRingEnd ℂ s = -3 - w := by
    apply Complex.ext <;> simp [hsdef, hwdef]
    ring
  have hodd : skewHorizonFlux w = -(starRingEnd ℂ (skewHorizonFlux s)) := by
    have hc := skewHorizonFlux_conj s hs hs3
    rw [hconj, skewHorizonFlux_reflect w hw hw3] at hc
    rw [← hc]; ring
  have hsum : skewHorizonFlux s - skewHorizonFlux w = (2 * (skewHorizonFlux s).re : ℂ) := by
    rw [hodd, sub_neg_eq_add, Complex.add_conj]; push_cast; ring
  have hsub := skewHorizonFlux_sub s w hs hs3 hw hw3
  have hsw : s - w = ((2 * σ - 1 : ℝ) : ℂ) := by rw [hsdef, hwdef]; push_cast; ring
  have hcof : skewFluxCofactor s w = (skewFluxTiltCofactor σ t : ℂ) := by
    rw [hsdef, hwdef]; exact skewFluxCofactor_reflected σ t
  rw [hsw, hcof] at hsub
  have key : (2 * (skewHorizonFlux s).re : ℂ) = ((2 * σ - 1 : ℝ) : ℂ) * (skewFluxTiltCofactor σ t : ℂ) := by
    rw [← hsum, hsub]
  exact_mod_cast key

theorem skewMonoSix_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) (a b : ℕ) (hb : b ≤ 6) :
    σ ^ a * t ^ b ≤ t ^ 6 := by
  calc σ ^ a * t ^ b ≤ 1 * t ^ 6 :=
        mul_le_mul (pow_le_one₀ h0 h1) (pow_le_pow_right₀ ht1 hb) (pow_nonneg (by linarith) b) zero_le_one
    _ = t ^ 6 := one_mul _

/-- Group 1 of the lower-order monomials of the cofactor. -/
noncomputable def skewFluxTiltPart1 (σ t : ℝ) : ℝ := (7 / 128 : ℝ) * (σ ^ 0 * t ^ 0) + (-67 / 512 : ℝ) * (σ ^ 1 * t ^ 0) + (81 / 1024 : ℝ) * (σ ^ 2 * t ^ 0) + (173 / 2048 : ℝ) * (σ ^ 3 * t ^ 0) + (-69 / 128 : ℝ) * (σ ^ 4 * t ^ 2) + (27 / 1024 : ℝ) * (σ ^ 6 * t ^ 0)

theorem skewFluxTiltPart1_ge (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    (-343 / 512 : ℝ) * t ^ 6 ≤ skewFluxTiltPart1 σ t := by
  unfold skewFluxTiltPart1
  have hb_0_0 : 0 ≤ (7 / 128 : ℝ) * (σ ^ 0 * t ^ 0) :=
    mul_nonneg (show (0 : ℝ) ≤ (7 / 128 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 0)
  have hb_1_0 : (-67 / 512 : ℝ) * t ^ 6 ≤ (-67 / 512 : ℝ) * (σ ^ 1 * t ^ 0) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 1 0 (by norm_num)) (show (-67 / 512 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_2_0 : 0 ≤ (81 / 1024 : ℝ) * (σ ^ 2 * t ^ 0) :=
    mul_nonneg (show (0 : ℝ) ≤ (81 / 1024 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 0)
  have hb_3_0 : 0 ≤ (173 / 2048 : ℝ) * (σ ^ 3 * t ^ 0) :=
    mul_nonneg (show (0 : ℝ) ≤ (173 / 2048 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 0)
  have hb_4_2 : (-69 / 128 : ℝ) * t ^ 6 ≤ (-69 / 128 : ℝ) * (σ ^ 4 * t ^ 2) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 4 2 (by norm_num)) (show (-69 / 128 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_6_0 : 0 ≤ (27 / 1024 : ℝ) * (σ ^ 6 * t ^ 0) :=
    mul_nonneg (show (0 : ℝ) ≤ (27 / 1024 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 0)
  linarith

/-- Group 2 of the lower-order monomials of the cofactor. -/
noncomputable def skewFluxTiltPart2 (σ t : ℝ) : ℝ := (-349 / 1024 : ℝ) * (σ ^ 0 * t ^ 2) + (-943 / 2048 : ℝ) * (σ ^ 1 * t ^ 2) + (109 / 2048 : ℝ) * (σ ^ 2 * t ^ 2) + (879 / 1024 : ℝ) * (σ ^ 3 * t ^ 2) + (315 / 2048 : ℝ) * (σ ^ 4 * t ^ 4) + (-45 / 1024 : ℝ) * (σ ^ 6 * t ^ 2)

theorem skewFluxTiltPart2_ge (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    (-1731 / 2048 : ℝ) * t ^ 6 ≤ skewFluxTiltPart2 σ t := by
  unfold skewFluxTiltPart2
  have hb_0_2 : (-349 / 1024 : ℝ) * t ^ 6 ≤ (-349 / 1024 : ℝ) * (σ ^ 0 * t ^ 2) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 0 2 (by norm_num)) (show (-349 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_1_2 : (-943 / 2048 : ℝ) * t ^ 6 ≤ (-943 / 2048 : ℝ) * (σ ^ 1 * t ^ 2) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 1 2 (by norm_num)) (show (-943 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_2_2 : 0 ≤ (109 / 2048 : ℝ) * (σ ^ 2 * t ^ 2) :=
    mul_nonneg (show (0 : ℝ) ≤ (109 / 2048 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 2)
  have hb_3_2 : 0 ≤ (879 / 1024 : ℝ) * (σ ^ 3 * t ^ 2) :=
    mul_nonneg (show (0 : ℝ) ≤ (879 / 1024 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 2)
  have hb_4_4 : 0 ≤ (315 / 2048 : ℝ) * (σ ^ 4 * t ^ 4) :=
    mul_nonneg (show (0 : ℝ) ≤ (315 / 2048 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 4)
  have hb_6_2 : (-45 / 1024 : ℝ) * t ^ 6 ≤ (-45 / 1024 : ℝ) * (σ ^ 6 * t ^ 2) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 6 2 (by norm_num)) (show (-45 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num)
  linarith

/-- Group 3 of the lower-order monomials of the cofactor. -/
noncomputable def skewFluxTiltPart3 (σ t : ℝ) : ℝ := (-665 / 4096 : ℝ) * (σ ^ 0 * t ^ 4) + (-1435 / 2048 : ℝ) * (σ ^ 1 * t ^ 4) + (875 / 1024 : ℝ) * (σ ^ 2 * t ^ 4) + (-315 / 1024 : ℝ) * (σ ^ 3 * t ^ 4) + (-127 / 2048 : ℝ) * (σ ^ 5 * t ^ 0) + (-5 / 1024 : ℝ) * (σ ^ 7 * t ^ 0)

theorem skewFluxTiltPart3_ge (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    (-5069 / 4096 : ℝ) * t ^ 6 ≤ skewFluxTiltPart3 σ t := by
  unfold skewFluxTiltPart3
  have hb_0_4 : (-665 / 4096 : ℝ) * t ^ 6 ≤ (-665 / 4096 : ℝ) * (σ ^ 0 * t ^ 4) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 0 4 (by norm_num)) (show (-665 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_1_4 : (-1435 / 2048 : ℝ) * t ^ 6 ≤ (-1435 / 2048 : ℝ) * (σ ^ 1 * t ^ 4) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 1 4 (by norm_num)) (show (-1435 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_2_4 : 0 ≤ (875 / 1024 : ℝ) * (σ ^ 2 * t ^ 4) :=
    mul_nonneg (show (0 : ℝ) ≤ (875 / 1024 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 4)
  have hb_3_4 : (-315 / 1024 : ℝ) * t ^ 6 ≤ (-315 / 1024 : ℝ) * (σ ^ 3 * t ^ 4) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 3 4 (by norm_num)) (show (-315 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_5_0 : (-127 / 2048 : ℝ) * t ^ 6 ≤ (-127 / 2048 : ℝ) * (σ ^ 5 * t ^ 0) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 5 0 (by norm_num)) (show (-127 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_7_0 : (-5 / 1024 : ℝ) * t ^ 6 ≤ (-5 / 1024 : ℝ) * (σ ^ 7 * t ^ 0) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 7 0 (by norm_num)) (show (-5 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num)
  linarith

/-- Group 4 of the lower-order monomials of the cofactor. -/
noncomputable def skewFluxTiltPart4 (σ t : ℝ) : ℝ := (-77 / 512 : ℝ) * (σ ^ 0 * t ^ 6) + (105 / 1024 : ℝ) * (σ ^ 1 * t ^ 6) + (-105 / 1024 : ℝ) * (σ ^ 2 * t ^ 6) + (27 / 4096 : ℝ) * (σ ^ 4 * t ^ 0) + (135 / 1024 : ℝ) * (σ ^ 5 * t ^ 2) + (5 / 4096 : ℝ) * (σ ^ 8 * t ^ 0)

theorem skewFluxTiltPart4_ge (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    (-259 / 1024 : ℝ) * t ^ 6 ≤ skewFluxTiltPart4 σ t := by
  unfold skewFluxTiltPart4
  have hb_0_6 : (-77 / 512 : ℝ) * t ^ 6 ≤ (-77 / 512 : ℝ) * (σ ^ 0 * t ^ 6) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 0 6 (by norm_num)) (show (-77 / 512 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_1_6 : 0 ≤ (105 / 1024 : ℝ) * (σ ^ 1 * t ^ 6) :=
    mul_nonneg (show (0 : ℝ) ≤ (105 / 1024 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 6)
  have hb_2_6 : (-105 / 1024 : ℝ) * t ^ 6 ≤ (-105 / 1024 : ℝ) * (σ ^ 2 * t ^ 6) :=
    mul_le_mul_of_nonpos_left (skewMonoSix_le σ t h0 h1 ht1 2 6 (by norm_num)) (show (-105 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num)
  have hb_4_0 : 0 ≤ (27 / 4096 : ℝ) * (σ ^ 4 * t ^ 0) :=
    mul_nonneg (show (0 : ℝ) ≤ (27 / 4096 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 0)
  have hb_5_2 : 0 ≤ (135 / 1024 : ℝ) * (σ ^ 5 * t ^ 2) :=
    mul_nonneg (show (0 : ℝ) ≤ (135 / 1024 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 2)
  have hb_8_0 : 0 ≤ (5 / 4096 : ℝ) * (σ ^ 8 * t ^ 0) :=
    mul_nonneg (show (0 : ℝ) ≤ (5 / 4096 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 0)
  linarith

theorem skewFluxTiltCofactor_split (σ t : ℝ) :
    skewFluxTiltCofactor σ t = ((45 / 4096 : ℝ)) * t ^ 8 + skewFluxTiltPart1 σ t + skewFluxTiltPart2 σ t + skewFluxTiltPart3 σ t + skewFluxTiltPart4 σ t := by
  unfold skewFluxTiltCofactor skewFluxTiltPart1 skewFluxTiltPart2 skewFluxTiltPart3 skewFluxTiltPart4
  ring

/-- On the strip and above height 17 the flux's cofactor is positive. -/
theorem skewFluxTiltCofactor_pos (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (17 : ℝ) ≤ t) : 0 < skewFluxTiltCofactor σ t := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  rw [skewFluxTiltCofactor_split]
  have p1 := skewFluxTiltPart1_ge σ t h0 h1 ht1
  have p2 := skewFluxTiltPart2_ge σ t h0 h1 ht1
  have p3 := skewFluxTiltPart3_ge σ t h0 h1 ht1
  have p4 := skewFluxTiltPart4_ge σ t h0 h1 ht1
  have hbig : (12311 / 4096 : ℝ) * t ^ 6 < ((45 / 4096 : ℝ)) * t ^ 8 := by
    have : t ^ 8 = t ^ 6 * t ^ 2 := by ring
    rw [this]
    have h6 : 0 < t ^ 6 := pow_pos (by linarith) 6
    have hsq : (17 : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith
    nlinarith
  linarith

/-- Above height 17 the real part of the horizon flux vanishes exactly on the critical line. -/
theorem skewHorizonFlux_re_eq_zero_iff (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (17 : ℝ) ≤ t) :
    (skewHorizonFlux ((σ : ℂ) - 2 + (t : ℂ) * Complex.I)).re = 0 ↔ σ = 1 / 2 := by
  have hs : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hs3 : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have key := skewHorizonFlux_re_tilt σ t hs hs3
  have hpos := skewFluxTiltCofactor_pos σ t h0 h1 ht
  constructor
  · intro hre
    rw [hre] at key
    have : (2 * σ - 1) * skewFluxTiltCofactor σ t = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hpos.ne'
  · intro hσ
    subst hσ
    have : (2 * ((1 / 2 : ℝ)) - 1) * skewFluxTiltCofactor (1 / 2) t = 0 := by ring
    linarith

end RHTower.D4BMScalarStream
