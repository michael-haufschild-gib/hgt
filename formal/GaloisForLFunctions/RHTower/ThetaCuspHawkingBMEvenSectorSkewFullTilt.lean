import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewFinitePart
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewTiltDetection
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewRadialTrace

/-!
# The regularized elementary skew cut and its tilt detection at every cutoff

The radial two-rate density `skewRadDensitySS` is `N(r)/(r⁷ s(s+3))` with `N` even, so in `u = 1/r` it
is the Laurent polynomial `skewRadLaurent` (`skewRadDensitySS_substitution`); with `u = (1−z)^{1/2}`
its `z³` Taylor coefficient at the horizon — the Hadamard finite part of the dressed flux
`z^{−3}·r²·(radial current)` at the horizon end, the boundary end contributing none — is the
rational function `skewRadHorizonFP` (`skewRadHorizonFP_eq`). The finite part of the elementary
skew cut is `skewFinitePart = −3·(rational part of the bulk finite part) − ½·skewRadHorizonFP`
(`skewFinitePart_eq`), odd under the branch reflection (`skewFinitePart_reflect`), and the
regularized cut with horizon cutoff `z = ε` is
`skewCut s ε = skewFinitePart s + skewLogCoeff s · log(4/ε)`, equal to `−3·(bulk finite part
plus its logarithmic divergence) − ½·skewRadHorizonFP` (`skewCut_eq_regularized`). Its real part is the
tilt times `skewTiltCofactorQ + log(4/ε)·skewTiltCofactor` (`skewCut_re_tilt`); the two cofactors have
leading terms `(675/4096)t¹²` and `−(675/2048)t¹²`, so for every cutoff `ε ≤ 4/e` and height
`t ≥ 58` the real part vanishes exactly on the critical line (`skewCut_re_eq_zero_iff`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

/-- The radial density in the boundary variable `u = 1/r`. -/
noncomputable def skewRadLaurent (s u : ℂ) : ℂ := (((-135 / 16 : ℂ) * s ^ 2 + (-765 / 32 : ℂ) * s ^ 3 + (-435 / 64 : ℂ) * s ^ 4 + (6805 / 128 : ℂ) * s ^ 5 + (11865 / 128 : ℂ) * s ^ 6 + (2375 / 32 : ℂ) * s ^ 7 + (135 / 4 : ℂ) * s ^ 8 + (1145 / 128 : ℂ) * s ^ 9 + (165 / 128 : ℂ) * s ^ 10 + (5 / 64 : ℂ) * s ^ 11) / (s * (s + 3))) * u ^ 7 + (((675 / 8 : ℂ) * s ^ 2 + (711 / 2 : ℂ) * s ^ 3 + (21021 / 32 : ℂ) * s ^ 4 + (10549 / 16 : ℂ) * s ^ 5 + (6111 / 16 : ℂ) * s ^ 6 + (255 / 2 : ℂ) * s ^ 7 + (729 / 32 : ℂ) * s ^ 8 + (27 / 16 : ℂ) * s ^ 9) / (s * (s + 3))) * u ^ 5 + (((-21 / 2 : ℂ) + (-25 : ℂ) * s + (-423 / 16 : ℂ) * s ^ 2 + (-245 / 32 : ℂ) * s ^ 3 + (255 / 32 : ℂ) * s ^ 4 + (223 / 32 : ℂ) * s ^ 5 + (63 / 32 : ℂ) * s ^ 6 + (3 / 16 : ℂ) * s ^ 7) / (s * (s + 3))) * u ^ 3 + (((6 : ℂ) + (233 / 2 : ℂ) * s + (1683 / 8 : ℂ) * s ^ 2 + (311 / 2 : ℂ) * s ^ 3 + (435 / 8 : ℂ) * s ^ 4 + (29 / 4 : ℂ) * s ^ 5) / (s * (s + 3))) * u + (((9 / 2 : ℂ) + (-21 / 2 : ℂ) * s + (-27 / 2 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 3) / (s * (s + 3))) * u⁻¹

theorem skewRadDensitySS_substitution (s u : ℂ) (hu : u ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewRadDensitySS s (1 / u) = skewRadLaurent s u := by
  unfold skewRadDensitySS skewRadLaurent
  field_simp
  ring

/-- Horizon finite part of the dressed radial flux: the `z³` coefficient of `skewRadLaurent s ((1−z)^{1/2})`. -/
noncomputable def skewRadHorizonFP (s : ℂ) : ℂ := (((3 / 8 : ℂ) + (-97 / 8 : ℂ) * s + (-3447 / 128 : ℂ) * s ^ 2 + (-17903 / 256 : ℂ) * s ^ 3 + (-197955 / 1024 : ℂ) * s ^ 4 + (-660171 / 2048 : ℂ) * s ^ 5 + (-659463 / 2048 : ℂ) * s ^ 6 + (-103519 / 512 : ℂ) * s ^ 7 + (-41445 / 512 : ℂ) * s ^ 8 + (-41155 / 2048 : ℂ) * s ^ 9 + (-5775 / 2048 : ℂ) * s ^ 10 + (-175 / 1024 : ℂ) * s ^ 11) / (s * (s + 3)))

theorem skewRadHorizonFP_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    (((-135 / 16 : ℂ) * s ^ 2 + (-765 / 32 : ℂ) * s ^ 3 + (-435 / 64 : ℂ) * s ^ 4 + (6805 / 128 : ℂ) * s ^ 5 + (11865 / 128 : ℂ) * s ^ 6 + (2375 / 32 : ℂ) * s ^ 7 + (135 / 4 : ℂ) * s ^ 8 + (1145 / 128 : ℂ) * s ^ 9 + (165 / 128 : ℂ) * s ^ 10 + (5 / 64 : ℂ) * s ^ 11) / (s * (s + 3))) * (-35 / 16 : ℂ) + (((675 / 8 : ℂ) * s ^ 2 + (711 / 2 : ℂ) * s ^ 3 + (21021 / 32 : ℂ) * s ^ 4 + (10549 / 16 : ℂ) * s ^ 5 + (6111 / 16 : ℂ) * s ^ 6 + (255 / 2 : ℂ) * s ^ 7 + (729 / 32 : ℂ) * s ^ 8 + (27 / 16 : ℂ) * s ^ 9) / (s * (s + 3))) * (-5 / 16 : ℂ) + (((-21 / 2 : ℂ) + (-25 : ℂ) * s + (-423 / 16 : ℂ) * s ^ 2 + (-245 / 32 : ℂ) * s ^ 3 + (255 / 32 : ℂ) * s ^ 4 + (223 / 32 : ℂ) * s ^ 5 + (63 / 32 : ℂ) * s ^ 6 + (3 / 16 : ℂ) * s ^ 7) / (s * (s + 3))) * (1 / 16 : ℂ) + (((6 : ℂ) + (233 / 2 : ℂ) * s + (1683 / 8 : ℂ) * s ^ 2 + (311 / 2 : ℂ) * s ^ 3 + (435 / 8 : ℂ) * s ^ 4 + (29 / 4 : ℂ) * s ^ 5) / (s * (s + 3))) * (-1 / 16 : ℂ) + (((9 / 2 : ℂ) + (-21 / 2 : ℂ) * s + (-27 / 2 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 3) / (s * (s + 3))) * (5 / 16 : ℂ) = skewRadHorizonFP s := by
  unfold skewRadHorizonFP
  field_simp
  ring

/-- Rational part of the bulk finite part. -/
noncomputable def skewBulkRational (s : ℂ) : ℂ := (((-219 / 64 : ℂ) + (1157 / 128 : ℂ) * s + (2457 / 128 : ℂ) * s ^ 2 + (9785 / 256 : ℂ) * s ^ 3 + (304129 / 4096 : ℂ) * s ^ 4 + (2203847 / 24576 : ℂ) * s ^ 5 + (564529 / 8192 : ℂ) * s ^ 6 + (216647 / 6144 : ℂ) * s ^ 7 + (24903 / 2048 : ℂ) * s ^ 8 + (67511 / 24576 : ℂ) * s ^ 9 + (3025 / 8192 : ℂ) * s ^ 10 + (275 / 12288 : ℂ) * s ^ 11) / (s * (s + 3)))

theorem skewBulkFinitePart_eq' (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewBulkFinitePart s = skewBulkRational s + (skewPfB1 s + skewPfD1 s) * ((Real.log 2 : ℝ) : ℂ) := by
  rw [skewBulkFinitePart_eq s hs hs3]
  unfold skewBulkRational
  field_simp

/-- Finite part of the elementary skew cut (cutoff scale `4` absorbed into the logarithm). -/
noncomputable def skewFinitePart (s : ℂ) : ℂ := (-3) * skewBulkRational s - (1 / 2) * skewRadHorizonFP s

theorem skewFinitePart_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewFinitePart s = (((645 / 64 : ℂ) + (-2695 / 128 : ℂ) * s + (-11295 / 256 : ℂ) * s ^ 2 + (-40807 / 512 : ℂ) * s ^ 3 + (-516477 / 4096 : ℂ) * s ^ 4 + (-883505 / 8192 : ℂ) * s ^ 5 + (-374661 / 8192 : ℂ) * s ^ 6 + (-9609 / 2048 : ℂ) * s ^ 7 + (8181 / 2048 : ℂ) * s ^ 8 + (14799 / 8192 : ℂ) * s ^ 9 + (2475 / 8192 : ℂ) * s ^ 10 + (75 / 4096 : ℂ) * s ^ 11) / (s * (s + 3))) := by
  unfold skewFinitePart skewBulkRational skewRadHorizonFP
  field_simp
  ring

theorem skewFinitePart_reflect (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewFinitePart (-3 - s) = -skewFinitePart s := by
  have hs' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  have hs3' : (-3 : ℂ) - s + 3 ≠ 0 := by intro h; apply hs; linear_combination -h
  rw [skewFinitePart_eq _ hs' hs3', skewFinitePart_eq s hs hs3]
  field_simp
  ring

/-- The regularized elementary skew cut with horizon cutoff `z = ε`. -/
noncomputable def skewCut (s : ℂ) (ε : ℝ) : ℂ :=
  skewFinitePart s + skewLogCoeff s * ((Real.log (4 / ε) : ℝ) : ℂ)

/-- The regularized cut is `−3` times the bulk finite part with its logarithmic divergence restored,
minus one half of the radial flux's horizon finite part. -/
theorem skewCut_eq_regularized (s : ℂ) (ε : ℝ) (hε : 0 < ε) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewCut s ε = (-3) * (skewBulkFinitePart s + (-skewPfB1 s) * ((Real.log ε : ℝ) : ℂ)) - (1 / 2) * skewRadHorizonFP s := by
  unfold skewCut skewFinitePart
  rw [skewBulkFinitePart_eq' s hs hs3]
  obtain ⟨h1, h2⟩ := skewBulk_log_coefficients s hs hs3
  have hlog : Real.log (4 / ε) = 2 * Real.log 2 - Real.log ε := by
    rw [Real.log_div (by norm_num) hε.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [hlog]
  push_cast
  linear_combination (-(Real.log ε : ℂ)) * h1 + (3 * (Real.log 2 : ℂ)) * h2

/-- The difference-quotient cofactor of the finite part. -/
noncomputable def skewFPCofactor (s w : ℂ) : ℂ := (-1935 / 64 : ℂ) + (-645 / 64 : ℂ) * w + (-645 / 64 : ℂ) * s + (-28495 / 256 : ℂ) * s * w + (-122421 / 512 : ℂ) * s * w ^ 2 + (-1549431 / 4096 : ℂ) * s * w ^ 3 + (-2650515 / 8192 : ℂ) * s * w ^ 4 + (-1123983 / 8192 : ℂ) * s * w ^ 5 + (-28827 / 2048 : ℂ) * s * w ^ 6 + (24543 / 2048 : ℂ) * s * w ^ 7 + (44397 / 8192 : ℂ) * s * w ^ 8 + (7425 / 8192 : ℂ) * s * w ^ 9 + (225 / 4096 : ℂ) * s * w ^ 10 + (-122421 / 512 : ℂ) * s ^ 2 * w + (-1875887 / 4096 : ℂ) * s ^ 2 * w ^ 2 + (-3683469 / 8192 : ℂ) * s ^ 2 * w ^ 3 + (-31367 / 128 : ℂ) * s ^ 2 * w ^ 4 + (-489969 / 8192 : ℂ) * s ^ 2 * w ^ 5 + (7467 / 1024 : ℂ) * s ^ 2 * w ^ 6 + (77121 / 8192 : ℂ) * s ^ 2 * w ^ 7 + (1389 / 512 : ℂ) * s ^ 2 * w ^ 8 + (2925 / 8192 : ℂ) * s ^ 2 * w ^ 9 + (75 / 4096 : ℂ) * s ^ 2 * w ^ 10 + (-1549431 / 4096 : ℂ) * s ^ 3 * w + (-3683469 / 8192 : ℂ) * s ^ 3 * w ^ 2 + (-31367 / 128 : ℂ) * s ^ 3 * w ^ 3 + (-489969 / 8192 : ℂ) * s ^ 3 * w ^ 4 + (7467 / 1024 : ℂ) * s ^ 3 * w ^ 5 + (77121 / 8192 : ℂ) * s ^ 3 * w ^ 6 + (1389 / 512 : ℂ) * s ^ 3 * w ^ 7 + (2925 / 8192 : ℂ) * s ^ 3 * w ^ 8 + (75 / 4096 : ℂ) * s ^ 3 * w ^ 9 + (-2650515 / 8192 : ℂ) * s ^ 4 * w + (-31367 / 128 : ℂ) * s ^ 4 * w ^ 2 + (-489969 / 8192 : ℂ) * s ^ 4 * w ^ 3 + (7467 / 1024 : ℂ) * s ^ 4 * w ^ 4 + (77121 / 8192 : ℂ) * s ^ 4 * w ^ 5 + (1389 / 512 : ℂ) * s ^ 4 * w ^ 6 + (2925 / 8192 : ℂ) * s ^ 4 * w ^ 7 + (75 / 4096 : ℂ) * s ^ 4 * w ^ 8 + (-1123983 / 8192 : ℂ) * s ^ 5 * w + (-489969 / 8192 : ℂ) * s ^ 5 * w ^ 2 + (7467 / 1024 : ℂ) * s ^ 5 * w ^ 3 + (77121 / 8192 : ℂ) * s ^ 5 * w ^ 4 + (1389 / 512 : ℂ) * s ^ 5 * w ^ 5 + (2925 / 8192 : ℂ) * s ^ 5 * w ^ 6 + (75 / 4096 : ℂ) * s ^ 5 * w ^ 7 + (-28827 / 2048 : ℂ) * s ^ 6 * w + (7467 / 1024 : ℂ) * s ^ 6 * w ^ 2 + (77121 / 8192 : ℂ) * s ^ 6 * w ^ 3 + (1389 / 512 : ℂ) * s ^ 6 * w ^ 4 + (2925 / 8192 : ℂ) * s ^ 6 * w ^ 5 + (75 / 4096 : ℂ) * s ^ 6 * w ^ 6 + (24543 / 2048 : ℂ) * s ^ 7 * w + (77121 / 8192 : ℂ) * s ^ 7 * w ^ 2 + (1389 / 512 : ℂ) * s ^ 7 * w ^ 3 + (2925 / 8192 : ℂ) * s ^ 7 * w ^ 4 + (75 / 4096 : ℂ) * s ^ 7 * w ^ 5 + (44397 / 8192 : ℂ) * s ^ 8 * w + (1389 / 512 : ℂ) * s ^ 8 * w ^ 2 + (2925 / 8192 : ℂ) * s ^ 8 * w ^ 3 + (75 / 4096 : ℂ) * s ^ 8 * w ^ 4 + (7425 / 8192 : ℂ) * s ^ 9 * w + (2925 / 8192 : ℂ) * s ^ 9 * w ^ 2 + (75 / 4096 : ℂ) * s ^ 9 * w ^ 3 + (225 / 4096 : ℂ) * s ^ 10 * w + (75 / 4096 : ℂ) * s ^ 10 * w ^ 2

theorem skewFinitePart_sub (s w : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hw : w ≠ 0) (hw3 : w + 3 ≠ 0) :
    skewFinitePart s - skewFinitePart w = (s - w) * skewFPCofactor s w / (s * (s + 3) * (w * (w + 3))) := by
  rw [skewFinitePart_eq s hs hs3, skewFinitePart_eq w hw hw3]
  unfold skewFPCofactor
  field_simp
  ring

/-- The finite part's cofactor at the reflected pair, as a real polynomial. -/
noncomputable def skewTiltCofactorQ (σ t : ℝ) : ℝ := (-1267 / 32 : ℝ) + (-8183 / 256 : ℝ) * t ^ 2 + (-531 / 64 : ℝ) * t ^ 4 + (64857 / 4096 : ℝ) * t ^ 6 + (60645 / 4096 : ℝ) * t ^ 8 + (13791 / 4096 : ℝ) * t ^ 10 + (675 / 4096 : ℝ) * t ^ 12 + (-4347 / 128 : ℝ) * σ + (7229 / 256 : ℝ) * σ * t ^ 2 + (185381 / 2048 : ℝ) * σ * t ^ 4 + (177165 / 2048 : ℝ) * σ * t ^ 6 + (34299 / 2048 : ℝ) * σ * t ^ 8 + (2475 / 2048 : ℝ) * σ * t ^ 10 + (7441 / 256 : ℝ) * σ ^ 2 + (7649 / 256 : ℝ) * σ ^ 2 * t ^ 2 + (20267 / 4096 : ℝ) * σ ^ 2 * t ^ 4 + (-43497 / 512 : ℝ) * σ ^ 2 * t ^ 6 + (-71073 / 4096 : ℝ) * σ ^ 2 * t ^ 8 + (-2475 / 2048 : ℝ) * σ ^ 2 * t ^ 10 + (3545 / 256 : ℝ) * σ ^ 3 + (-75965 / 1024 : ℝ) * σ ^ 3 * t ^ 2 + (-370893 / 2048 : ℝ) * σ ^ 3 * t ^ 4 + (-1413 / 256 : ℝ) * σ ^ 3 * t ^ 6 + (2475 / 2048 : ℝ) * σ ^ 3 * t ^ 8 + (-3767 / 256 : ℝ) * σ ^ 4 + (-236813 / 4096 : ℝ) * σ ^ 4 * t ^ 2 + (137169 / 2048 : ℝ) * σ ^ 4 * t ^ 4 + (18027 / 2048 : ℝ) * σ ^ 4 * t ^ 6 + (-2475 / 4096 : ℝ) * σ ^ 4 * t ^ 8 + (6609 / 2048 : ℝ) * σ ^ 5 + (175935 / 2048 : ℝ) * σ ^ 5 * t ^ 2 + (26079 / 1024 : ℝ) * σ ^ 5 * t ^ 4 + (-7425 / 1024 : ℝ) * σ ^ 5 * t ^ 6 + (31649 / 4096 : ℝ) * σ ^ 6 + (4131 / 256 : ℝ) * σ ^ 6 * t ^ 2 + (-7761 / 2048 : ℝ) * σ ^ 6 * t ^ 4 + (2475 / 1024 : ℝ) * σ ^ 6 * t ^ 6 + (-9831 / 2048 : ℝ) * σ ^ 7 + (-2217 / 64 : ℝ) * σ ^ 7 * t ^ 2 + (-4125 / 1024 : ℝ) * σ ^ 7 * t ^ 4 + (-8607 / 4096 : ℝ) * σ ^ 8 + (16347 / 4096 : ℝ) * σ ^ 8 * t ^ 2 + (4125 / 4096 : ℝ) * σ ^ 8 * t ^ 4 + (4095 / 2048 : ℝ) * σ ^ 9 + (6375 / 2048 : ℝ) * σ ^ 9 * t ^ 2 + (-813 / 4096 : ℝ) * σ ^ 10 + (-1275 / 2048 : ℝ) * σ ^ 10 * t ^ 2 + (-225 / 2048 : ℝ) * σ ^ 11 + (75 / 4096 : ℝ) * σ ^ 12

theorem skewFPCofactor_reflected (σ t : ℝ) :
    skewFPCofactor ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) (-1 - (σ : ℂ) + (t : ℂ) * Complex.I) = (skewTiltCofactorQ σ t : ℂ) := by
  unfold skewFPCofactor skewTiltCofactorQ
  push_cast
  linear_combination ((8183 / 256 : ℂ) * (t : ℂ) ^ 2 + (531 / 64 : ℂ) * (t : ℂ) ^ 4 + (-531 / 64 : ℂ) * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-64857 / 4096 : ℂ) * (t : ℂ) ^ 6 + (64857 / 4096 : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 2 + (-64857 / 4096 : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-60645 / 4096 : ℂ) * (t : ℂ) ^ 8 + (60645 / 4096 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 2 + (-60645 / 4096 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 4 + (60645 / 4096 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 6 + (-13791 / 4096 : ℂ) * (t : ℂ) ^ 10 + (13791 / 4096 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 2 + (-13791 / 4096 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 4 + (13791 / 4096 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 6 + (-13791 / 4096 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 8 + (-675 / 4096 : ℂ) * (t : ℂ) ^ 12 + (675 / 4096 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 2 + (-675 / 4096 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 4 + (675 / 4096 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 6 + (-675 / 4096 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 8 + (675 / 4096 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 10 + (-7229 / 256 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 2 + (-185381 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 4 + (185381 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-177165 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 + (177165 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 2 + (-177165 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-34299 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 + (34299 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 2 + (-34299 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 4 + (34299 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 6 + (-2475 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 + (2475 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 2 + (-2475 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 4 + (2475 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 6 + (-2475 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 8 + (-7649 / 256 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 2 + (-20267 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 4 + (20267 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (43497 / 512 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 + (-43497 / 512 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (43497 / 512 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (71073 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 + (-71073 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 * Complex.I ^ 2 + (71073 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 * Complex.I ^ 4 + (-71073 / 4096 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 * Complex.I ^ 6 + (2475 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 + (-2475 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 2 + (2475 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 4 + (-2475 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 6 + (2475 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 8 + (75965 / 1024 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 2 + (370893 / 2048 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 4 + (-370893 / 2048 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (1413 / 256 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 6 + (-1413 / 256 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (1413 / 256 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-2475 / 2048 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 + (2475 / 2048 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 * Complex.I ^ 2 + (-2475 / 2048 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 * Complex.I ^ 4 + (2475 / 2048 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 * Complex.I ^ 6 + (236813 / 4096 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 2 + (-137169 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 4 + (137169 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-18027 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 6 + (18027 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (-18027 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (2475 / 4096 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 + (-2475 / 4096 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 * Complex.I ^ 2 + (2475 / 4096 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 * Complex.I ^ 4 + (-2475 / 4096 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 * Complex.I ^ 6 + (-175935 / 2048 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 2 + (-26079 / 1024 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 4 + (26079 / 1024 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (7425 / 1024 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 6 + (-7425 / 1024 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (7425 / 1024 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-4131 / 256 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 2 + (7761 / 2048 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 4 + (-7761 / 2048 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-2475 / 1024 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 6 + (2475 / 1024 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (-2475 / 1024 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (2217 / 64 : ℂ) * (σ : ℂ) ^ 7 * (t : ℂ) ^ 2 + (4125 / 1024 : ℂ) * (σ : ℂ) ^ 7 * (t : ℂ) ^ 4 + (-4125 / 1024 : ℂ) * (σ : ℂ) ^ 7 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-16347 / 4096 : ℂ) * (σ : ℂ) ^ 8 * (t : ℂ) ^ 2 + (-4125 / 4096 : ℂ) * (σ : ℂ) ^ 8 * (t : ℂ) ^ 4 + (4125 / 4096 : ℂ) * (σ : ℂ) ^ 8 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-6375 / 2048 : ℂ) * (σ : ℂ) ^ 9 * (t : ℂ) ^ 2 + (1275 / 2048 : ℂ) * (σ : ℂ) ^ 10 * (t : ℂ) ^ 2) * Complex.I_sq

theorem skewFinitePart_conj (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewFinitePart (starRingEnd ℂ s) = starRingEnd ℂ (skewFinitePart s) := by
  have hs' : starRingEnd ℂ s ≠ 0 := by simpa using hs
  have hs3' : starRingEnd ℂ s + 3 ≠ 0 := by
    intro h; apply hs3
    have := congrArg (starRingEnd ℂ) h
    simp only [map_add, map_zero, Complex.conj_conj, map_ofNat] at this
    exact this
  rw [skewFinitePart_eq _ hs' hs3', skewFinitePart_eq s hs hs3]
  simp only [map_div₀, map_add, map_mul, map_pow, map_neg, map_ofNat]

/-- The real part of the finite part is the tilt times its cofactor. -/
theorem skewFinitePart_re_tilt (σ t : ℝ) (hs : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ≠ 0)
    (hs3 : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 ≠ 0) :
    2 * (skewFinitePart ((σ : ℂ) - 2 + (t : ℂ) * Complex.I)).re *
        Complex.normSq (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) * (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3)) =
      (2 * σ - 1) * skewTiltCofactorQ σ t := by
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
  have hodd : skewFinitePart w = -(starRingEnd ℂ (skewFinitePart s)) := by
    have hc := skewFinitePart_conj s hs hs3
    rw [hconj, skewFinitePart_reflect w hw hw3] at hc
    rw [← hc]; ring
  have hsum : skewFinitePart s - skewFinitePart w = (2 * (skewFinitePart s).re : ℂ) := by
    rw [hodd, sub_neg_eq_add, Complex.add_conj]; push_cast; ring
  have hsub := skewFinitePart_sub s w hs hs3 hw hw3
  have hsw : s - w = ((2 * σ - 1 : ℝ) : ℂ) := by rw [hsdef, hwdef]; push_cast; ring
  have hden : s * (s + 3) * (w * (w + 3)) = (Complex.normSq (s * (s + 3)) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    have : starRingEnd ℂ (s * (s + 3)) = w * (w + 3) := by
      apply Complex.ext <;> simp [hsdef, hwdef] <;> ring
    rw [this]; ring
  have hcof : skewFPCofactor s w = (skewTiltCofactorQ σ t : ℂ) := by
    rw [hsdef, hwdef]; exact skewFPCofactor_reflected σ t
  rw [hsw, hden, hcof] at hsub
  have hns : (Complex.normSq (s * (s + 3)) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr (mul_ne_zero hs hs3)).ne'
  have key : (2 * (skewFinitePart s).re : ℂ) * (Complex.normSq (s * (s + 3)) : ℂ) = ((2 * σ - 1 : ℝ) : ℂ) * (skewTiltCofactorQ σ t : ℂ) := by
    rw [← hsum, hsub]; field_simp
  have key' : (2 * (skewFinitePart s).re * Complex.normSq (s * (s + 3)) : ℝ) = (2 * σ - 1) * skewTiltCofactorQ σ t := by
    exact_mod_cast key
  exact key'

/-- Group 1 of the lower-order monomials of the summed cofactor. -/
noncomputable def skewTiltSumPart1 (σ t : ℝ) : ℝ := (-325 / 32 : ℝ) * (σ ^ 0 * t ^ 0) + (48795 / 4096 : ℝ) * (σ ^ 0 * t ^ 8) + (91979 / 2048 : ℝ) * (σ ^ 1 * t ^ 4) + (1615 / 256 : ℝ) * (σ ^ 2 * t ^ 0) + (4545 / 4096 : ℝ) * (σ ^ 2 * t ^ 8) + (-377619 / 2048 : ℝ) * (σ ^ 3 * t ^ 4) + (-237587 / 4096 : ℝ) * (σ ^ 4 * t ^ 2) + (-4257 / 2048 : ℝ) * (σ ^ 5 * t ^ 0) + (24575 / 4096 : ℝ) * (σ ^ 6 * t ^ 0) + (-5433 / 2048 : ℝ) * (σ ^ 7 * t ^ 0) + (43845 / 4096 : ℝ) * (σ ^ 8 * t ^ 2) + (-2355 / 4096 : ℝ) * (σ ^ 10 * t ^ 0)

theorem skewTiltSumPart1_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltSumPart1 σ t ≤ (165779 / 2048 : ℝ) * t ^ 10 := by
  unfold skewTiltSumPart1
  have hb_0_0 : (-325 / 32 : ℝ) * (σ ^ 0 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-325 / 32 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 0)
    rw [zero_mul] at this
    exact this
  have hb_0_8 : (48795 / 4096 : ℝ) * (σ ^ 0 * t ^ 8) ≤ (48795 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 0 8 (by norm_num)) (show (0 : ℝ) ≤ (48795 / 4096 : ℝ) by norm_num)
  have hb_1_4 : (91979 / 2048 : ℝ) * (σ ^ 1 * t ^ 4) ≤ (91979 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 1 4 (by norm_num)) (show (0 : ℝ) ≤ (91979 / 2048 : ℝ) by norm_num)
  have hb_2_0 : (1615 / 256 : ℝ) * (σ ^ 2 * t ^ 0) ≤ (1615 / 256 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 0 (by norm_num)) (show (0 : ℝ) ≤ (1615 / 256 : ℝ) by norm_num)
  have hb_2_8 : (4545 / 4096 : ℝ) * (σ ^ 2 * t ^ 8) ≤ (4545 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 8 (by norm_num)) (show (0 : ℝ) ≤ (4545 / 4096 : ℝ) by norm_num)
  have hb_3_4 : (-377619 / 2048 : ℝ) * (σ ^ 3 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-377619 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 4)
    rw [zero_mul] at this
    exact this
  have hb_4_2 : (-237587 / 4096 : ℝ) * (σ ^ 4 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-237587 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 2)
    rw [zero_mul] at this
    exact this
  have hb_5_0 : (-4257 / 2048 : ℝ) * (σ ^ 5 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-4257 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 0)
    rw [zero_mul] at this
    exact this
  have hb_6_0 : (24575 / 4096 : ℝ) * (σ ^ 6 * t ^ 0) ≤ (24575 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 6 0 (by norm_num)) (show (0 : ℝ) ≤ (24575 / 4096 : ℝ) by norm_num)
  have hb_7_0 : (-5433 / 2048 : ℝ) * (σ ^ 7 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-5433 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 7 0)
    rw [zero_mul] at this
    exact this
  have hb_8_2 : (43845 / 4096 : ℝ) * (σ ^ 8 * t ^ 2) ≤ (43845 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 8 2 (by norm_num)) (show (0 : ℝ) ≤ (43845 / 4096 : ℝ) by norm_num)
  have hb_10_0 : (-2355 / 4096 : ℝ) * (σ ^ 10 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2355 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 10 0)
    rw [zero_mul] at this
    exact this
  linarith

/-- Group 2 of the lower-order monomials of the summed cofactor. -/
noncomputable def skewTiltSumPart2 (σ t : ℝ) : ℝ := (-2153 / 256 : ℝ) * (σ ^ 0 * t ^ 2) + (8385 / 4096 : ℝ) * (σ ^ 0 * t ^ 10) + (155475 / 2048 : ℝ) * (σ ^ 1 * t ^ 6) + (9431 / 256 : ℝ) * (σ ^ 2 * t ^ 2) + (2475 / 2048 : ℝ) * (σ ^ 2 * t ^ 10) + (18045 / 256 : ℝ) * (σ ^ 3 * t ^ 6) + (260847 / 2048 : ℝ) * (σ ^ 4 * t ^ 4) + (146913 / 2048 : ℝ) * (σ ^ 5 * t ^ 2) + (-27 / 256 : ℝ) * (σ ^ 6 * t ^ 2) + (-1545 / 64 : ℝ) * (σ ^ 7 * t ^ 2) + (-4125 / 4096 : ℝ) * (σ ^ 8 * t ^ 4) + (1275 / 2048 : ℝ) * (σ ^ 10 * t ^ 2)

theorem skewTiltSumPart2_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltSumPart2 σ t ≤ (1581971 / 4096 : ℝ) * t ^ 10 := by
  unfold skewTiltSumPart2
  have hb_0_2 : (-2153 / 256 : ℝ) * (σ ^ 0 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2153 / 256 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 2)
    rw [zero_mul] at this
    exact this
  have hb_0_10 : (8385 / 4096 : ℝ) * (σ ^ 0 * t ^ 10) ≤ (8385 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 0 10 (by norm_num)) (show (0 : ℝ) ≤ (8385 / 4096 : ℝ) by norm_num)
  have hb_1_6 : (155475 / 2048 : ℝ) * (σ ^ 1 * t ^ 6) ≤ (155475 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 1 6 (by norm_num)) (show (0 : ℝ) ≤ (155475 / 2048 : ℝ) by norm_num)
  have hb_2_2 : (9431 / 256 : ℝ) * (σ ^ 2 * t ^ 2) ≤ (9431 / 256 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 2 (by norm_num)) (show (0 : ℝ) ≤ (9431 / 256 : ℝ) by norm_num)
  have hb_2_10 : (2475 / 2048 : ℝ) * (σ ^ 2 * t ^ 10) ≤ (2475 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 10 (by norm_num)) (show (0 : ℝ) ≤ (2475 / 2048 : ℝ) by norm_num)
  have hb_3_6 : (18045 / 256 : ℝ) * (σ ^ 3 * t ^ 6) ≤ (18045 / 256 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 3 6 (by norm_num)) (show (0 : ℝ) ≤ (18045 / 256 : ℝ) by norm_num)
  have hb_4_4 : (260847 / 2048 : ℝ) * (σ ^ 4 * t ^ 4) ≤ (260847 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 4 4 (by norm_num)) (show (0 : ℝ) ≤ (260847 / 2048 : ℝ) by norm_num)
  have hb_5_2 : (146913 / 2048 : ℝ) * (σ ^ 5 * t ^ 2) ≤ (146913 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 5 2 (by norm_num)) (show (0 : ℝ) ≤ (146913 / 2048 : ℝ) by norm_num)
  have hb_6_2 : (-27 / 256 : ℝ) * (σ ^ 6 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-27 / 256 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 2)
    rw [zero_mul] at this
    exact this
  have hb_7_2 : (-1545 / 64 : ℝ) * (σ ^ 7 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1545 / 64 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 7 2)
    rw [zero_mul] at this
    exact this
  have hb_8_4 : (-4125 / 4096 : ℝ) * (σ ^ 8 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-4125 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 4)
    rw [zero_mul] at this
    exact this
  have hb_10_2 : (1275 / 2048 : ℝ) * (σ ^ 10 * t ^ 2) ≤ (1275 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 10 2 (by norm_num)) (show (0 : ℝ) ≤ (1275 / 2048 : ℝ) by norm_num)
  linarith

/-- Group 3 of the lower-order monomials of the summed cofactor. -/
noncomputable def skewTiltSumPart3 (σ t : ℝ) : ℝ := (-483 / 32 : ℝ) * (σ ^ 0 * t ^ 4) + (-1173 / 128 : ℝ) * (σ ^ 1 * t ^ 0) + (-1035 / 2048 : ℝ) * (σ ^ 1 * t ^ 8) + (164021 / 4096 : ℝ) * (σ ^ 2 * t ^ 4) + (1751 / 256 : ℝ) * (σ ^ 3 * t ^ 0) + (-2475 / 2048 : ℝ) * (σ ^ 3 * t ^ 8) + (-84555 / 2048 : ℝ) * (σ ^ 4 * t ^ 6) + (-40335 / 1024 : ℝ) * (σ ^ 5 * t ^ 4) + (17265 / 2048 : ℝ) * (σ ^ 6 * t ^ 4) + (4125 / 1024 : ℝ) * (σ ^ 7 * t ^ 4) + (3825 / 2048 : ℝ) * (σ ^ 9 * t ^ 0) + (225 / 2048 : ℝ) * (σ ^ 11 * t ^ 0)

theorem skewTiltSumPart3_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltSumPart3 σ t ≤ (251167 / 4096 : ℝ) * t ^ 10 := by
  unfold skewTiltSumPart3
  have hb_0_4 : (-483 / 32 : ℝ) * (σ ^ 0 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-483 / 32 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 4)
    rw [zero_mul] at this
    exact this
  have hb_1_0 : (-1173 / 128 : ℝ) * (σ ^ 1 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1173 / 128 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 0)
    rw [zero_mul] at this
    exact this
  have hb_1_8 : (-1035 / 2048 : ℝ) * (σ ^ 1 * t ^ 8) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1035 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 8)
    rw [zero_mul] at this
    exact this
  have hb_2_4 : (164021 / 4096 : ℝ) * (σ ^ 2 * t ^ 4) ≤ (164021 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 4 (by norm_num)) (show (0 : ℝ) ≤ (164021 / 4096 : ℝ) by norm_num)
  have hb_3_0 : (1751 / 256 : ℝ) * (σ ^ 3 * t ^ 0) ≤ (1751 / 256 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 3 0 (by norm_num)) (show (0 : ℝ) ≤ (1751 / 256 : ℝ) by norm_num)
  have hb_3_8 : (-2475 / 2048 : ℝ) * (σ ^ 3 * t ^ 8) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2475 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 8)
    rw [zero_mul] at this
    exact this
  have hb_4_6 : (-84555 / 2048 : ℝ) * (σ ^ 4 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-84555 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 6)
    rw [zero_mul] at this
    exact this
  have hb_5_4 : (-40335 / 1024 : ℝ) * (σ ^ 5 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-40335 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 4)
    rw [zero_mul] at this
    exact this
  have hb_6_4 : (17265 / 2048 : ℝ) * (σ ^ 6 * t ^ 4) ≤ (17265 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 6 4 (by norm_num)) (show (0 : ℝ) ≤ (17265 / 2048 : ℝ) by norm_num)
  have hb_7_4 : (4125 / 1024 : ℝ) * (σ ^ 7 * t ^ 4) ≤ (4125 / 1024 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 7 4 (by norm_num)) (show (0 : ℝ) ≤ (4125 / 1024 : ℝ) by norm_num)
  have hb_9_0 : (3825 / 2048 : ℝ) * (σ ^ 9 * t ^ 0) ≤ (3825 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 9 0 (by norm_num)) (show (0 : ℝ) ≤ (3825 / 2048 : ℝ) by norm_num)
  have hb_11_0 : (225 / 2048 : ℝ) * (σ ^ 11 * t ^ 0) ≤ (225 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 11 0 (by norm_num)) (show (0 : ℝ) ≤ (225 / 2048 : ℝ) by norm_num)
  linarith

/-- Group 4 of the lower-order monomials of the summed cofactor. -/
noncomputable def skewTiltSumPart4 (σ t : ℝ) : ℝ := (4935 / 4096 : ℝ) * (σ ^ 0 * t ^ 6) + (-2317 / 256 : ℝ) * (σ ^ 1 * t ^ 2) + (-2475 / 2048 : ℝ) * (σ ^ 1 * t ^ 10) + (-56295 / 512 : ℝ) * (σ ^ 2 * t ^ 6) + (-26099 / 1024 : ℝ) * (σ ^ 3 * t ^ 2) + (-1229 / 256 : ℝ) * (σ ^ 4 * t ^ 0) + (2475 / 4096 : ℝ) * (σ ^ 4 * t ^ 8) + (7425 / 1024 : ℝ) * (σ ^ 5 * t ^ 6) + (-2475 / 1024 : ℝ) * (σ ^ 6 * t ^ 6) + (-7521 / 4096 : ℝ) * (σ ^ 8 * t ^ 0) + (-6375 / 2048 : ℝ) * (σ ^ 9 * t ^ 2) + (-75 / 4096 : ℝ) * (σ ^ 12 * t ^ 0)

theorem skewTiltSumPart4_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltSumPart4 σ t ≤ (18555 / 2048 : ℝ) * t ^ 10 := by
  unfold skewTiltSumPart4
  have hb_0_6 : (4935 / 4096 : ℝ) * (σ ^ 0 * t ^ 6) ≤ (4935 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 0 6 (by norm_num)) (show (0 : ℝ) ≤ (4935 / 4096 : ℝ) by norm_num)
  have hb_1_2 : (-2317 / 256 : ℝ) * (σ ^ 1 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2317 / 256 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 2)
    rw [zero_mul] at this
    exact this
  have hb_1_10 : (-2475 / 2048 : ℝ) * (σ ^ 1 * t ^ 10) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2475 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 10)
    rw [zero_mul] at this
    exact this
  have hb_2_6 : (-56295 / 512 : ℝ) * (σ ^ 2 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-56295 / 512 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 6)
    rw [zero_mul] at this
    exact this
  have hb_3_2 : (-26099 / 1024 : ℝ) * (σ ^ 3 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-26099 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 2)
    rw [zero_mul] at this
    exact this
  have hb_4_0 : (-1229 / 256 : ℝ) * (σ ^ 4 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1229 / 256 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 0)
    rw [zero_mul] at this
    exact this
  have hb_4_8 : (2475 / 4096 : ℝ) * (σ ^ 4 * t ^ 8) ≤ (2475 / 4096 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 4 8 (by norm_num)) (show (0 : ℝ) ≤ (2475 / 4096 : ℝ) by norm_num)
  have hb_5_6 : (7425 / 1024 : ℝ) * (σ ^ 5 * t ^ 6) ≤ (7425 / 1024 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 5 6 (by norm_num)) (show (0 : ℝ) ≤ (7425 / 1024 : ℝ) by norm_num)
  have hb_6_6 : (-2475 / 1024 : ℝ) * (σ ^ 6 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2475 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 6)
    rw [zero_mul] at this
    exact this
  have hb_8_0 : (-7521 / 4096 : ℝ) * (σ ^ 8 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-7521 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 0)
    rw [zero_mul] at this
    exact this
  have hb_9_2 : (-6375 / 2048 : ℝ) * (σ ^ 9 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-6375 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 9 2)
    rw [zero_mul] at this
    exact this
  have hb_12_0 : (-75 / 4096 : ℝ) * (σ ^ 12 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-75 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 12 0)
    rw [zero_mul] at this
    exact this
  linarith

theorem skewTiltCofactorSum_split (σ t : ℝ) :
    skewTiltCofactorQ σ t + skewTiltCofactor σ t = (-(675 / 4096 : ℝ)) * t ^ 12 + skewTiltSumPart1 σ t + skewTiltSumPart2 σ t + skewTiltSumPart3 σ t + skewTiltSumPart4 σ t := by
  unfold skewTiltCofactorQ skewTiltCofactor skewTiltSumPart1 skewTiltSumPart2 skewTiltSumPart3 skewTiltSumPart4
  ring

/-- Above height 58 the summed cofactor is negative on the strip. -/
theorem skewTiltCofactorSum_neg (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (58 : ℝ) ≤ t) :
    skewTiltCofactorQ σ t + skewTiltCofactor σ t < 0 := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  rw [skewTiltCofactorSum_split]
  have p1 := skewTiltSumPart1_le σ t h0 h1 ht1
  have p2 := skewTiltSumPart2_le σ t h0 h1 ht1
  have p3 := skewTiltSumPart3_le σ t h0 h1 ht1
  have p4 := skewTiltSumPart4_le σ t h0 h1 ht1
  have hbig : (1100903 / 2048 : ℝ) * t ^ 10 < (675 / 4096 : ℝ) * t ^ 12 := by
    have : t ^ 12 = t ^ 10 * t ^ 2 := by ring
    rw [this]
    have h10 : 0 < t ^ 10 := pow_pos (by linarith) 10
    have hsq : (58 : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith
    nlinarith
  linarith

/-- The real part of the regularized cut is the tilt times the combined cofactor. -/
theorem skewCut_re_tilt (σ t ε : ℝ) (hs : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ≠ 0)
    (hs3 : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 ≠ 0) :
    2 * (skewCut ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ε).re *
        Complex.normSq (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) * (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3)) =
      (2 * σ - 1) * (skewTiltCofactorQ σ t + Real.log (4 / ε) * skewTiltCofactor σ t) := by
  have h1 := skewFinitePart_re_tilt σ t hs hs3
  have h2 := skewLogCoeff_re_tilt σ t hs hs3
  unfold skewCut
  rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  linear_combination h1 + Real.log (4 / ε) * h2

/-- Tilt detection by the regularized elementary cut at every cutoff `ε ≤ 4/e` and height at least 58. -/
theorem skewCut_re_eq_zero_iff (σ t ε : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (58 : ℝ) ≤ t)
    (hε : 1 ≤ Real.log (4 / ε)) :
    (skewCut ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ε).re = 0 ↔ σ = 1 / 2 := by
  have hs : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hs3 : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have key := skewCut_re_tilt σ t ε hs hs3
  have hpos : 0 < Complex.normSq (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) * (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3)) :=
    Complex.normSq_pos.mpr (mul_ne_zero hs hs3)
  have hL := skewTiltCofactor_neg σ t h0 h1 (by linarith)
  have hS := skewTiltCofactorSum_neg σ t h0 h1 (by linarith)
  have hneg : skewTiltCofactorQ σ t + Real.log (4 / ε) * skewTiltCofactor σ t < 0 := by
    have : Real.log (4 / ε) * skewTiltCofactor σ t ≤ 1 * skewTiltCofactor σ t :=
      mul_le_mul_of_nonpos_right hε hL.le
    linarith
  constructor
  · intro hre
    rw [hre] at key
    have : (2 * σ - 1) * (skewTiltCofactorQ σ t + Real.log (4 / ε) * skewTiltCofactor σ t) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hneg.ne
  · intro hσ
    subst hσ
    have : 2 * (skewCut (((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I) ε).re * Complex.normSq ((((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I) * ((((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I) + 3)) = 0 := by
      rw [key]; ring
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hpos.ne'

end RHTower.D4BMScalarStream
