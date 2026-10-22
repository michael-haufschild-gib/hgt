import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorSkewFinitePart
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorSkewTiltDetection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorSkewRadialTrace

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
noncomputable def skewRadLaurent (s u : ℂ) : ℂ := (((-135 / 16 : ℂ) * s ^ (2 : ℕ) + (-765 / 32 : ℂ) * s ^ (3 : ℕ) + (-435 / 64 : ℂ) * s ^ (4 : ℕ) + (6805 / 128 : ℂ) * s ^ (5 : ℕ) + (11865 / 128 : ℂ) * s ^ (6 : ℕ) + (2375 / 32 : ℂ) * s ^ (7 : ℕ) + (135 / 4 : ℂ) * s ^ (8 : ℕ) + (1145 / 128 : ℂ) * s ^ (9 : ℕ) + (165 / 128 : ℂ) * s ^ (10 : ℕ) + (5 / 64 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3))) * u ^ (7 : ℕ) + (((675 / 8 : ℂ) * s ^ (2 : ℕ) + (711 / 2 : ℂ) * s ^ (3 : ℕ) + (21021 / 32 : ℂ) * s ^ (4 : ℕ) + (10549 / 16 : ℂ) * s ^ (5 : ℕ) + (6111 / 16 : ℂ) * s ^ (6 : ℕ) + (255 / 2 : ℂ) * s ^ (7 : ℕ) + (729 / 32 : ℂ) * s ^ (8 : ℕ) + (27 / 16 : ℂ) * s ^ (9 : ℕ)) / (s * (s + 3))) * u ^ (5 : ℕ) + (((-21 / 2 : ℂ) + (-25 : ℂ) * s + (-423 / 16 : ℂ) * s ^ (2 : ℕ) + (-245 / 32 : ℂ) * s ^ (3 : ℕ) + (255 / 32 : ℂ) * s ^ (4 : ℕ) + (223 / 32 : ℂ) * s ^ (5 : ℕ) + (63 / 32 : ℂ) * s ^ (6 : ℕ) + (3 / 16 : ℂ) * s ^ (7 : ℕ)) / (s * (s + 3))) * u ^ (3 : ℕ) + (((6 : ℂ) + (233 / 2 : ℂ) * s + (1683 / 8 : ℂ) * s ^ (2 : ℕ) + (311 / 2 : ℂ) * s ^ (3 : ℕ) + (435 / 8 : ℂ) * s ^ (4 : ℕ) + (29 / 4 : ℂ) * s ^ (5 : ℕ)) / (s * (s + 3))) * u + (((9 / 2 : ℂ) + (-21 / 2 : ℂ) * s + (-27 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ)) / (s * (s + 3))) * u⁻¹

theorem skewRadDensitySS_substitution (s u : ℂ) (hu : u ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewRadDensitySS s (1 / u) = skewRadLaurent s u := by
  unfold skewRadDensitySS skewRadLaurent
  field_simp
  ring

/-- Horizon finite part of the dressed radial flux: the `z³` coefficient of `skewRadLaurent s ((1−z)^{1/2})`. -/
noncomputable def skewRadHorizonFP (s : ℂ) : ℂ := (((3 / 8 : ℂ) + (-97 / 8 : ℂ) * s + (-3447 / 128 : ℂ) * s ^ (2 : ℕ) + (-17903 / 256 : ℂ) * s ^ (3 : ℕ) + (-197955 / 1024 : ℂ) * s ^ (4 : ℕ) + (-660171 / 2048 : ℂ) * s ^ (5 : ℕ) + (-659463 / 2048 : ℂ) * s ^ (6 : ℕ) + (-103519 / 512 : ℂ) * s ^ (7 : ℕ) + (-41445 / 512 : ℂ) * s ^ (8 : ℕ) + (-41155 / 2048 : ℂ) * s ^ (9 : ℕ) + (-5775 / 2048 : ℂ) * s ^ (10 : ℕ) + (-175 / 1024 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3)))

theorem skewRadHorizonFP_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    (((-135 / 16 : ℂ) * s ^ (2 : ℕ) + (-765 / 32 : ℂ) * s ^ (3 : ℕ) + (-435 / 64 : ℂ) * s ^ (4 : ℕ) + (6805 / 128 : ℂ) * s ^ (5 : ℕ) + (11865 / 128 : ℂ) * s ^ (6 : ℕ) + (2375 / 32 : ℂ) * s ^ (7 : ℕ) + (135 / 4 : ℂ) * s ^ (8 : ℕ) + (1145 / 128 : ℂ) * s ^ (9 : ℕ) + (165 / 128 : ℂ) * s ^ (10 : ℕ) + (5 / 64 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3))) * (-35 / 16 : ℂ) + (((675 / 8 : ℂ) * s ^ (2 : ℕ) + (711 / 2 : ℂ) * s ^ (3 : ℕ) + (21021 / 32 : ℂ) * s ^ (4 : ℕ) + (10549 / 16 : ℂ) * s ^ (5 : ℕ) + (6111 / 16 : ℂ) * s ^ (6 : ℕ) + (255 / 2 : ℂ) * s ^ (7 : ℕ) + (729 / 32 : ℂ) * s ^ (8 : ℕ) + (27 / 16 : ℂ) * s ^ (9 : ℕ)) / (s * (s + 3))) * (-5 / 16 : ℂ) + (((-21 / 2 : ℂ) + (-25 : ℂ) * s + (-423 / 16 : ℂ) * s ^ (2 : ℕ) + (-245 / 32 : ℂ) * s ^ (3 : ℕ) + (255 / 32 : ℂ) * s ^ (4 : ℕ) + (223 / 32 : ℂ) * s ^ (5 : ℕ) + (63 / 32 : ℂ) * s ^ (6 : ℕ) + (3 / 16 : ℂ) * s ^ (7 : ℕ)) / (s * (s + 3))) * (1 / 16 : ℂ) + (((6 : ℂ) + (233 / 2 : ℂ) * s + (1683 / 8 : ℂ) * s ^ (2 : ℕ) + (311 / 2 : ℂ) * s ^ (3 : ℕ) + (435 / 8 : ℂ) * s ^ (4 : ℕ) + (29 / 4 : ℂ) * s ^ (5 : ℕ)) / (s * (s + 3))) * (-1 / 16 : ℂ) + (((9 / 2 : ℂ) + (-21 / 2 : ℂ) * s + (-27 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ)) / (s * (s + 3))) * (5 / 16 : ℂ) = skewRadHorizonFP s := by
  unfold skewRadHorizonFP
  field_simp
  ring

/-- Rational part of the bulk finite part. -/
noncomputable def skewBulkRational (s : ℂ) : ℂ := (((-219 / 64 : ℂ) + (1157 / 128 : ℂ) * s + (2457 / 128 : ℂ) * s ^ (2 : ℕ) + (9785 / 256 : ℂ) * s ^ (3 : ℕ) + (304129 / 4096 : ℂ) * s ^ (4 : ℕ) + (2203847 / 24576 : ℂ) * s ^ (5 : ℕ) + (564529 / 8192 : ℂ) * s ^ (6 : ℕ) + (216647 / 6144 : ℂ) * s ^ (7 : ℕ) + (24903 / 2048 : ℂ) * s ^ (8 : ℕ) + (67511 / 24576 : ℂ) * s ^ (9 : ℕ) + (3025 / 8192 : ℂ) * s ^ (10 : ℕ) + (275 / 12288 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3)))

theorem skewBulkFinitePart_eq' (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewBulkFinitePart s = skewBulkRational s + (skewPfB1 s + skewPfD1 s) * ((Real.log 2 : ℝ) : ℂ) := by
  rw [skewBulkFinitePart_eq s hs hs3]
  unfold skewBulkRational
  field_simp

/-- Finite part of the elementary skew cut (cutoff scale `4` absorbed into the logarithm). -/
noncomputable def skewFinitePart (s : ℂ) : ℂ := (-3) * skewBulkRational s - (1 / 2) * skewRadHorizonFP s

theorem skewFinitePart_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewFinitePart s = (((645 / 64 : ℂ) + (-2695 / 128 : ℂ) * s + (-11295 / 256 : ℂ) * s ^ (2 : ℕ) + (-40807 / 512 : ℂ) * s ^ (3 : ℕ) + (-516477 / 4096 : ℂ) * s ^ (4 : ℕ) + (-883505 / 8192 : ℂ) * s ^ (5 : ℕ) + (-374661 / 8192 : ℂ) * s ^ (6 : ℕ) + (-9609 / 2048 : ℂ) * s ^ (7 : ℕ) + (8181 / 2048 : ℂ) * s ^ (8 : ℕ) + (14799 / 8192 : ℂ) * s ^ (9 : ℕ) + (2475 / 8192 : ℂ) * s ^ (10 : ℕ) + (75 / 4096 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3))) := by
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
    rw [Real.log_div (by norm_num) hε.ne', show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [hlog]
  push_cast
  linear_combination (-(Real.log ε : ℂ)) * h1 + (3 * (Real.log 2 : ℂ)) * h2

/-- The difference-quotient cofactor of the finite part. -/
noncomputable def skewFPCofactor (s w : ℂ) : ℂ := (-1935 / 64 : ℂ) + (-645 / 64 : ℂ) * w + (-645 / 64 : ℂ) * s + (-28495 / 256 : ℂ) * s * w + (-122421 / 512 : ℂ) * s * w ^ (2 : ℕ) + (-1549431 / 4096 : ℂ) * s * w ^ (3 : ℕ) + (-2650515 / 8192 : ℂ) * s * w ^ (4 : ℕ) + (-1123983 / 8192 : ℂ) * s * w ^ (5 : ℕ) + (-28827 / 2048 : ℂ) * s * w ^ (6 : ℕ) + (24543 / 2048 : ℂ) * s * w ^ (7 : ℕ) + (44397 / 8192 : ℂ) * s * w ^ (8 : ℕ) + (7425 / 8192 : ℂ) * s * w ^ (9 : ℕ) + (225 / 4096 : ℂ) * s * w ^ (10 : ℕ) + (-122421 / 512 : ℂ) * s ^ (2 : ℕ) * w + (-1875887 / 4096 : ℂ) * s ^ (2 : ℕ) * w ^ (2 : ℕ) + (-3683469 / 8192 : ℂ) * s ^ (2 : ℕ) * w ^ (3 : ℕ) + (-31367 / 128 : ℂ) * s ^ (2 : ℕ) * w ^ (4 : ℕ) + (-489969 / 8192 : ℂ) * s ^ (2 : ℕ) * w ^ (5 : ℕ) + (7467 / 1024 : ℂ) * s ^ (2 : ℕ) * w ^ (6 : ℕ) + (77121 / 8192 : ℂ) * s ^ (2 : ℕ) * w ^ (7 : ℕ) + (1389 / 512 : ℂ) * s ^ (2 : ℕ) * w ^ (8 : ℕ) + (2925 / 8192 : ℂ) * s ^ (2 : ℕ) * w ^ (9 : ℕ) + (75 / 4096 : ℂ) * s ^ (2 : ℕ) * w ^ (10 : ℕ) + (-1549431 / 4096 : ℂ) * s ^ (3 : ℕ) * w + (-3683469 / 8192 : ℂ) * s ^ (3 : ℕ) * w ^ (2 : ℕ) + (-31367 / 128 : ℂ) * s ^ (3 : ℕ) * w ^ (3 : ℕ) + (-489969 / 8192 : ℂ) * s ^ (3 : ℕ) * w ^ (4 : ℕ) + (7467 / 1024 : ℂ) * s ^ (3 : ℕ) * w ^ (5 : ℕ) + (77121 / 8192 : ℂ) * s ^ (3 : ℕ) * w ^ (6 : ℕ) + (1389 / 512 : ℂ) * s ^ (3 : ℕ) * w ^ (7 : ℕ) + (2925 / 8192 : ℂ) * s ^ (3 : ℕ) * w ^ (8 : ℕ) + (75 / 4096 : ℂ) * s ^ (3 : ℕ) * w ^ (9 : ℕ) + (-2650515 / 8192 : ℂ) * s ^ (4 : ℕ) * w + (-31367 / 128 : ℂ) * s ^ (4 : ℕ) * w ^ (2 : ℕ) + (-489969 / 8192 : ℂ) * s ^ (4 : ℕ) * w ^ (3 : ℕ) + (7467 / 1024 : ℂ) * s ^ (4 : ℕ) * w ^ (4 : ℕ) + (77121 / 8192 : ℂ) * s ^ (4 : ℕ) * w ^ (5 : ℕ) + (1389 / 512 : ℂ) * s ^ (4 : ℕ) * w ^ (6 : ℕ) + (2925 / 8192 : ℂ) * s ^ (4 : ℕ) * w ^ (7 : ℕ) + (75 / 4096 : ℂ) * s ^ (4 : ℕ) * w ^ (8 : ℕ) + (-1123983 / 8192 : ℂ) * s ^ (5 : ℕ) * w + (-489969 / 8192 : ℂ) * s ^ (5 : ℕ) * w ^ (2 : ℕ) + (7467 / 1024 : ℂ) * s ^ (5 : ℕ) * w ^ (3 : ℕ) + (77121 / 8192 : ℂ) * s ^ (5 : ℕ) * w ^ (4 : ℕ) + (1389 / 512 : ℂ) * s ^ (5 : ℕ) * w ^ (5 : ℕ) + (2925 / 8192 : ℂ) * s ^ (5 : ℕ) * w ^ (6 : ℕ) + (75 / 4096 : ℂ) * s ^ (5 : ℕ) * w ^ (7 : ℕ) + (-28827 / 2048 : ℂ) * s ^ (6 : ℕ) * w + (7467 / 1024 : ℂ) * s ^ (6 : ℕ) * w ^ (2 : ℕ) + (77121 / 8192 : ℂ) * s ^ (6 : ℕ) * w ^ (3 : ℕ) + (1389 / 512 : ℂ) * s ^ (6 : ℕ) * w ^ (4 : ℕ) + (2925 / 8192 : ℂ) * s ^ (6 : ℕ) * w ^ (5 : ℕ) + (75 / 4096 : ℂ) * s ^ (6 : ℕ) * w ^ (6 : ℕ) + (24543 / 2048 : ℂ) * s ^ (7 : ℕ) * w + (77121 / 8192 : ℂ) * s ^ (7 : ℕ) * w ^ (2 : ℕ) + (1389 / 512 : ℂ) * s ^ (7 : ℕ) * w ^ (3 : ℕ) + (2925 / 8192 : ℂ) * s ^ (7 : ℕ) * w ^ (4 : ℕ) + (75 / 4096 : ℂ) * s ^ (7 : ℕ) * w ^ (5 : ℕ) + (44397 / 8192 : ℂ) * s ^ (8 : ℕ) * w + (1389 / 512 : ℂ) * s ^ (8 : ℕ) * w ^ (2 : ℕ) + (2925 / 8192 : ℂ) * s ^ (8 : ℕ) * w ^ (3 : ℕ) + (75 / 4096 : ℂ) * s ^ (8 : ℕ) * w ^ (4 : ℕ) + (7425 / 8192 : ℂ) * s ^ (9 : ℕ) * w + (2925 / 8192 : ℂ) * s ^ (9 : ℕ) * w ^ (2 : ℕ) + (75 / 4096 : ℂ) * s ^ (9 : ℕ) * w ^ (3 : ℕ) + (225 / 4096 : ℂ) * s ^ (10 : ℕ) * w + (75 / 4096 : ℂ) * s ^ (10 : ℕ) * w ^ (2 : ℕ)

theorem skewFinitePart_sub (s w : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hw : w ≠ 0) (hw3 : w + 3 ≠ 0) :
    skewFinitePart s - skewFinitePart w = (s - w) * skewFPCofactor s w / (s * (s + 3) * (w * (w + 3))) := by
  rw [skewFinitePart_eq s hs hs3, skewFinitePart_eq w hw hw3]
  unfold skewFPCofactor
  field_simp
  ring

/-- The finite part's cofactor at the reflected pair, as a real polynomial. -/
noncomputable def skewTiltCofactorQ (σ t : ℝ) : ℝ := (-1267 / 32 : ℝ) + (-8183 / 256 : ℝ) * t ^ (2 : ℕ) + (-531 / 64 : ℝ) * t ^ (4 : ℕ) + (64857 / 4096 : ℝ) * t ^ (6 : ℕ) + (60645 / 4096 : ℝ) * t ^ (8 : ℕ) + (13791 / 4096 : ℝ) * t ^ (10 : ℕ) + (675 / 4096 : ℝ) * t ^ (12 : ℕ) + (-4347 / 128 : ℝ) * σ + (7229 / 256 : ℝ) * σ * t ^ (2 : ℕ) + (185381 / 2048 : ℝ) * σ * t ^ (4 : ℕ) + (177165 / 2048 : ℝ) * σ * t ^ (6 : ℕ) + (34299 / 2048 : ℝ) * σ * t ^ (8 : ℕ) + (2475 / 2048 : ℝ) * σ * t ^ (10 : ℕ) + (7441 / 256 : ℝ) * σ ^ (2 : ℕ) + (7649 / 256 : ℝ) * σ ^ (2 : ℕ) * t ^ (2 : ℕ) + (20267 / 4096 : ℝ) * σ ^ (2 : ℕ) * t ^ (4 : ℕ) + (-43497 / 512 : ℝ) * σ ^ (2 : ℕ) * t ^ (6 : ℕ) + (-71073 / 4096 : ℝ) * σ ^ (2 : ℕ) * t ^ (8 : ℕ) + (-2475 / 2048 : ℝ) * σ ^ (2 : ℕ) * t ^ (10 : ℕ) + (3545 / 256 : ℝ) * σ ^ (3 : ℕ) + (-75965 / 1024 : ℝ) * σ ^ (3 : ℕ) * t ^ (2 : ℕ) + (-370893 / 2048 : ℝ) * σ ^ (3 : ℕ) * t ^ (4 : ℕ) + (-1413 / 256 : ℝ) * σ ^ (3 : ℕ) * t ^ (6 : ℕ) + (2475 / 2048 : ℝ) * σ ^ (3 : ℕ) * t ^ (8 : ℕ) + (-3767 / 256 : ℝ) * σ ^ (4 : ℕ) + (-236813 / 4096 : ℝ) * σ ^ (4 : ℕ) * t ^ (2 : ℕ) + (137169 / 2048 : ℝ) * σ ^ (4 : ℕ) * t ^ (4 : ℕ) + (18027 / 2048 : ℝ) * σ ^ (4 : ℕ) * t ^ (6 : ℕ) + (-2475 / 4096 : ℝ) * σ ^ (4 : ℕ) * t ^ (8 : ℕ) + (6609 / 2048 : ℝ) * σ ^ (5 : ℕ) + (175935 / 2048 : ℝ) * σ ^ (5 : ℕ) * t ^ (2 : ℕ) + (26079 / 1024 : ℝ) * σ ^ (5 : ℕ) * t ^ (4 : ℕ) + (-7425 / 1024 : ℝ) * σ ^ (5 : ℕ) * t ^ (6 : ℕ) + (31649 / 4096 : ℝ) * σ ^ (6 : ℕ) + (4131 / 256 : ℝ) * σ ^ (6 : ℕ) * t ^ (2 : ℕ) + (-7761 / 2048 : ℝ) * σ ^ (6 : ℕ) * t ^ (4 : ℕ) + (2475 / 1024 : ℝ) * σ ^ (6 : ℕ) * t ^ (6 : ℕ) + (-9831 / 2048 : ℝ) * σ ^ (7 : ℕ) + (-2217 / 64 : ℝ) * σ ^ (7 : ℕ) * t ^ (2 : ℕ) + (-4125 / 1024 : ℝ) * σ ^ (7 : ℕ) * t ^ (4 : ℕ) + (-8607 / 4096 : ℝ) * σ ^ (8 : ℕ) + (16347 / 4096 : ℝ) * σ ^ (8 : ℕ) * t ^ (2 : ℕ) + (4125 / 4096 : ℝ) * σ ^ (8 : ℕ) * t ^ (4 : ℕ) + (4095 / 2048 : ℝ) * σ ^ (9 : ℕ) + (6375 / 2048 : ℝ) * σ ^ (9 : ℕ) * t ^ (2 : ℕ) + (-813 / 4096 : ℝ) * σ ^ (10 : ℕ) + (-1275 / 2048 : ℝ) * σ ^ (10 : ℕ) * t ^ (2 : ℕ) + (-225 / 2048 : ℝ) * σ ^ (11 : ℕ) + (75 / 4096 : ℝ) * σ ^ (12 : ℕ)

theorem skewFPCofactor_reflected (σ t : ℝ) :
    skewFPCofactor ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) (-1 - (σ : ℂ) + (t : ℂ) * Complex.I) = (skewTiltCofactorQ σ t : ℂ) := by
  unfold skewFPCofactor skewTiltCofactorQ
  push_cast
  linear_combination ((8183 / 256 : ℂ) * (t : ℂ) ^ (2 : ℕ) + (531 / 64 : ℂ) * (t : ℂ) ^ (4 : ℕ) + (-531 / 64 : ℂ) * (t : ℂ) ^ (4 : ℕ) * Complex.I ^ (2 : ℕ) + (-64857 / 4096 : ℂ) * (t : ℂ) ^ (6 : ℕ) + (64857 / 4096 : ℂ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (2 : ℕ) + (-64857 / 4096 : ℂ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (4 : ℕ) + (-60645 / 4096 : ℂ) * (t : ℂ) ^ (8 : ℕ) + (60645 / 4096 : ℂ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (2 : ℕ) + (-60645 / 4096 : ℂ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (4 : ℕ) + (60645 / 4096 : ℂ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (6 : ℕ) + (-13791 / 4096 : ℂ) * (t : ℂ) ^ (10 : ℕ) + (13791 / 4096 : ℂ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (2 : ℕ) + (-13791 / 4096 : ℂ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (4 : ℕ) + (13791 / 4096 : ℂ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (6 : ℕ) + (-13791 / 4096 : ℂ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (8 : ℕ) + (-675 / 4096 : ℂ) * (t : ℂ) ^ (12 : ℕ) + (675 / 4096 : ℂ) * (t : ℂ) ^ (12 : ℕ) * Complex.I ^ (2 : ℕ) + (-675 / 4096 : ℂ) * (t : ℂ) ^ (12 : ℕ) * Complex.I ^ (4 : ℕ) + (675 / 4096 : ℂ) * (t : ℂ) ^ (12 : ℕ) * Complex.I ^ (6 : ℕ) + (-675 / 4096 : ℂ) * (t : ℂ) ^ (12 : ℕ) * Complex.I ^ (8 : ℕ) + (675 / 4096 : ℂ) * (t : ℂ) ^ (12 : ℕ) * Complex.I ^ (10 : ℕ) + (-7229 / 256 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (2 : ℕ) + (-185381 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (4 : ℕ) + (185381 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (4 : ℕ) * Complex.I ^ (2 : ℕ) + (-177165 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (6 : ℕ) + (177165 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (2 : ℕ) + (-177165 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (4 : ℕ) + (-34299 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (8 : ℕ) + (34299 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (2 : ℕ) + (-34299 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (4 : ℕ) + (34299 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (6 : ℕ) + (-2475 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (10 : ℕ) + (2475 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (2 : ℕ) + (-2475 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (4 : ℕ) + (2475 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (6 : ℕ) + (-2475 / 2048 : ℂ) * (σ : ℂ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (8 : ℕ) + (-7649 / 256 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (2 : ℕ) + (-20267 / 4096 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (4 : ℕ) + (20267 / 4096 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (4 : ℕ) * Complex.I ^ (2 : ℕ) + (43497 / 512 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (6 : ℕ) + (-43497 / 512 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (2 : ℕ) + (43497 / 512 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (4 : ℕ) + (71073 / 4096 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (8 : ℕ) + (-71073 / 4096 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (2 : ℕ) + (71073 / 4096 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (4 : ℕ) + (-71073 / 4096 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (6 : ℕ) + (2475 / 2048 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (10 : ℕ) + (-2475 / 2048 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (2 : ℕ) + (2475 / 2048 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (4 : ℕ) + (-2475 / 2048 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (6 : ℕ) + (2475 / 2048 : ℂ) * (σ : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (10 : ℕ) * Complex.I ^ (8 : ℕ) + (75965 / 1024 : ℂ) * (σ : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (2 : ℕ) + (370893 / 2048 : ℂ) * (σ : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (4 : ℕ) + (-370893 / 2048 : ℂ) * (σ : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (4 : ℕ) * Complex.I ^ (2 : ℕ) + (1413 / 256 : ℂ) * (σ : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (6 : ℕ) + (-1413 / 256 : ℂ) * (σ : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (2 : ℕ) + (1413 / 256 : ℂ) * (σ : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (4 : ℕ) + (-2475 / 2048 : ℂ) * (σ : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (8 : ℕ) + (2475 / 2048 : ℂ) * (σ : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (2 : ℕ) + (-2475 / 2048 : ℂ) * (σ : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (4 : ℕ) + (2475 / 2048 : ℂ) * (σ : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (6 : ℕ) + (236813 / 4096 : ℂ) * (σ : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (2 : ℕ) + (-137169 / 2048 : ℂ) * (σ : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (4 : ℕ) + (137169 / 2048 : ℂ) * (σ : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (4 : ℕ) * Complex.I ^ (2 : ℕ) + (-18027 / 2048 : ℂ) * (σ : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (6 : ℕ) + (18027 / 2048 : ℂ) * (σ : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (2 : ℕ) + (-18027 / 2048 : ℂ) * (σ : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (4 : ℕ) + (2475 / 4096 : ℂ) * (σ : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (8 : ℕ) + (-2475 / 4096 : ℂ) * (σ : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (2 : ℕ) + (2475 / 4096 : ℂ) * (σ : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (4 : ℕ) + (-2475 / 4096 : ℂ) * (σ : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (8 : ℕ) * Complex.I ^ (6 : ℕ) + (-175935 / 2048 : ℂ) * (σ : ℂ) ^ (5 : ℕ) * (t : ℂ) ^ (2 : ℕ) + (-26079 / 1024 : ℂ) * (σ : ℂ) ^ (5 : ℕ) * (t : ℂ) ^ (4 : ℕ) + (26079 / 1024 : ℂ) * (σ : ℂ) ^ (5 : ℕ) * (t : ℂ) ^ (4 : ℕ) * Complex.I ^ (2 : ℕ) + (7425 / 1024 : ℂ) * (σ : ℂ) ^ (5 : ℕ) * (t : ℂ) ^ (6 : ℕ) + (-7425 / 1024 : ℂ) * (σ : ℂ) ^ (5 : ℕ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (2 : ℕ) + (7425 / 1024 : ℂ) * (σ : ℂ) ^ (5 : ℕ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (4 : ℕ) + (-4131 / 256 : ℂ) * (σ : ℂ) ^ (6 : ℕ) * (t : ℂ) ^ (2 : ℕ) + (7761 / 2048 : ℂ) * (σ : ℂ) ^ (6 : ℕ) * (t : ℂ) ^ (4 : ℕ) + (-7761 / 2048 : ℂ) * (σ : ℂ) ^ (6 : ℕ) * (t : ℂ) ^ (4 : ℕ) * Complex.I ^ (2 : ℕ) + (-2475 / 1024 : ℂ) * (σ : ℂ) ^ (6 : ℕ) * (t : ℂ) ^ (6 : ℕ) + (2475 / 1024 : ℂ) * (σ : ℂ) ^ (6 : ℕ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (2 : ℕ) + (-2475 / 1024 : ℂ) * (σ : ℂ) ^ (6 : ℕ) * (t : ℂ) ^ (6 : ℕ) * Complex.I ^ (4 : ℕ) + (2217 / 64 : ℂ) * (σ : ℂ) ^ (7 : ℕ) * (t : ℂ) ^ (2 : ℕ) + (4125 / 1024 : ℂ) * (σ : ℂ) ^ (7 : ℕ) * (t : ℂ) ^ (4 : ℕ) + (-4125 / 1024 : ℂ) * (σ : ℂ) ^ (7 : ℕ) * (t : ℂ) ^ (4 : ℕ) * Complex.I ^ (2 : ℕ) + (-16347 / 4096 : ℂ) * (σ : ℂ) ^ (8 : ℕ) * (t : ℂ) ^ (2 : ℕ) + (-4125 / 4096 : ℂ) * (σ : ℂ) ^ (8 : ℕ) * (t : ℂ) ^ (4 : ℕ) + (4125 / 4096 : ℂ) * (σ : ℂ) ^ (8 : ℕ) * (t : ℂ) ^ (4 : ℕ) * Complex.I ^ (2 : ℕ) + (-6375 / 2048 : ℂ) * (σ : ℂ) ^ (9 : ℕ) * (t : ℂ) ^ (2 : ℕ) + (1275 / 2048 : ℂ) * (σ : ℂ) ^ (10 : ℕ) * (t : ℂ) ^ (2 : ℕ)) * Complex.I_sq

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
noncomputable def skewTiltSumPart1 (σ t : ℝ) : ℝ := (-325 / 32 : ℝ) * (σ ^ (0 : ℕ) * t ^ (0 : ℕ)) + (48795 / 4096 : ℝ) * (σ ^ (0 : ℕ) * t ^ (8 : ℕ)) + (91979 / 2048 : ℝ) * (σ ^ (1 : ℕ) * t ^ (4 : ℕ)) + (1615 / 256 : ℝ) * (σ ^ (2 : ℕ) * t ^ (0 : ℕ)) + (4545 / 4096 : ℝ) * (σ ^ (2 : ℕ) * t ^ (8 : ℕ)) + (-377619 / 2048 : ℝ) * (σ ^ (3 : ℕ) * t ^ (4 : ℕ)) + (-237587 / 4096 : ℝ) * (σ ^ (4 : ℕ) * t ^ (2 : ℕ)) + (-4257 / 2048 : ℝ) * (σ ^ (5 : ℕ) * t ^ (0 : ℕ)) + (24575 / 4096 : ℝ) * (σ ^ (6 : ℕ) * t ^ (0 : ℕ)) + (-5433 / 2048 : ℝ) * (σ ^ (7 : ℕ) * t ^ (0 : ℕ)) + (43845 / 4096 : ℝ) * (σ ^ (8 : ℕ) * t ^ (2 : ℕ)) + (-2355 / 4096 : ℝ) * (σ ^ (10 : ℕ) * t ^ (0 : ℕ))

theorem skewTiltSumPart1_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltSumPart1 σ t ≤ (165779 / 2048 : ℝ) * t ^ (10 : ℕ) := by
  unfold skewTiltSumPart1
  have hb_0_0 : (-325 / 32 : ℝ) * (σ ^ (0 : ℕ) * t ^ (0 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-325 / 32 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 0)
    rw [zero_mul] at this
    exact this
  have hb_0_8 : (48795 / 4096 : ℝ) * (σ ^ (0 : ℕ) * t ^ (8 : ℕ)) ≤ (48795 / 4096 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 0 8 (by norm_num)) (show (0 : ℝ) ≤ (48795 / 4096 : ℝ) by norm_num)
  have hb_1_4 : (91979 / 2048 : ℝ) * (σ ^ (1 : ℕ) * t ^ (4 : ℕ)) ≤ (91979 / 2048 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 1 4 (by norm_num)) (show (0 : ℝ) ≤ (91979 / 2048 : ℝ) by norm_num)
  have hb_2_0 : (1615 / 256 : ℝ) * (σ ^ (2 : ℕ) * t ^ (0 : ℕ)) ≤ (1615 / 256 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 0 (by norm_num)) (show (0 : ℝ) ≤ (1615 / 256 : ℝ) by norm_num)
  have hb_2_8 : (4545 / 4096 : ℝ) * (σ ^ (2 : ℕ) * t ^ (8 : ℕ)) ≤ (4545 / 4096 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 8 (by norm_num)) (show (0 : ℝ) ≤ (4545 / 4096 : ℝ) by norm_num)
  have hb_3_4 : (-377619 / 2048 : ℝ) * (σ ^ (3 : ℕ) * t ^ (4 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-377619 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 4)
    rw [zero_mul] at this
    exact this
  have hb_4_2 : (-237587 / 4096 : ℝ) * (σ ^ (4 : ℕ) * t ^ (2 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-237587 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 2)
    rw [zero_mul] at this
    exact this
  have hb_5_0 : (-4257 / 2048 : ℝ) * (σ ^ (5 : ℕ) * t ^ (0 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-4257 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 0)
    rw [zero_mul] at this
    exact this
  have hb_6_0 : (24575 / 4096 : ℝ) * (σ ^ (6 : ℕ) * t ^ (0 : ℕ)) ≤ (24575 / 4096 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 6 0 (by norm_num)) (show (0 : ℝ) ≤ (24575 / 4096 : ℝ) by norm_num)
  have hb_7_0 : (-5433 / 2048 : ℝ) * (σ ^ (7 : ℕ) * t ^ (0 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-5433 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 7 0)
    rw [zero_mul] at this
    exact this
  have hb_8_2 : (43845 / 4096 : ℝ) * (σ ^ (8 : ℕ) * t ^ (2 : ℕ)) ≤ (43845 / 4096 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 8 2 (by norm_num)) (show (0 : ℝ) ≤ (43845 / 4096 : ℝ) by norm_num)
  have hb_10_0 : (-2355 / 4096 : ℝ) * (σ ^ (10 : ℕ) * t ^ (0 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2355 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 10 0)
    rw [zero_mul] at this
    exact this
  linarith

/-- Group 2 of the lower-order monomials of the summed cofactor. -/
noncomputable def skewTiltSumPart2 (σ t : ℝ) : ℝ := (-2153 / 256 : ℝ) * (σ ^ (0 : ℕ) * t ^ (2 : ℕ)) + (8385 / 4096 : ℝ) * (σ ^ (0 : ℕ) * t ^ (10 : ℕ)) + (155475 / 2048 : ℝ) * (σ ^ (1 : ℕ) * t ^ (6 : ℕ)) + (9431 / 256 : ℝ) * (σ ^ (2 : ℕ) * t ^ (2 : ℕ)) + (2475 / 2048 : ℝ) * (σ ^ (2 : ℕ) * t ^ (10 : ℕ)) + (18045 / 256 : ℝ) * (σ ^ (3 : ℕ) * t ^ (6 : ℕ)) + (260847 / 2048 : ℝ) * (σ ^ (4 : ℕ) * t ^ (4 : ℕ)) + (146913 / 2048 : ℝ) * (σ ^ (5 : ℕ) * t ^ (2 : ℕ)) + (-27 / 256 : ℝ) * (σ ^ (6 : ℕ) * t ^ (2 : ℕ)) + (-1545 / 64 : ℝ) * (σ ^ (7 : ℕ) * t ^ (2 : ℕ)) + (-4125 / 4096 : ℝ) * (σ ^ (8 : ℕ) * t ^ (4 : ℕ)) + (1275 / 2048 : ℝ) * (σ ^ (10 : ℕ) * t ^ (2 : ℕ))

theorem skewTiltSumPart2_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltSumPart2 σ t ≤ (1581971 / 4096 : ℝ) * t ^ (10 : ℕ) := by
  unfold skewTiltSumPart2
  have hb_0_2 : (-2153 / 256 : ℝ) * (σ ^ (0 : ℕ) * t ^ (2 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2153 / 256 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 2)
    rw [zero_mul] at this
    exact this
  have hb_0_10 : (8385 / 4096 : ℝ) * (σ ^ (0 : ℕ) * t ^ (10 : ℕ)) ≤ (8385 / 4096 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 0 10 (by norm_num)) (show (0 : ℝ) ≤ (8385 / 4096 : ℝ) by norm_num)
  have hb_1_6 : (155475 / 2048 : ℝ) * (σ ^ (1 : ℕ) * t ^ (6 : ℕ)) ≤ (155475 / 2048 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 1 6 (by norm_num)) (show (0 : ℝ) ≤ (155475 / 2048 : ℝ) by norm_num)
  have hb_2_2 : (9431 / 256 : ℝ) * (σ ^ (2 : ℕ) * t ^ (2 : ℕ)) ≤ (9431 / 256 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 2 (by norm_num)) (show (0 : ℝ) ≤ (9431 / 256 : ℝ) by norm_num)
  have hb_2_10 : (2475 / 2048 : ℝ) * (σ ^ (2 : ℕ) * t ^ (10 : ℕ)) ≤ (2475 / 2048 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 10 (by norm_num)) (show (0 : ℝ) ≤ (2475 / 2048 : ℝ) by norm_num)
  have hb_3_6 : (18045 / 256 : ℝ) * (σ ^ (3 : ℕ) * t ^ (6 : ℕ)) ≤ (18045 / 256 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 3 6 (by norm_num)) (show (0 : ℝ) ≤ (18045 / 256 : ℝ) by norm_num)
  have hb_4_4 : (260847 / 2048 : ℝ) * (σ ^ (4 : ℕ) * t ^ (4 : ℕ)) ≤ (260847 / 2048 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 4 4 (by norm_num)) (show (0 : ℝ) ≤ (260847 / 2048 : ℝ) by norm_num)
  have hb_5_2 : (146913 / 2048 : ℝ) * (σ ^ (5 : ℕ) * t ^ (2 : ℕ)) ≤ (146913 / 2048 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 5 2 (by norm_num)) (show (0 : ℝ) ≤ (146913 / 2048 : ℝ) by norm_num)
  have hb_6_2 : (-27 / 256 : ℝ) * (σ ^ (6 : ℕ) * t ^ (2 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-27 / 256 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 2)
    rw [zero_mul] at this
    exact this
  have hb_7_2 : (-1545 / 64 : ℝ) * (σ ^ (7 : ℕ) * t ^ (2 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1545 / 64 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 7 2)
    rw [zero_mul] at this
    exact this
  have hb_8_4 : (-4125 / 4096 : ℝ) * (σ ^ (8 : ℕ) * t ^ (4 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-4125 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 4)
    rw [zero_mul] at this
    exact this
  have hb_10_2 : (1275 / 2048 : ℝ) * (σ ^ (10 : ℕ) * t ^ (2 : ℕ)) ≤ (1275 / 2048 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 10 2 (by norm_num)) (show (0 : ℝ) ≤ (1275 / 2048 : ℝ) by norm_num)
  linarith

/-- Group 3 of the lower-order monomials of the summed cofactor. -/
noncomputable def skewTiltSumPart3 (σ t : ℝ) : ℝ := (-483 / 32 : ℝ) * (σ ^ (0 : ℕ) * t ^ (4 : ℕ)) + (-1173 / 128 : ℝ) * (σ ^ (1 : ℕ) * t ^ (0 : ℕ)) + (-1035 / 2048 : ℝ) * (σ ^ (1 : ℕ) * t ^ (8 : ℕ)) + (164021 / 4096 : ℝ) * (σ ^ (2 : ℕ) * t ^ (4 : ℕ)) + (1751 / 256 : ℝ) * (σ ^ (3 : ℕ) * t ^ (0 : ℕ)) + (-2475 / 2048 : ℝ) * (σ ^ (3 : ℕ) * t ^ (8 : ℕ)) + (-84555 / 2048 : ℝ) * (σ ^ (4 : ℕ) * t ^ (6 : ℕ)) + (-40335 / 1024 : ℝ) * (σ ^ (5 : ℕ) * t ^ (4 : ℕ)) + (17265 / 2048 : ℝ) * (σ ^ (6 : ℕ) * t ^ (4 : ℕ)) + (4125 / 1024 : ℝ) * (σ ^ (7 : ℕ) * t ^ (4 : ℕ)) + (3825 / 2048 : ℝ) * (σ ^ (9 : ℕ) * t ^ (0 : ℕ)) + (225 / 2048 : ℝ) * (σ ^ (11 : ℕ) * t ^ (0 : ℕ))

theorem skewTiltSumPart3_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltSumPart3 σ t ≤ (251167 / 4096 : ℝ) * t ^ (10 : ℕ) := by
  unfold skewTiltSumPart3
  have hb_0_4 : (-483 / 32 : ℝ) * (σ ^ (0 : ℕ) * t ^ (4 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-483 / 32 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 4)
    rw [zero_mul] at this
    exact this
  have hb_1_0 : (-1173 / 128 : ℝ) * (σ ^ (1 : ℕ) * t ^ (0 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1173 / 128 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 0)
    rw [zero_mul] at this
    exact this
  have hb_1_8 : (-1035 / 2048 : ℝ) * (σ ^ (1 : ℕ) * t ^ (8 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1035 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 8)
    rw [zero_mul] at this
    exact this
  have hb_2_4 : (164021 / 4096 : ℝ) * (σ ^ (2 : ℕ) * t ^ (4 : ℕ)) ≤ (164021 / 4096 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 4 (by norm_num)) (show (0 : ℝ) ≤ (164021 / 4096 : ℝ) by norm_num)
  have hb_3_0 : (1751 / 256 : ℝ) * (σ ^ (3 : ℕ) * t ^ (0 : ℕ)) ≤ (1751 / 256 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 3 0 (by norm_num)) (show (0 : ℝ) ≤ (1751 / 256 : ℝ) by norm_num)
  have hb_3_8 : (-2475 / 2048 : ℝ) * (σ ^ (3 : ℕ) * t ^ (8 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2475 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 8)
    rw [zero_mul] at this
    exact this
  have hb_4_6 : (-84555 / 2048 : ℝ) * (σ ^ (4 : ℕ) * t ^ (6 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-84555 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 6)
    rw [zero_mul] at this
    exact this
  have hb_5_4 : (-40335 / 1024 : ℝ) * (σ ^ (5 : ℕ) * t ^ (4 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-40335 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 4)
    rw [zero_mul] at this
    exact this
  have hb_6_4 : (17265 / 2048 : ℝ) * (σ ^ (6 : ℕ) * t ^ (4 : ℕ)) ≤ (17265 / 2048 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 6 4 (by norm_num)) (show (0 : ℝ) ≤ (17265 / 2048 : ℝ) by norm_num)
  have hb_7_4 : (4125 / 1024 : ℝ) * (σ ^ (7 : ℕ) * t ^ (4 : ℕ)) ≤ (4125 / 1024 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 7 4 (by norm_num)) (show (0 : ℝ) ≤ (4125 / 1024 : ℝ) by norm_num)
  have hb_9_0 : (3825 / 2048 : ℝ) * (σ ^ (9 : ℕ) * t ^ (0 : ℕ)) ≤ (3825 / 2048 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 9 0 (by norm_num)) (show (0 : ℝ) ≤ (3825 / 2048 : ℝ) by norm_num)
  have hb_11_0 : (225 / 2048 : ℝ) * (σ ^ (11 : ℕ) * t ^ (0 : ℕ)) ≤ (225 / 2048 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 11 0 (by norm_num)) (show (0 : ℝ) ≤ (225 / 2048 : ℝ) by norm_num)
  linarith

/-- Group 4 of the lower-order monomials of the summed cofactor. -/
noncomputable def skewTiltSumPart4 (σ t : ℝ) : ℝ := (4935 / 4096 : ℝ) * (σ ^ (0 : ℕ) * t ^ (6 : ℕ)) + (-2317 / 256 : ℝ) * (σ ^ (1 : ℕ) * t ^ (2 : ℕ)) + (-2475 / 2048 : ℝ) * (σ ^ (1 : ℕ) * t ^ (10 : ℕ)) + (-56295 / 512 : ℝ) * (σ ^ (2 : ℕ) * t ^ (6 : ℕ)) + (-26099 / 1024 : ℝ) * (σ ^ (3 : ℕ) * t ^ (2 : ℕ)) + (-1229 / 256 : ℝ) * (σ ^ (4 : ℕ) * t ^ (0 : ℕ)) + (2475 / 4096 : ℝ) * (σ ^ (4 : ℕ) * t ^ (8 : ℕ)) + (7425 / 1024 : ℝ) * (σ ^ (5 : ℕ) * t ^ (6 : ℕ)) + (-2475 / 1024 : ℝ) * (σ ^ (6 : ℕ) * t ^ (6 : ℕ)) + (-7521 / 4096 : ℝ) * (σ ^ (8 : ℕ) * t ^ (0 : ℕ)) + (-6375 / 2048 : ℝ) * (σ ^ (9 : ℕ) * t ^ (2 : ℕ)) + (-75 / 4096 : ℝ) * (σ ^ (12 : ℕ) * t ^ (0 : ℕ))

theorem skewTiltSumPart4_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltSumPart4 σ t ≤ (18555 / 2048 : ℝ) * t ^ (10 : ℕ) := by
  unfold skewTiltSumPart4
  have hb_0_6 : (4935 / 4096 : ℝ) * (σ ^ (0 : ℕ) * t ^ (6 : ℕ)) ≤ (4935 / 4096 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 0 6 (by norm_num)) (show (0 : ℝ) ≤ (4935 / 4096 : ℝ) by norm_num)
  have hb_1_2 : (-2317 / 256 : ℝ) * (σ ^ (1 : ℕ) * t ^ (2 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2317 / 256 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 2)
    rw [zero_mul] at this
    exact this
  have hb_1_10 : (-2475 / 2048 : ℝ) * (σ ^ (1 : ℕ) * t ^ (10 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2475 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 10)
    rw [zero_mul] at this
    exact this
  have hb_2_6 : (-56295 / 512 : ℝ) * (σ ^ (2 : ℕ) * t ^ (6 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-56295 / 512 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 6)
    rw [zero_mul] at this
    exact this
  have hb_3_2 : (-26099 / 1024 : ℝ) * (σ ^ (3 : ℕ) * t ^ (2 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-26099 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 2)
    rw [zero_mul] at this
    exact this
  have hb_4_0 : (-1229 / 256 : ℝ) * (σ ^ (4 : ℕ) * t ^ (0 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-1229 / 256 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 0)
    rw [zero_mul] at this
    exact this
  have hb_4_8 : (2475 / 4096 : ℝ) * (σ ^ (4 : ℕ) * t ^ (8 : ℕ)) ≤ (2475 / 4096 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 4 8 (by norm_num)) (show (0 : ℝ) ≤ (2475 / 4096 : ℝ) by norm_num)
  have hb_5_6 : (7425 / 1024 : ℝ) * (σ ^ (5 : ℕ) * t ^ (6 : ℕ)) ≤ (7425 / 1024 : ℝ) * t ^ (10 : ℕ) :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 5 6 (by norm_num)) (show (0 : ℝ) ≤ (7425 / 1024 : ℝ) by norm_num)
  have hb_6_6 : (-2475 / 1024 : ℝ) * (σ ^ (6 : ℕ) * t ^ (6 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2475 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 6)
    rw [zero_mul] at this
    exact this
  have hb_8_0 : (-7521 / 4096 : ℝ) * (σ ^ (8 : ℕ) * t ^ (0 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-7521 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 0)
    rw [zero_mul] at this
    exact this
  have hb_9_2 : (-6375 / 2048 : ℝ) * (σ ^ (9 : ℕ) * t ^ (2 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-6375 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 9 2)
    rw [zero_mul] at this
    exact this
  have hb_12_0 : (-75 / 4096 : ℝ) * (σ ^ (12 : ℕ) * t ^ (0 : ℕ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-75 / 4096 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 12 0)
    rw [zero_mul] at this
    exact this
  linarith

theorem skewTiltCofactorSum_split (σ t : ℝ) :
    skewTiltCofactorQ σ t + skewTiltCofactor σ t = (-(675 / 4096 : ℝ)) * t ^ (12 : ℕ) + skewTiltSumPart1 σ t + skewTiltSumPart2 σ t + skewTiltSumPart3 σ t + skewTiltSumPart4 σ t := by
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
  have hbig : (1100903 / 2048 : ℝ) * t ^ (10 : ℕ) < (675 / 4096 : ℝ) * t ^ (12 : ℕ) := by
    have : t ^ (12 : ℕ) = t ^ (10 : ℕ) * t ^ (2 : ℕ) := by ring
    rw [this]
    have h10 : 0 < t ^ (10 : ℕ) := pow_pos (by linarith) 10
    have hsq : (58 : ℝ) ^ (2 : ℕ) ≤ t ^ (2 : ℕ) := by nlinarith
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
