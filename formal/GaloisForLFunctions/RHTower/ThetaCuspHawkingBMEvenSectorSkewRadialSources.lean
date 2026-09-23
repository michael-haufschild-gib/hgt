import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewRadialFamilies

/-!
# The two-rate radial current between the `++` and `−−` Laurent responses: source pieces

The current between a single harmonic source jet of the `++` reconstruction at half-rate `s` and a
single source jet of the `−−` reconstruction at half-rate `−3−s` (`evenSector_skewRadRadQQ_*`), expressed
through the atoms of the family module, with closed forms `skewRadQQ_*`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet D4BMScalarLinearEquation
open RHTower.D4BMMixedActionCurrent RHTower.D4BMActionSymplecticForm
noncomputable section

def skewRadQQ_qtr0_qtr0 (s r μ : ℂ) : ℂ := (((-72 : ℂ) * r ^ (3 : ℕ) + (144 : ℂ) * r ^ (5 : ℕ) + (-48 : ℂ) * s * r ^ (3 : ℕ) + (96 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qtr0_qtr0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0' : ℂ) :
    skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr0' * skewRadQQ_qtr0_qtr0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr0_qtr0 skewRadAtom1_qtr0_F0 skewRadAtom1_qtr0_F01 skewRadAtom1_qtr0_F1 skewRadAtom1_qtr0_F2 skewRadAtom1_qtr0_H skewRadAtom1_qtr0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr0_qtr0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0 qtr0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr0 * (skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr0 * Y0 * P * Q) * skewRadAtom1_qtr0_F0_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y1 * P * Q) * skewRadAtom1_qtr0_F01_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y2 * P * Q) * skewRadAtom1_qtr0_F1_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y4 * P * Q) * skewRadAtom1_qtr0_F2_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y6 * P * Q) * skewRadAtom1_qtr0_H_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y7 * P * Q) * skewRadAtom1_qtr0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr0_qtr1 (s r μ : ℂ) : ℂ := (((2 : ℂ) * r ^ (2 : ℕ) + (-12 : ℂ) * r ^ (4 : ℕ) + (18 : ℂ) * r ^ (6 : ℕ) + (-8 : ℂ) * r ^ (8 : ℕ) + (-12 : ℂ) * s * r ^ (4 : ℕ) + (12 : ℂ) * s * r ^ (6 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qtr0_qtr1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1' : ℂ) :
    skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr1' * skewRadQQ_qtr0_qtr1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr0_qtr1 skewRadAtom1_qtr0_F0 skewRadAtom1_qtr0_F01 skewRadAtom1_qtr0_F1 skewRadAtom1_qtr0_F2 skewRadAtom1_qtr0_H skewRadAtom1_qtr0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr0_qtr1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0 qtr1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr0 * (skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr0 * Y0 * P * Q) * skewRadAtom1_qtr0_F0_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y1 * P * Q) * skewRadAtom1_qtr0_F01_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y2 * P * Q) * skewRadAtom1_qtr0_F1_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y4 * P * Q) * skewRadAtom1_qtr0_F2_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y6 * P * Q) * skewRadAtom1_qtr0_H_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y7 * P * Q) * skewRadAtom1_qtr0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr0_qtr2 (s r μ : ℂ) : ℂ := (((1 : ℂ) * r ^ (3 : ℕ) + (-3 : ℂ) * r ^ (5 : ℕ) + (3 : ℂ) * r ^ (7 : ℕ) + (-1 : ℂ) * r ^ (9 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qtr0_qtr2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2' : ℂ) :
    skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr2' * skewRadQQ_qtr0_qtr2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr0_qtr2 skewRadAtom1_qtr0_F0 skewRadAtom1_qtr0_F01 skewRadAtom1_qtr0_F1 skewRadAtom1_qtr0_F2 skewRadAtom1_qtr0_H skewRadAtom1_qtr0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr0_qtr2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0 qtr2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr0 * (skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr0 * Y0 * P * Q) * skewRadAtom1_qtr0_F0_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y1 * P * Q) * skewRadAtom1_qtr0_F01_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y2 * P * Q) * skewRadAtom1_qtr0_F1_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y4 * P * Q) * skewRadAtom1_qtr0_F2_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y6 * P * Q) * skewRadAtom1_qtr0_H_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y7 * P * Q) * skewRadAtom1_qtr0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr0_qt0 (s r μ : ℂ) : ℂ := (((-2 : ℂ) + (1 : ℂ) * μ + (-128 : ℂ) * r ^ (2 : ℕ) + (-2 : ℂ) * r ^ (2 : ℕ) * μ + (262 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * r ^ (4 : ℕ) * μ + (12 : ℂ) * r ^ (6 : ℕ) + (-96 : ℂ) * s * r ^ (2 : ℕ) + (12 : ℂ) * s * r ^ (2 : ℕ) * μ + (168 : ℂ) * s * r ^ (4 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qtr0_qt0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0' : ℂ) :
    skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt0' * skewRadQQ_qtr0_qt0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr0_qt0 skewRadAtom1_qtr0_F0 skewRadAtom1_qtr0_F01 skewRadAtom1_qtr0_F1 skewRadAtom1_qtr0_F2 skewRadAtom1_qtr0_H skewRadAtom1_qtr0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr0_qt0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0 qt0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr0 * (skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr0 * Y0 * P * Q) * skewRadAtom1_qtr0_F0_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y1 * P * Q) * skewRadAtom1_qtr0_F01_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y2 * P * Q) * skewRadAtom1_qtr0_F1_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y4 * P * Q) * skewRadAtom1_qtr0_F2_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y6 * P * Q) * skewRadAtom1_qtr0_H_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y7 * P * Q) * skewRadAtom1_qtr0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr0_qt1 (s r μ : ℂ) : ℂ := (((2 : ℂ) * r + (-1 : ℂ) * r * μ + (-16 : ℂ) * r ^ (3 : ℕ) + (2 : ℂ) * r ^ (3 : ℕ) * μ + (26 : ℂ) * r ^ (5 : ℕ) + (-1 : ℂ) * r ^ (5 : ℕ) * μ + (-12 : ℂ) * r ^ (7 : ℕ) + (-24 : ℂ) * s * r ^ (3 : ℕ) + (24 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qtr0_qt1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1' : ℂ) :
    skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt1' * skewRadQQ_qtr0_qt1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr0_qt1 skewRadAtom1_qtr0_F0 skewRadAtom1_qtr0_F01 skewRadAtom1_qtr0_F1 skewRadAtom1_qtr0_F2 skewRadAtom1_qtr0_H skewRadAtom1_qtr0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr0_qt1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0 qt1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr0 * (skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr0 * Y0 * P * Q) * skewRadAtom1_qtr0_F0_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y1 * P * Q) * skewRadAtom1_qtr0_F01_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y2 * P * Q) * skewRadAtom1_qtr0_F1_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y4 * P * Q) * skewRadAtom1_qtr0_F2_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y6 * P * Q) * skewRadAtom1_qtr0_H_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y7 * P * Q) * skewRadAtom1_qtr0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr0_qt2 (s r μ : ℂ) : ℂ := (((2 : ℂ) * r ^ (2 : ℕ) + (-6 : ℂ) * r ^ (4 : ℕ) + (6 : ℂ) * r ^ (6 : ℕ) + (-2 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qtr0_qt2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2' : ℂ) :
    skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt2' * skewRadQQ_qtr0_qt2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr0_qt2 skewRadAtom1_qtr0_F0 skewRadAtom1_qtr0_F01 skewRadAtom1_qtr0_F1 skewRadAtom1_qtr0_F2 skewRadAtom1_qtr0_H skewRadAtom1_qtr0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr0_qt2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0 qt2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr0 * (skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr0 * Y0 * P * Q) * skewRadAtom1_qtr0_F0_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y1 * P * Q) * skewRadAtom1_qtr0_F01_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y2 * P * Q) * skewRadAtom1_qtr0_F1_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y4 * P * Q) * skewRadAtom1_qtr0_F2_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y6 * P * Q) * skewRadAtom1_qtr0_H_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y7 * P * Q) * skewRadAtom1_qtr0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr0_qT0 (s r μ : ℂ) : ℂ := (((6 : ℂ) + (-3 : ℂ) * μ + (262 : ℂ) * r ^ (2 : ℕ) + (-1 : ℂ) * r ^ (2 : ℕ) * μ + (-674 : ℂ) * r ^ (4 : ℕ) + (15 : ℂ) * r ^ (4 : ℕ) * μ + (250 : ℂ) * r ^ (6 : ℕ) + (-11 : ℂ) * r ^ (6 : ℕ) * μ + (12 : ℂ) * r ^ (8 : ℕ) + (216 : ℂ) * s * r ^ (2 : ℕ) + (-36 : ℂ) * s * r ^ (2 : ℕ) * μ + (-432 : ℂ) * s * r ^ (4 : ℕ) + (36 : ℂ) * s * r ^ (4 : ℕ) * μ + (168 : ℂ) * s * r ^ (6 : ℕ) + (16 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-16 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (8 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ) / ((r ^ (2 : ℕ) - 1) * (2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qtr0_qT0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0' : ℂ) :
    skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) = qT0' * skewRadQQ_qtr0_qT0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr0_qT0 skewRadAtom1_qtr0_F0 skewRadAtom1_qtr0_F01 skewRadAtom1_qtr0_F1 skewRadAtom1_qtr0_F2 skewRadAtom1_qtr0_H skewRadAtom1_qtr0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr0_qT0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0 qT0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr0 * (skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr0 * Y0 * P * Q) * skewRadAtom1_qtr0_F0_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y1 * P * Q) * skewRadAtom1_qtr0_F01_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y2 * P * Q) * skewRadAtom1_qtr0_F1_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y4 * P * Q) * skewRadAtom1_qtr0_F2_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y6 * P * Q) * skewRadAtom1_qtr0_H_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y7 * P * Q) * skewRadAtom1_qtr0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr0_qT1 (s r μ : ℂ) : ℂ := (((6 : ℂ) * r + (-3 : ℂ) * r * μ + (-168 : ℂ) * r ^ (3 : ℕ) + (4 : ℂ) * r ^ (3 : ℕ) * μ + (318 : ℂ) * r ^ (5 : ℕ) + (-1 : ℂ) * r ^ (5 : ℕ) * μ + (-12 : ℂ) * r ^ (7 : ℕ) + (-144 : ℂ) * s * r ^ (3 : ℕ) + (216 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qtr0_qT1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1' : ℂ) :
    skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) = qT1' * skewRadQQ_qtr0_qT1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr0_qT1 skewRadAtom1_qtr0_F0 skewRadAtom1_qtr0_F01 skewRadAtom1_qtr0_F1 skewRadAtom1_qtr0_F2 skewRadAtom1_qtr0_H skewRadAtom1_qtr0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr0_qT1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0 qT1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr0 * (skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr0 * Y0 * P * Q) * skewRadAtom1_qtr0_F0_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y1 * P * Q) * skewRadAtom1_qtr0_F01_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y2 * P * Q) * skewRadAtom1_qtr0_F1_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y4 * P * Q) * skewRadAtom1_qtr0_F2_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y6 * P * Q) * skewRadAtom1_qtr0_H_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y7 * P * Q) * skewRadAtom1_qtr0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr0_qT2 (s r μ : ℂ) : ℂ := (((8 : ℂ) * r ^ (2 : ℕ) + (-34 : ℂ) * r ^ (4 : ℕ) + (44 : ℂ) * r ^ (6 : ℕ) + (-18 : ℂ) * r ^ (8 : ℕ) + (-24 : ℂ) * s * r ^ (4 : ℕ) + (24 : ℂ) * s * r ^ (6 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qtr0_qT2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2' : ℂ) :
    skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) = qT2' * skewRadQQ_qtr0_qT2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr0_qT2 skewRadAtom1_qtr0_F0 skewRadAtom1_qtr0_F01 skewRadAtom1_qtr0_F1 skewRadAtom1_qtr0_F2 skewRadAtom1_qtr0_H skewRadAtom1_qtr0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr0_qT2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0 qT2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr0 * (skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr0 * Y0 * P * Q) * skewRadAtom1_qtr0_F0_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y1 * P * Q) * skewRadAtom1_qtr0_F01_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y2 * P * Q) * skewRadAtom1_qtr0_F1_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y4 * P * Q) * skewRadAtom1_qtr0_F2_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y6 * P * Q) * skewRadAtom1_qtr0_H_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y7 * P * Q) * skewRadAtom1_qtr0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr0_qT3 (s r μ : ℂ) : ℂ := (((2 : ℂ) * r ^ (3 : ℕ) + (-6 : ℂ) * r ^ (5 : ℕ) + (6 : ℂ) * r ^ (7 : ℕ) + (-2 : ℂ) * r ^ (9 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qtr0_qT3_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3' : ℂ) :
    skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) = qT3' * skewRadQQ_qtr0_qT3 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr0_qT3 skewRadAtom1_qtr0_F0 skewRadAtom1_qtr0_F01 skewRadAtom1_qtr0_F1 skewRadAtom1_qtr0_F2 skewRadAtom1_qtr0_H skewRadAtom1_qtr0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr0_qT3 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0 qT3' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 qtr0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr0 * (skewRadAtom1_qtr0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr0 * Y0 * P * Q) * skewRadAtom1_qtr0_F0_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y1 * P * Q) * skewRadAtom1_qtr0_F01_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y2 * P * Q) * skewRadAtom1_qtr0_F1_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y4 * P * Q) * skewRadAtom1_qtr0_F2_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y6 * P * Q) * skewRadAtom1_qtr0_H_eq s r μ hr hf hμ hs hs3 + (qtr0 * Y7 * P * Q) * skewRadAtom1_qtr0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr1_qtr0 (s r μ : ℂ) : ℂ := (((-2 : ℂ) * r ^ (2 : ℕ) + (-24 : ℂ) * r ^ (4 : ℕ) + (18 : ℂ) * r ^ (6 : ℕ) + (8 : ℂ) * r ^ (8 : ℕ) + (-12 : ℂ) * s * r ^ (4 : ℕ) + (12 : ℂ) * s * r ^ (6 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qtr1_qtr0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0' : ℂ) :
    skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr0' * skewRadQQ_qtr1_qtr0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr1_qtr0 skewRadAtom1_qtr1_F1 skewRadAtom1_qtr1_F2 skewRadAtom1_qtr1_H skewRadAtom1_qtr1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr1_qtr0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1 qtr0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr1 * (skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr1 * Y2 * P * Q) * skewRadAtom1_qtr1_F1_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y4 * P * Q) * skewRadAtom1_qtr1_F2_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y6 * P * Q) * skewRadAtom1_qtr1_H_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y7 * P * Q) * skewRadAtom1_qtr1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr1_qtr1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr1_qtr1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1' : ℂ) :
    skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr1' * skewRadQQ_qtr1_qtr1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr1_qtr1 skewRadAtom1_qtr1_F1 skewRadAtom1_qtr1_F2 skewRadAtom1_qtr1_H skewRadAtom1_qtr1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr1_qtr1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1 qtr1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr1 * (skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr1 * Y2 * P * Q) * skewRadAtom1_qtr1_F1_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y4 * P * Q) * skewRadAtom1_qtr1_F2_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y6 * P * Q) * skewRadAtom1_qtr1_H_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y7 * P * Q) * skewRadAtom1_qtr1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr1_qtr2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr1_qtr2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2' : ℂ) :
    skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr2' * skewRadQQ_qtr1_qtr2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr1_qtr2 skewRadAtom1_qtr1_F1 skewRadAtom1_qtr1_F2 skewRadAtom1_qtr1_H skewRadAtom1_qtr1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr1_qtr2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1 qtr2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr1 * (skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr1 * Y2 * P * Q) * skewRadAtom1_qtr1_F1_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y4 * P * Q) * skewRadAtom1_qtr1_F2_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y6 * P * Q) * skewRadAtom1_qtr1_H_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y7 * P * Q) * skewRadAtom1_qtr1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr1_qt0 (s r μ : ℂ) : ℂ := (((-6 : ℂ) * r + (1 : ℂ) * r * μ + (-44 : ℂ) * r ^ (3 : ℕ) + (-2 : ℂ) * r ^ (3 : ℕ) * μ + (34 : ℂ) * r ^ (5 : ℕ) + (1 : ℂ) * r ^ (5 : ℕ) * μ + (16 : ℂ) * r ^ (7 : ℕ) + (-24 : ℂ) * s * r ^ (3 : ℕ) + (24 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qtr1_qt0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0' : ℂ) :
    skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt0' * skewRadQQ_qtr1_qt0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr1_qt0 skewRadAtom1_qtr1_F1 skewRadAtom1_qtr1_F2 skewRadAtom1_qtr1_H skewRadAtom1_qtr1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr1_qt0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1 qt0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr1 * (skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr1 * Y2 * P * Q) * skewRadAtom1_qtr1_F1_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y4 * P * Q) * skewRadAtom1_qtr1_F2_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y6 * P * Q) * skewRadAtom1_qtr1_H_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y7 * P * Q) * skewRadAtom1_qtr1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr1_qt1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr1_qt1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1' : ℂ) :
    skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt1' * skewRadQQ_qtr1_qt1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr1_qt1 skewRadAtom1_qtr1_F1 skewRadAtom1_qtr1_F2 skewRadAtom1_qtr1_H skewRadAtom1_qtr1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr1_qt1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1 qt1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr1 * (skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr1 * Y2 * P * Q) * skewRadAtom1_qtr1_F1_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y4 * P * Q) * skewRadAtom1_qtr1_F2_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y6 * P * Q) * skewRadAtom1_qtr1_H_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y7 * P * Q) * skewRadAtom1_qtr1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr1_qt2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr1_qt2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2' : ℂ) :
    skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt2' * skewRadQQ_qtr1_qt2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr1_qt2 skewRadAtom1_qtr1_F1 skewRadAtom1_qtr1_F2 skewRadAtom1_qtr1_H skewRadAtom1_qtr1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr1_qt2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1 qt2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr1 * (skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr1 * Y2 * P * Q) * skewRadAtom1_qtr1_F1_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y4 * P * Q) * skewRadAtom1_qtr1_F2_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y6 * P * Q) * skewRadAtom1_qtr1_H_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y7 * P * Q) * skewRadAtom1_qtr1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr1_qT0 (s r μ : ℂ) : ℂ := (((-6 : ℂ) * r + (-1 : ℂ) * r * μ + (-116 : ℂ) * r ^ (3 : ℕ) + (8 : ℂ) * r ^ (3 : ℕ) * μ + (34 : ℂ) * r ^ (5 : ℕ) + (-7 : ℂ) * r ^ (5 : ℕ) * μ + (16 : ℂ) * r ^ (7 : ℕ) + (-48 : ℂ) * s * r ^ (3 : ℕ) + (24 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qtr1_qT0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0' : ℂ) :
    skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) = qT0' * skewRadQQ_qtr1_qT0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr1_qT0 skewRadAtom1_qtr1_F1 skewRadAtom1_qtr1_F2 skewRadAtom1_qtr1_H skewRadAtom1_qtr1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr1_qT0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1 qT0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr1 * (skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr1 * Y2 * P * Q) * skewRadAtom1_qtr1_F1_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y4 * P * Q) * skewRadAtom1_qtr1_F2_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y6 * P * Q) * skewRadAtom1_qtr1_H_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y7 * P * Q) * skewRadAtom1_qtr1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr1_qT1 (s r μ : ℂ) : ℂ := (((-6 : ℂ) * r ^ (2 : ℕ) + (1 : ℂ) * r ^ (2 : ℕ) * μ + (-44 : ℂ) * r ^ (4 : ℕ) + (-2 : ℂ) * r ^ (4 : ℕ) * μ + (34 : ℂ) * r ^ (6 : ℕ) + (1 : ℂ) * r ^ (6 : ℕ) * μ + (16 : ℂ) * r ^ (8 : ℕ) + (-24 : ℂ) * s * r ^ (4 : ℕ) + (24 : ℂ) * s * r ^ (6 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qtr1_qT1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1' : ℂ) :
    skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) = qT1' * skewRadQQ_qtr1_qT1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr1_qT1 skewRadAtom1_qtr1_F1 skewRadAtom1_qtr1_F2 skewRadAtom1_qtr1_H skewRadAtom1_qtr1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr1_qT1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1 qT1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr1 * (skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr1 * Y2 * P * Q) * skewRadAtom1_qtr1_F1_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y4 * P * Q) * skewRadAtom1_qtr1_F2_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y6 * P * Q) * skewRadAtom1_qtr1_H_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y7 * P * Q) * skewRadAtom1_qtr1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr1_qT2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr1_qT2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2' : ℂ) :
    skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) = qT2' * skewRadQQ_qtr1_qT2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr1_qT2 skewRadAtom1_qtr1_F1 skewRadAtom1_qtr1_F2 skewRadAtom1_qtr1_H skewRadAtom1_qtr1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr1_qT2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1 qT2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr1 * (skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr1 * Y2 * P * Q) * skewRadAtom1_qtr1_F1_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y4 * P * Q) * skewRadAtom1_qtr1_F2_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y6 * P * Q) * skewRadAtom1_qtr1_H_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y7 * P * Q) * skewRadAtom1_qtr1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr1_qT3 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr1_qT3_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3' : ℂ) :
    skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) = qT3' * skewRadQQ_qtr1_qT3 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr1_qT3 skewRadAtom1_qtr1_F1 skewRadAtom1_qtr1_F2 skewRadAtom1_qtr1_H skewRadAtom1_qtr1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr1_qT3 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1 qT3' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr1 * (skewRadAtom1_qtr1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qtr1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr1 * Y2 * P * Q) * skewRadAtom1_qtr1_F1_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y4 * P * Q) * skewRadAtom1_qtr1_F2_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y6 * P * Q) * skewRadAtom1_qtr1_H_eq s r μ hr hf hμ hs hs3 + (qtr1 * Y7 * P * Q) * skewRadAtom1_qtr1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr2_qtr0 (s r μ : ℂ) : ℂ := (((-1 : ℂ) * r ^ (3 : ℕ) + (3 : ℂ) * r ^ (5 : ℕ) + (-3 : ℂ) * r ^ (7 : ℕ) + (1 : ℂ) * r ^ (9 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qtr2_qtr0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0' : ℂ) :
    skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr0' * skewRadQQ_qtr2_qtr0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr2_qtr0 skewRadAtom1_qtr2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr2_qtr0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2 qtr0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr2 * (skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr2 * Y6 * P * Q) * skewRadAtom1_qtr2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr2_qtr1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr2_qtr1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1' : ℂ) :
    skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr1' * skewRadQQ_qtr2_qtr1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr2_qtr1 skewRadAtom1_qtr2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr2_qtr1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2 qtr1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr2 * (skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr2 * Y6 * P * Q) * skewRadAtom1_qtr2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr2_qtr2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr2_qtr2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2' : ℂ) :
    skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr2' * skewRadQQ_qtr2_qtr2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr2_qtr2 skewRadAtom1_qtr2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr2_qtr2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2 qtr2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr2 * (skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr2 * Y6 * P * Q) * skewRadAtom1_qtr2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr2_qt0 (s r μ : ℂ) : ℂ := (((-2 : ℂ) * r ^ (2 : ℕ) + (6 : ℂ) * r ^ (4 : ℕ) + (-6 : ℂ) * r ^ (6 : ℕ) + (2 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qtr2_qt0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0' : ℂ) :
    skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt0' * skewRadQQ_qtr2_qt0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr2_qt0 skewRadAtom1_qtr2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr2_qt0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2 qt0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr2 * (skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr2 * Y6 * P * Q) * skewRadAtom1_qtr2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr2_qt1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr2_qt1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1' : ℂ) :
    skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt1' * skewRadQQ_qtr2_qt1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr2_qt1 skewRadAtom1_qtr2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr2_qt1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2 qt1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr2 * (skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr2 * Y6 * P * Q) * skewRadAtom1_qtr2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr2_qt2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr2_qt2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2' : ℂ) :
    skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt2' * skewRadQQ_qtr2_qt2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr2_qt2 skewRadAtom1_qtr2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr2_qt2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2 qt2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr2 * (skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr2 * Y6 * P * Q) * skewRadAtom1_qtr2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr2_qT0 (s r μ : ℂ) : ℂ := (((-2 : ℂ) * r ^ (2 : ℕ) + (-1 : ℂ) * r ^ (2 : ℕ) * μ + (6 : ℂ) * r ^ (4 : ℕ) + (2 : ℂ) * r ^ (4 : ℕ) * μ + (-6 : ℂ) * r ^ (6 : ℕ) + (-1 : ℂ) * r ^ (6 : ℕ) * μ + (2 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qtr2_qT0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0' : ℂ) :
    skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) = qT0' * skewRadQQ_qtr2_qT0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr2_qT0 skewRadAtom1_qtr2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr2_qT0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2 qT0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr2 * (skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr2 * Y6 * P * Q) * skewRadAtom1_qtr2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr2_qT1 (s r μ : ℂ) : ℂ := (((-2 : ℂ) * r ^ (3 : ℕ) + (6 : ℂ) * r ^ (5 : ℕ) + (-6 : ℂ) * r ^ (7 : ℕ) + (2 : ℂ) * r ^ (9 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qtr2_qT1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1' : ℂ) :
    skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) = qT1' * skewRadQQ_qtr2_qT1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr2_qT1 skewRadAtom1_qtr2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr2_qT1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2 qT1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr2 * (skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr2 * Y6 * P * Q) * skewRadAtom1_qtr2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr2_qT2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr2_qT2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2' : ℂ) :
    skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) = qT2' * skewRadQQ_qtr2_qT2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr2_qT2 skewRadAtom1_qtr2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr2_qT2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2 qT2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr2 * (skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr2 * Y6 * P * Q) * skewRadAtom1_qtr2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qtr2_qT3 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qtr2_qT3_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3' : ℂ) :
    skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) = qT3' * skewRadQQ_qtr2_qT3 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qtr2_qT3 skewRadAtom1_qtr2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qtr2_qT3 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2 qT3' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qtr2 * (skewRadAtom1_qtr2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qtr2 * Y6 * P * Q) * skewRadAtom1_qtr2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt0_qtr0 (s r μ : ℂ) : ℂ := (((2 : ℂ) + (-1 : ℂ) * μ + (-160 : ℂ) * r ^ (2 : ℕ) + (38 : ℂ) * r ^ (2 : ℕ) * μ + (242 : ℂ) * r ^ (4 : ℕ) + (-1 : ℂ) * r ^ (4 : ℕ) * μ + (-12 : ℂ) * r ^ (6 : ℕ) + (-96 : ℂ) * s * r ^ (2 : ℕ) + (12 : ℂ) * s * r ^ (2 : ℕ) * μ + (168 : ℂ) * s * r ^ (4 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qt0_qtr0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0' : ℂ) :
    skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr0' * skewRadQQ_qt0_qtr0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt0_qtr0 skewRadAtom1_qt0_F0 skewRadAtom1_qt0_F01 skewRadAtom1_qt0_F1 skewRadAtom1_qt0_F2 skewRadAtom1_qt0_H skewRadAtom1_qt0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt0_qtr0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0 qtr0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt0 * (skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt0 * Y0 * P * Q) * skewRadAtom1_qt0_F0_eq s r μ hr hf hμ hs hs3 + (qt0 * Y1 * P * Q) * skewRadAtom1_qt0_F01_eq s r μ hr hf hμ hs hs3 + (qt0 * Y2 * P * Q) * skewRadAtom1_qt0_F1_eq s r μ hr hf hμ hs hs3 + (qt0 * Y4 * P * Q) * skewRadAtom1_qt0_F2_eq s r μ hr hf hμ hs hs3 + (qt0 * Y6 * P * Q) * skewRadAtom1_qt0_H_eq s r μ hr hf hμ hs hs3 + (qt0 * Y7 * P * Q) * skewRadAtom1_qt0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt0_qtr1 (s r μ : ℂ) : ℂ := (((6 : ℂ) * r + (-1 : ℂ) * r * μ + (-28 : ℂ) * r ^ (3 : ℕ) + (2 : ℂ) * r ^ (3 : ℕ) * μ + (38 : ℂ) * r ^ (5 : ℕ) + (-1 : ℂ) * r ^ (5 : ℕ) * μ + (-16 : ℂ) * r ^ (7 : ℕ) + (-24 : ℂ) * s * r ^ (3 : ℕ) + (24 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qt0_qtr1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1' : ℂ) :
    skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr1' * skewRadQQ_qt0_qtr1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt0_qtr1 skewRadAtom1_qt0_F0 skewRadAtom1_qt0_F01 skewRadAtom1_qt0_F1 skewRadAtom1_qt0_F2 skewRadAtom1_qt0_H skewRadAtom1_qt0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt0_qtr1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0 qtr1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt0 * (skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt0 * Y0 * P * Q) * skewRadAtom1_qt0_F0_eq s r μ hr hf hμ hs hs3 + (qt0 * Y1 * P * Q) * skewRadAtom1_qt0_F01_eq s r μ hr hf hμ hs hs3 + (qt0 * Y2 * P * Q) * skewRadAtom1_qt0_F1_eq s r μ hr hf hμ hs hs3 + (qt0 * Y4 * P * Q) * skewRadAtom1_qt0_F2_eq s r μ hr hf hμ hs hs3 + (qt0 * Y6 * P * Q) * skewRadAtom1_qt0_H_eq s r μ hr hf hμ hs hs3 + (qt0 * Y7 * P * Q) * skewRadAtom1_qt0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt0_qtr2 (s r μ : ℂ) : ℂ := (((2 : ℂ) * r ^ (2 : ℕ) + (-6 : ℂ) * r ^ (4 : ℕ) + (6 : ℂ) * r ^ (6 : ℕ) + (-2 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qt0_qtr2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2' : ℂ) :
    skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr2' * skewRadQQ_qt0_qtr2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt0_qtr2 skewRadAtom1_qt0_F0 skewRadAtom1_qt0_F01 skewRadAtom1_qt0_F1 skewRadAtom1_qt0_F2 skewRadAtom1_qt0_H skewRadAtom1_qt0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt0_qtr2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0 qtr2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt0 * (skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt0 * Y0 * P * Q) * skewRadAtom1_qt0_F0_eq s r μ hr hf hμ hs hs3 + (qt0 * Y1 * P * Q) * skewRadAtom1_qt0_F01_eq s r μ hr hf hμ hs hs3 + (qt0 * Y2 * P * Q) * skewRadAtom1_qt0_F1_eq s r μ hr hf hμ hs hs3 + (qt0 * Y4 * P * Q) * skewRadAtom1_qt0_F2_eq s r μ hr hf hμ hs hs3 + (qt0 * Y6 * P * Q) * skewRadAtom1_qt0_H_eq s r μ hr hf hμ hs hs3 + (qt0 * Y7 * P * Q) * skewRadAtom1_qt0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt0_qt0 (s r μ : ℂ) : ℂ := (((-288 : ℂ) * r + (72 : ℂ) * r * μ + (432 : ℂ) * r ^ (3 : ℕ) + (-192 : ℂ) * s * r + (48 : ℂ) * s * r * μ + (288 : ℂ) * s * r ^ (3 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qt0_qt0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0' : ℂ) :
    skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt0' * skewRadQQ_qt0_qt0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt0_qt0 skewRadAtom1_qt0_F0 skewRadAtom1_qt0_F01 skewRadAtom1_qt0_F1 skewRadAtom1_qt0_F2 skewRadAtom1_qt0_H skewRadAtom1_qt0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt0_qt0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0 qt0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt0 * (skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt0 * Y0 * P * Q) * skewRadAtom1_qt0_F0_eq s r μ hr hf hμ hs hs3 + (qt0 * Y1 * P * Q) * skewRadAtom1_qt0_F01_eq s r μ hr hf hμ hs hs3 + (qt0 * Y2 * P * Q) * skewRadAtom1_qt0_F1_eq s r μ hr hf hμ hs hs3 + (qt0 * Y4 * P * Q) * skewRadAtom1_qt0_F2_eq s r μ hr hf hμ hs hs3 + (qt0 * Y6 * P * Q) * skewRadAtom1_qt0_H_eq s r μ hr hf hμ hs hs3 + (qt0 * Y7 * P * Q) * skewRadAtom1_qt0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt0_qt1 (s r μ : ℂ) : ℂ := (((8 : ℂ) + (-4 : ℂ) * μ + (-40 : ℂ) * r ^ (2 : ℕ) + (8 : ℂ) * r ^ (2 : ℕ) * μ + (56 : ℂ) * r ^ (4 : ℕ) + (-4 : ℂ) * r ^ (4 : ℕ) * μ + (-24 : ℂ) * r ^ (6 : ℕ) + (-48 : ℂ) * s * r ^ (2 : ℕ) + (48 : ℂ) * s * r ^ (4 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qt0_qt1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1' : ℂ) :
    skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt1' * skewRadQQ_qt0_qt1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt0_qt1 skewRadAtom1_qt0_F0 skewRadAtom1_qt0_F01 skewRadAtom1_qt0_F1 skewRadAtom1_qt0_F2 skewRadAtom1_qt0_H skewRadAtom1_qt0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt0_qt1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0 qt1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt0 * (skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt0 * Y0 * P * Q) * skewRadAtom1_qt0_F0_eq s r μ hr hf hμ hs hs3 + (qt0 * Y1 * P * Q) * skewRadAtom1_qt0_F01_eq s r μ hr hf hμ hs hs3 + (qt0 * Y2 * P * Q) * skewRadAtom1_qt0_F1_eq s r μ hr hf hμ hs hs3 + (qt0 * Y4 * P * Q) * skewRadAtom1_qt0_F2_eq s r μ hr hf hμ hs hs3 + (qt0 * Y6 * P * Q) * skewRadAtom1_qt0_H_eq s r μ hr hf hμ hs hs3 + (qt0 * Y7 * P * Q) * skewRadAtom1_qt0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt0_qt2 (s r μ : ℂ) : ℂ := (((4 : ℂ) * r + (-12 : ℂ) * r ^ (3 : ℕ) + (12 : ℂ) * r ^ (5 : ℕ) + (-4 : ℂ) * r ^ (7 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qt0_qt2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2' : ℂ) :
    skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt2' * skewRadQQ_qt0_qt2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt0_qt2 skewRadAtom1_qt0_F0 skewRadAtom1_qt0_F01 skewRadAtom1_qt0_F1 skewRadAtom1_qt0_F2 skewRadAtom1_qt0_H skewRadAtom1_qt0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt0_qt2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0 qt2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt0 * (skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt0 * Y0 * P * Q) * skewRadAtom1_qt0_F0_eq s r μ hr hf hμ hs hs3 + (qt0 * Y1 * P * Q) * skewRadAtom1_qt0_F01_eq s r μ hr hf hμ hs hs3 + (qt0 * Y2 * P * Q) * skewRadAtom1_qt0_F1_eq s r μ hr hf hμ hs hs3 + (qt0 * Y4 * P * Q) * skewRadAtom1_qt0_F2_eq s r μ hr hf hμ hs hs3 + (qt0 * Y6 * P * Q) * skewRadAtom1_qt0_H_eq s r μ hr hf hμ hs hs3 + (qt0 * Y7 * P * Q) * skewRadAtom1_qt0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt0_qT0 (s r μ : ℂ) : ℂ := (((4 : ℂ) * μ + (-2 : ℂ) * μ ^ (2 : ℕ) + (576 : ℂ) * r ^ (2 : ℕ) + (-160 : ℂ) * r ^ (2 : ℕ) * μ + (6 : ℂ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-1152 : ℂ) * r ^ (4 : ℕ) + (96 : ℂ) * r ^ (4 : ℕ) * μ + (-4 : ℂ) * r ^ (4 : ℕ) * μ ^ (2 : ℕ) + (432 : ℂ) * r ^ (6 : ℕ) + (-12 : ℂ) * r ^ (6 : ℕ) * μ + (432 : ℂ) * s * r ^ (2 : ℕ) + (-120 : ℂ) * s * r ^ (2 : ℕ) * μ + (-768 : ℂ) * s * r ^ (4 : ℕ) + (96 : ℂ) * s * r ^ (4 : ℕ) * μ + (288 : ℂ) * s * r ^ (6 : ℕ) + (32 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-16 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-32 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (16 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ) / (r * (r ^ (2 : ℕ) - 1) * (2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qt0_qT0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0' : ℂ) :
    skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) = qT0' * skewRadQQ_qt0_qT0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt0_qT0 skewRadAtom1_qt0_F0 skewRadAtom1_qt0_F01 skewRadAtom1_qt0_F1 skewRadAtom1_qt0_F2 skewRadAtom1_qt0_H skewRadAtom1_qt0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt0_qT0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0 qT0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt0 * (skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt0 * Y0 * P * Q) * skewRadAtom1_qt0_F0_eq s r μ hr hf hμ hs hs3 + (qt0 * Y1 * P * Q) * skewRadAtom1_qt0_F01_eq s r μ hr hf hμ hs hs3 + (qt0 * Y2 * P * Q) * skewRadAtom1_qt0_F1_eq s r μ hr hf hμ hs hs3 + (qt0 * Y4 * P * Q) * skewRadAtom1_qt0_F2_eq s r μ hr hf hμ hs hs3 + (qt0 * Y6 * P * Q) * skewRadAtom1_qt0_H_eq s r μ hr hf hμ hs hs3 + (qt0 * Y7 * P * Q) * skewRadAtom1_qt0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt0_qT1 (s r μ : ℂ) : ℂ := (((24 : ℂ) + (-10 : ℂ) * μ + (-1 : ℂ) * μ ^ (2 : ℕ) + (-384 : ℂ) * r ^ (2 : ℕ) + (90 : ℂ) * r ^ (2 : ℕ) * μ + (1 : ℂ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (552 : ℂ) * r ^ (4 : ℕ) + (-8 : ℂ) * r ^ (4 : ℕ) * μ + (-48 : ℂ) * r ^ (6 : ℕ) + (-288 : ℂ) * s * r ^ (2 : ℕ) + (24 : ℂ) * s * r ^ (2 : ℕ) * μ + (384 : ℂ) * s * r ^ (4 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qt0_qT1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1' : ℂ) :
    skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) = qT1' * skewRadQQ_qt0_qT1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt0_qT1 skewRadAtom1_qt0_F0 skewRadAtom1_qt0_F01 skewRadAtom1_qt0_F1 skewRadAtom1_qt0_F2 skewRadAtom1_qt0_H skewRadAtom1_qt0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt0_qT1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0 qT1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt0 * (skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt0 * Y0 * P * Q) * skewRadAtom1_qt0_F0_eq s r μ hr hf hμ hs hs3 + (qt0 * Y1 * P * Q) * skewRadAtom1_qt0_F01_eq s r μ hr hf hμ hs hs3 + (qt0 * Y2 * P * Q) * skewRadAtom1_qt0_F1_eq s r μ hr hf hμ hs hs3 + (qt0 * Y4 * P * Q) * skewRadAtom1_qt0_F2_eq s r μ hr hf hμ hs hs3 + (qt0 * Y6 * P * Q) * skewRadAtom1_qt0_H_eq s r μ hr hf hμ hs hs3 + (qt0 * Y7 * P * Q) * skewRadAtom1_qt0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt0_qT2 (s r μ : ℂ) : ℂ := (((20 : ℂ) * r + (-2 : ℂ) * r * μ + (-76 : ℂ) * r ^ (3 : ℕ) + (4 : ℂ) * r ^ (3 : ℕ) * μ + (92 : ℂ) * r ^ (5 : ℕ) + (-2 : ℂ) * r ^ (5 : ℕ) * μ + (-36 : ℂ) * r ^ (7 : ℕ) + (-48 : ℂ) * s * r ^ (3 : ℕ) + (48 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qt0_qT2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2' : ℂ) :
    skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) = qT2' * skewRadQQ_qt0_qT2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt0_qT2 skewRadAtom1_qt0_F0 skewRadAtom1_qt0_F01 skewRadAtom1_qt0_F1 skewRadAtom1_qt0_F2 skewRadAtom1_qt0_H skewRadAtom1_qt0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt0_qT2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0 qT2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt0 * (skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt0 * Y0 * P * Q) * skewRadAtom1_qt0_F0_eq s r μ hr hf hμ hs hs3 + (qt0 * Y1 * P * Q) * skewRadAtom1_qt0_F01_eq s r μ hr hf hμ hs hs3 + (qt0 * Y2 * P * Q) * skewRadAtom1_qt0_F1_eq s r μ hr hf hμ hs hs3 + (qt0 * Y4 * P * Q) * skewRadAtom1_qt0_F2_eq s r μ hr hf hμ hs hs3 + (qt0 * Y6 * P * Q) * skewRadAtom1_qt0_H_eq s r μ hr hf hμ hs hs3 + (qt0 * Y7 * P * Q) * skewRadAtom1_qt0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt0_qT3 (s r μ : ℂ) : ℂ := (((4 : ℂ) * r ^ (2 : ℕ) + (-12 : ℂ) * r ^ (4 : ℕ) + (12 : ℂ) * r ^ (6 : ℕ) + (-4 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qt0_qT3_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3' : ℂ) :
    skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) = qT3' * skewRadQQ_qt0_qT3 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt0_qT3 skewRadAtom1_qt0_F0 skewRadAtom1_qt0_F01 skewRadAtom1_qt0_F1 skewRadAtom1_qt0_F2 skewRadAtom1_qt0_H skewRadAtom1_qt0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt0_qT3 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0 qT3' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt0 * (skewRadAtom1_qt0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt0 * Y0 * P * Q) * skewRadAtom1_qt0_F0_eq s r μ hr hf hμ hs hs3 + (qt0 * Y1 * P * Q) * skewRadAtom1_qt0_F01_eq s r μ hr hf hμ hs hs3 + (qt0 * Y2 * P * Q) * skewRadAtom1_qt0_F1_eq s r μ hr hf hμ hs hs3 + (qt0 * Y4 * P * Q) * skewRadAtom1_qt0_F2_eq s r μ hr hf hμ hs hs3 + (qt0 * Y6 * P * Q) * skewRadAtom1_qt0_H_eq s r μ hr hf hμ hs hs3 + (qt0 * Y7 * P * Q) * skewRadAtom1_qt0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt1_qtr0 (s r μ : ℂ) : ℂ := (((-2 : ℂ) * r + (1 : ℂ) * r * μ + (-56 : ℂ) * r ^ (3 : ℕ) + (-2 : ℂ) * r ^ (3 : ℕ) * μ + (46 : ℂ) * r ^ (5 : ℕ) + (1 : ℂ) * r ^ (5 : ℕ) * μ + (12 : ℂ) * r ^ (7 : ℕ) + (-24 : ℂ) * s * r ^ (3 : ℕ) + (24 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qt1_qtr0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0' : ℂ) :
    skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr0' * skewRadQQ_qt1_qtr0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt1_qtr0 skewRadAtom1_qt1_F1 skewRadAtom1_qt1_F2 skewRadAtom1_qt1_H skewRadAtom1_qt1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt1_qtr0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1 qtr0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt1 * (skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt1 * Y2 * P * Q) * skewRadAtom1_qt1_F1_eq s r μ hr hf hμ hs hs3 + (qt1 * Y4 * P * Q) * skewRadAtom1_qt1_F2_eq s r μ hr hf hμ hs hs3 + (qt1 * Y6 * P * Q) * skewRadAtom1_qt1_H_eq s r μ hr hf hμ hs hs3 + (qt1 * Y7 * P * Q) * skewRadAtom1_qt1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt1_qtr1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt1_qtr1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1' : ℂ) :
    skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr1' * skewRadQQ_qt1_qtr1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt1_qtr1 skewRadAtom1_qt1_F1 skewRadAtom1_qt1_F2 skewRadAtom1_qt1_H skewRadAtom1_qt1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt1_qtr1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1 qtr1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt1 * (skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt1 * Y2 * P * Q) * skewRadAtom1_qt1_F1_eq s r μ hr hf hμ hs hs3 + (qt1 * Y4 * P * Q) * skewRadAtom1_qt1_F2_eq s r μ hr hf hμ hs hs3 + (qt1 * Y6 * P * Q) * skewRadAtom1_qt1_H_eq s r μ hr hf hμ hs hs3 + (qt1 * Y7 * P * Q) * skewRadAtom1_qt1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt1_qtr2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt1_qtr2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2' : ℂ) :
    skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr2' * skewRadQQ_qt1_qtr2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt1_qtr2 skewRadAtom1_qt1_F1 skewRadAtom1_qt1_F2 skewRadAtom1_qt1_H skewRadAtom1_qt1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt1_qtr2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1 qtr2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt1 * (skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt1 * Y2 * P * Q) * skewRadAtom1_qt1_F1_eq s r μ hr hf hμ hs hs3 + (qt1 * Y4 * P * Q) * skewRadAtom1_qt1_F2_eq s r μ hr hf hμ hs hs3 + (qt1 * Y6 * P * Q) * skewRadAtom1_qt1_H_eq s r μ hr hf hμ hs hs3 + (qt1 * Y7 * P * Q) * skewRadAtom1_qt1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt1_qt0 (s r μ : ℂ) : ℂ := (((-8 : ℂ) + (4 : ℂ) * μ + (-104 : ℂ) * r ^ (2 : ℕ) + (-8 : ℂ) * r ^ (2 : ℕ) * μ + (88 : ℂ) * r ^ (4 : ℕ) + (4 : ℂ) * r ^ (4 : ℕ) * μ + (24 : ℂ) * r ^ (6 : ℕ) + (-48 : ℂ) * s * r ^ (2 : ℕ) + (48 : ℂ) * s * r ^ (4 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qt1_qt0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0' : ℂ) :
    skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt0' * skewRadQQ_qt1_qt0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt1_qt0 skewRadAtom1_qt1_F1 skewRadAtom1_qt1_F2 skewRadAtom1_qt1_H skewRadAtom1_qt1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt1_qt0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1 qt0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt1 * (skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt1 * Y2 * P * Q) * skewRadAtom1_qt1_F1_eq s r μ hr hf hμ hs hs3 + (qt1 * Y4 * P * Q) * skewRadAtom1_qt1_F2_eq s r μ hr hf hμ hs hs3 + (qt1 * Y6 * P * Q) * skewRadAtom1_qt1_H_eq s r μ hr hf hμ hs hs3 + (qt1 * Y7 * P * Q) * skewRadAtom1_qt1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt1_qt1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt1_qt1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1' : ℂ) :
    skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt1' * skewRadQQ_qt1_qt1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt1_qt1 skewRadAtom1_qt1_F1 skewRadAtom1_qt1_F2 skewRadAtom1_qt1_H skewRadAtom1_qt1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt1_qt1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1 qt1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt1 * (skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt1 * Y2 * P * Q) * skewRadAtom1_qt1_F1_eq s r μ hr hf hμ hs hs3 + (qt1 * Y4 * P * Q) * skewRadAtom1_qt1_F2_eq s r μ hr hf hμ hs hs3 + (qt1 * Y6 * P * Q) * skewRadAtom1_qt1_H_eq s r μ hr hf hμ hs hs3 + (qt1 * Y7 * P * Q) * skewRadAtom1_qt1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt1_qt2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt1_qt2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2' : ℂ) :
    skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt2' * skewRadQQ_qt1_qt2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt1_qt2 skewRadAtom1_qt1_F1 skewRadAtom1_qt1_F2 skewRadAtom1_qt1_H skewRadAtom1_qt1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt1_qt2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1 qt2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt1 * (skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt1 * Y2 * P * Q) * skewRadAtom1_qt1_F1_eq s r μ hr hf hμ hs hs3 + (qt1 * Y4 * P * Q) * skewRadAtom1_qt1_F2_eq s r μ hr hf hμ hs hs3 + (qt1 * Y6 * P * Q) * skewRadAtom1_qt1_H_eq s r μ hr hf hμ hs hs3 + (qt1 * Y7 * P * Q) * skewRadAtom1_qt1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt1_qT0 (s r μ : ℂ) : ℂ := (((-8 : ℂ) + (2 : ℂ) * μ + (1 : ℂ) * μ ^ (2 : ℕ) + (-248 : ℂ) * r ^ (2 : ℕ) + (6 : ℂ) * r ^ (2 : ℕ) * μ + (-1 : ℂ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (88 : ℂ) * r ^ (4 : ℕ) + (-8 : ℂ) * r ^ (4 : ℕ) * μ + (24 : ℂ) * r ^ (6 : ℕ) + (-96 : ℂ) * s * r ^ (2 : ℕ) + (48 : ℂ) * s * r ^ (4 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qt1_qT0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0' : ℂ) :
    skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) = qT0' * skewRadQQ_qt1_qT0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt1_qT0 skewRadAtom1_qt1_F1 skewRadAtom1_qt1_F2 skewRadAtom1_qt1_H skewRadAtom1_qt1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt1_qT0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1 qT0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt1 * (skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt1 * Y2 * P * Q) * skewRadAtom1_qt1_F1_eq s r μ hr hf hμ hs hs3 + (qt1 * Y4 * P * Q) * skewRadAtom1_qt1_F2_eq s r μ hr hf hμ hs hs3 + (qt1 * Y6 * P * Q) * skewRadAtom1_qt1_H_eq s r μ hr hf hμ hs hs3 + (qt1 * Y7 * P * Q) * skewRadAtom1_qt1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt1_qT1 (s r μ : ℂ) : ℂ := (((-8 : ℂ) * r + (4 : ℂ) * r * μ + (-104 : ℂ) * r ^ (3 : ℕ) + (-8 : ℂ) * r ^ (3 : ℕ) * μ + (88 : ℂ) * r ^ (5 : ℕ) + (4 : ℂ) * r ^ (5 : ℕ) * μ + (24 : ℂ) * r ^ (7 : ℕ) + (-48 : ℂ) * s * r ^ (3 : ℕ) + (48 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qt1_qT1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1' : ℂ) :
    skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) = qT1' * skewRadQQ_qt1_qT1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt1_qT1 skewRadAtom1_qt1_F1 skewRadAtom1_qt1_F2 skewRadAtom1_qt1_H skewRadAtom1_qt1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt1_qT1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1 qT1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt1 * (skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt1 * Y2 * P * Q) * skewRadAtom1_qt1_F1_eq s r μ hr hf hμ hs hs3 + (qt1 * Y4 * P * Q) * skewRadAtom1_qt1_F2_eq s r μ hr hf hμ hs hs3 + (qt1 * Y6 * P * Q) * skewRadAtom1_qt1_H_eq s r μ hr hf hμ hs hs3 + (qt1 * Y7 * P * Q) * skewRadAtom1_qt1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt1_qT2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt1_qT2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2' : ℂ) :
    skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) = qT2' * skewRadQQ_qt1_qT2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt1_qT2 skewRadAtom1_qt1_F1 skewRadAtom1_qt1_F2 skewRadAtom1_qt1_H skewRadAtom1_qt1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt1_qT2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1 qT2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt1 * (skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt1 * Y2 * P * Q) * skewRadAtom1_qt1_F1_eq s r μ hr hf hμ hs hs3 + (qt1 * Y4 * P * Q) * skewRadAtom1_qt1_F2_eq s r μ hr hf hμ hs hs3 + (qt1 * Y6 * P * Q) * skewRadAtom1_qt1_H_eq s r μ hr hf hμ hs hs3 + (qt1 * Y7 * P * Q) * skewRadAtom1_qt1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt1_qT3 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt1_qT3_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3' : ℂ) :
    skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) = qT3' * skewRadQQ_qt1_qT3 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt1_qT3 skewRadAtom1_qt1_F1 skewRadAtom1_qt1_F2 skewRadAtom1_qt1_H skewRadAtom1_qt1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt1_qT3 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1 qT3' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt1 * (skewRadAtom1_qt1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qt1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt1 * Y2 * P * Q) * skewRadAtom1_qt1_F1_eq s r μ hr hf hμ hs hs3 + (qt1 * Y4 * P * Q) * skewRadAtom1_qt1_F2_eq s r μ hr hf hμ hs hs3 + (qt1 * Y6 * P * Q) * skewRadAtom1_qt1_H_eq s r μ hr hf hμ hs hs3 + (qt1 * Y7 * P * Q) * skewRadAtom1_qt1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt2_qtr0 (s r μ : ℂ) : ℂ := (((-2 : ℂ) * r ^ (2 : ℕ) + (6 : ℂ) * r ^ (4 : ℕ) + (-6 : ℂ) * r ^ (6 : ℕ) + (2 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qt2_qtr0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0' : ℂ) :
    skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr0' * skewRadQQ_qt2_qtr0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt2_qtr0 skewRadAtom1_qt2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt2_qtr0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2 qtr0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt2 * (skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt2 * Y6 * P * Q) * skewRadAtom1_qt2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt2_qtr1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt2_qtr1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1' : ℂ) :
    skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr1' * skewRadQQ_qt2_qtr1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt2_qtr1 skewRadAtom1_qt2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt2_qtr1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2 qtr1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt2 * (skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt2 * Y6 * P * Q) * skewRadAtom1_qt2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt2_qtr2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt2_qtr2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2' : ℂ) :
    skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr2' * skewRadQQ_qt2_qtr2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt2_qtr2 skewRadAtom1_qt2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt2_qtr2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2 qtr2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt2 * (skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt2 * Y6 * P * Q) * skewRadAtom1_qt2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt2_qt0 (s r μ : ℂ) : ℂ := (((-4 : ℂ) * r + (12 : ℂ) * r ^ (3 : ℕ) + (-12 : ℂ) * r ^ (5 : ℕ) + (4 : ℂ) * r ^ (7 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s * (s + 3)))

theorem skewRadQQ_qt2_qt0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0' : ℂ) :
    skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt0' * skewRadQQ_qt2_qt0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt2_qt0 skewRadAtom1_qt2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt2_qt0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2 qt0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt2 * (skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt2 * Y6 * P * Q) * skewRadAtom1_qt2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt2_qt1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt2_qt1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1' : ℂ) :
    skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt1' * skewRadQQ_qt2_qt1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt2_qt1 skewRadAtom1_qt2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt2_qt1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2 qt1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt2 * (skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt2 * Y6 * P * Q) * skewRadAtom1_qt2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt2_qt2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt2_qt2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2' : ℂ) :
    skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt2' * skewRadQQ_qt2_qt2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt2_qt2 skewRadAtom1_qt2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt2_qt2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2 qt2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt2 * (skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt2 * Y6 * P * Q) * skewRadAtom1_qt2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt2_qT0 (s r μ : ℂ) : ℂ := (((-4 : ℂ) * r + (-2 : ℂ) * r * μ + (12 : ℂ) * r ^ (3 : ℕ) + (4 : ℂ) * r ^ (3 : ℕ) * μ + (-12 : ℂ) * r ^ (5 : ℕ) + (-2 : ℂ) * r ^ (5 : ℕ) * μ + (4 : ℂ) * r ^ (7 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qt2_qT0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0' : ℂ) :
    skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) = qT0' * skewRadQQ_qt2_qT0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt2_qT0 skewRadAtom1_qt2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt2_qT0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2 qT0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt2 * (skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt2 * Y6 * P * Q) * skewRadAtom1_qt2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt2_qT1 (s r μ : ℂ) : ℂ := (((-4 : ℂ) * r ^ (2 : ℕ) + (12 : ℂ) * r ^ (4 : ℕ) + (-12 : ℂ) * r ^ (6 : ℕ) + (4 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * s))

theorem skewRadQQ_qt2_qT1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1' : ℂ) :
    skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) = qT1' * skewRadQQ_qt2_qT1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt2_qT1 skewRadAtom1_qt2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt2_qT1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2 qT1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt2 * (skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt2 * Y6 * P * Q) * skewRadAtom1_qt2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt2_qT2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt2_qT2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2' : ℂ) :
    skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) = qT2' * skewRadQQ_qt2_qT2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt2_qT2 skewRadAtom1_qt2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt2_qT2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2 qT2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt2 * (skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt2 * Y6 * P * Q) * skewRadAtom1_qt2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qt2_qT3 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qt2_qT3_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3' : ℂ) :
    skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) = qT3' * skewRadQQ_qt2_qT3 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qt2_qT3 skewRadAtom1_qt2_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qt2_qT3 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2 qT3' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qt2 * (skewRadAtom1_qt2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qt2 * Y6 * P * Q) * skewRadAtom1_qt2_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT0_qtr0 (s r μ : ℂ) : ℂ := (((6 : ℂ) + (-3 : ℂ) * μ + (-242 : ℂ) * r ^ (2 : ℕ) + (35 : ℂ) * r ^ (2 : ℕ) * μ + (478 : ℂ) * r ^ (4 : ℕ) + (-21 : ℂ) * r ^ (4 : ℕ) * μ + (-254 : ℂ) * r ^ (6 : ℕ) + (-11 : ℂ) * r ^ (6 : ℕ) * μ + (12 : ℂ) * r ^ (8 : ℕ) + (-120 : ℂ) * s * r ^ (2 : ℕ) + (-12 : ℂ) * s * r ^ (2 : ℕ) * μ + (336 : ℂ) * s * r ^ (4 : ℕ) + (12 : ℂ) * s * r ^ (4 : ℕ) * μ + (-168 : ℂ) * s * r ^ (6 : ℕ) + (16 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-16 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (8 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ) / ((r ^ (2 : ℕ) - 1) * (2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT0_qtr0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0' : ℂ) :
    skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr0' * skewRadQQ_qT0_qtr0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT0_qtr0 skewRadAtom1_qT0_F0 skewRadAtom1_qT0_F01 skewRadAtom1_qT0_F1 skewRadAtom1_qT0_F2 skewRadAtom1_qT0_H skewRadAtom1_qT0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT0_qtr0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0 qtr0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT0 * (skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT0 * Y0 * P * Q) * skewRadAtom1_qT0_F0_eq s r μ hr hf hμ hs hs3 + (qT0 * Y1 * P * Q) * skewRadAtom1_qT0_F01_eq s r μ hr hf hμ hs hs3 + (qT0 * Y2 * P * Q) * skewRadAtom1_qT0_F1_eq s r μ hr hf hμ hs hs3 + (qT0 * Y4 * P * Q) * skewRadAtom1_qT0_F2_eq s r μ hr hf hμ hs hs3 + (qT0 * Y6 * P * Q) * skewRadAtom1_qT0_H_eq s r μ hr hf hμ hs hs3 + (qT0 * Y7 * P * Q) * skewRadAtom1_qT0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT0_qtr1 (s r μ : ℂ) : ℂ := (((-6 : ℂ) * r + (-1 : ℂ) * r * μ + (28 : ℂ) * r ^ (3 : ℕ) + (8 : ℂ) * r ^ (3 : ℕ) * μ + (-38 : ℂ) * r ^ (5 : ℕ) + (-7 : ℂ) * r ^ (5 : ℕ) * μ + (16 : ℂ) * r ^ (7 : ℕ) + (48 : ℂ) * s * r ^ (3 : ℕ) + (-24 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT0_qtr1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1' : ℂ) :
    skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr1' * skewRadQQ_qT0_qtr1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT0_qtr1 skewRadAtom1_qT0_F0 skewRadAtom1_qT0_F01 skewRadAtom1_qT0_F1 skewRadAtom1_qT0_F2 skewRadAtom1_qT0_H skewRadAtom1_qT0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT0_qtr1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0 qtr1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT0 * (skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT0 * Y0 * P * Q) * skewRadAtom1_qT0_F0_eq s r μ hr hf hμ hs hs3 + (qT0 * Y1 * P * Q) * skewRadAtom1_qT0_F01_eq s r μ hr hf hμ hs hs3 + (qT0 * Y2 * P * Q) * skewRadAtom1_qT0_F1_eq s r μ hr hf hμ hs hs3 + (qT0 * Y4 * P * Q) * skewRadAtom1_qT0_F2_eq s r μ hr hf hμ hs hs3 + (qT0 * Y6 * P * Q) * skewRadAtom1_qT0_H_eq s r μ hr hf hμ hs hs3 + (qT0 * Y7 * P * Q) * skewRadAtom1_qT0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT0_qtr2 (s r μ : ℂ) : ℂ := (((-2 : ℂ) * r ^ (2 : ℕ) + (-1 : ℂ) * r ^ (2 : ℕ) * μ + (6 : ℂ) * r ^ (4 : ℕ) + (2 : ℂ) * r ^ (4 : ℕ) * μ + (-6 : ℂ) * r ^ (6 : ℕ) + (-1 : ℂ) * r ^ (6 : ℕ) * μ + (2 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT0_qtr2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2' : ℂ) :
    skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr2' * skewRadQQ_qT0_qtr2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT0_qtr2 skewRadAtom1_qT0_F0 skewRadAtom1_qT0_F01 skewRadAtom1_qT0_F1 skewRadAtom1_qT0_F2 skewRadAtom1_qT0_H skewRadAtom1_qT0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT0_qtr2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0 qtr2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT0 * (skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT0 * Y0 * P * Q) * skewRadAtom1_qT0_F0_eq s r μ hr hf hμ hs hs3 + (qT0 * Y1 * P * Q) * skewRadAtom1_qT0_F01_eq s r μ hr hf hμ hs hs3 + (qT0 * Y2 * P * Q) * skewRadAtom1_qT0_F1_eq s r μ hr hf hμ hs hs3 + (qT0 * Y4 * P * Q) * skewRadAtom1_qT0_F2_eq s r μ hr hf hμ hs hs3 + (qT0 * Y6 * P * Q) * skewRadAtom1_qT0_H_eq s r μ hr hf hμ hs hs3 + (qT0 * Y7 * P * Q) * skewRadAtom1_qT0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT0_qt0 (s r μ : ℂ) : ℂ := (((4 : ℂ) * μ + (-2 : ℂ) * μ ^ (2 : ℕ) + (-432 : ℂ) * r ^ (2 : ℕ) + (56 : ℂ) * r ^ (2 : ℕ) * μ + (6 : ℂ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (864 : ℂ) * r ^ (4 : ℕ) + (-48 : ℂ) * r ^ (4 : ℕ) * μ + (-4 : ℂ) * r ^ (4 : ℕ) * μ ^ (2 : ℕ) + (-432 : ℂ) * r ^ (6 : ℕ) + (-12 : ℂ) * r ^ (6 : ℕ) * μ + (-240 : ℂ) * s * r ^ (2 : ℕ) + (24 : ℂ) * s * r ^ (2 : ℕ) * μ + (576 : ℂ) * s * r ^ (4 : ℕ) + (-288 : ℂ) * s * r ^ (6 : ℕ) + (32 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-16 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-32 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (16 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ) / (r * (r ^ (2 : ℕ) - 1) * (2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT0_qt0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0' : ℂ) :
    skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt0' * skewRadQQ_qT0_qt0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT0_qt0 skewRadAtom1_qT0_F0 skewRadAtom1_qT0_F01 skewRadAtom1_qT0_F1 skewRadAtom1_qT0_F2 skewRadAtom1_qT0_H skewRadAtom1_qT0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT0_qt0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0 qt0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT0 * (skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT0 * Y0 * P * Q) * skewRadAtom1_qT0_F0_eq s r μ hr hf hμ hs hs3 + (qT0 * Y1 * P * Q) * skewRadAtom1_qT0_F01_eq s r μ hr hf hμ hs hs3 + (qT0 * Y2 * P * Q) * skewRadAtom1_qT0_F1_eq s r μ hr hf hμ hs hs3 + (qT0 * Y4 * P * Q) * skewRadAtom1_qT0_F2_eq s r μ hr hf hμ hs hs3 + (qT0 * Y6 * P * Q) * skewRadAtom1_qT0_H_eq s r μ hr hf hμ hs hs3 + (qT0 * Y7 * P * Q) * skewRadAtom1_qT0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT0_qt1 (s r μ : ℂ) : ℂ := (((-8 : ℂ) + (2 : ℂ) * μ + (1 : ℂ) * μ ^ (2 : ℕ) + (40 : ℂ) * r ^ (2 : ℕ) + (6 : ℂ) * r ^ (2 : ℕ) * μ + (-1 : ℂ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-56 : ℂ) * r ^ (4 : ℕ) + (-8 : ℂ) * r ^ (4 : ℕ) * μ + (24 : ℂ) * r ^ (6 : ℕ) + (96 : ℂ) * s * r ^ (2 : ℕ) + (-48 : ℂ) * s * r ^ (4 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT0_qt1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1' : ℂ) :
    skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt1' * skewRadQQ_qT0_qt1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT0_qt1 skewRadAtom1_qT0_F0 skewRadAtom1_qT0_F01 skewRadAtom1_qT0_F1 skewRadAtom1_qT0_F2 skewRadAtom1_qT0_H skewRadAtom1_qT0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT0_qt1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0 qt1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT0 * (skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT0 * Y0 * P * Q) * skewRadAtom1_qT0_F0_eq s r μ hr hf hμ hs hs3 + (qT0 * Y1 * P * Q) * skewRadAtom1_qT0_F01_eq s r μ hr hf hμ hs hs3 + (qT0 * Y2 * P * Q) * skewRadAtom1_qT0_F1_eq s r μ hr hf hμ hs hs3 + (qT0 * Y4 * P * Q) * skewRadAtom1_qT0_F2_eq s r μ hr hf hμ hs hs3 + (qT0 * Y6 * P * Q) * skewRadAtom1_qT0_H_eq s r μ hr hf hμ hs hs3 + (qT0 * Y7 * P * Q) * skewRadAtom1_qT0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT0_qt2 (s r μ : ℂ) : ℂ := (((-4 : ℂ) * r + (-2 : ℂ) * r * μ + (12 : ℂ) * r ^ (3 : ℕ) + (4 : ℂ) * r ^ (3 : ℕ) * μ + (-12 : ℂ) * r ^ (5 : ℕ) + (-2 : ℂ) * r ^ (5 : ℕ) * μ + (4 : ℂ) * r ^ (7 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT0_qt2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2' : ℂ) :
    skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt2' * skewRadQQ_qT0_qt2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT0_qt2 skewRadAtom1_qT0_F0 skewRadAtom1_qT0_F01 skewRadAtom1_qT0_F1 skewRadAtom1_qT0_F2 skewRadAtom1_qT0_H skewRadAtom1_qT0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT0_qt2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0 qt2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT0 * (skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT0 * Y0 * P * Q) * skewRadAtom1_qT0_F0_eq s r μ hr hf hμ hs hs3 + (qT0 * Y1 * P * Q) * skewRadAtom1_qT0_F01_eq s r μ hr hf hμ hs hs3 + (qT0 * Y2 * P * Q) * skewRadAtom1_qT0_F1_eq s r μ hr hf hμ hs hs3 + (qT0 * Y4 * P * Q) * skewRadAtom1_qT0_F2_eq s r μ hr hf hμ hs hs3 + (qT0 * Y6 * P * Q) * skewRadAtom1_qT0_H_eq s r μ hr hf hμ hs hs3 + (qT0 * Y7 * P * Q) * skewRadAtom1_qT0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT0_qT0 (s r μ : ℂ) : ℂ := (((-864 : ℂ) * r + (144 : ℂ) * r * μ + (1296 : ℂ) * r ^ (3 : ℕ) + (-72 : ℂ) * r ^ (3 : ℕ) * μ + (-432 : ℂ) * r ^ (5 : ℕ) + (-576 : ℂ) * s * r + (96 : ℂ) * s * r * μ + (864 : ℂ) * s * r ^ (3 : ℕ) + (-48 : ℂ) * s * r ^ (3 : ℕ) * μ + (-288 : ℂ) * s * r ^ (5 : ℕ)) / ((r ^ (2 : ℕ) - 1) * (2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT0_qT0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0' : ℂ) :
    skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) = qT0' * skewRadQQ_qT0_qT0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT0_qT0 skewRadAtom1_qT0_F0 skewRadAtom1_qT0_F01 skewRadAtom1_qT0_F1 skewRadAtom1_qT0_F2 skewRadAtom1_qT0_H skewRadAtom1_qT0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT0_qT0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0 qT0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT0 * (skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT0 * Y0 * P * Q) * skewRadAtom1_qT0_F0_eq s r μ hr hf hμ hs hs3 + (qT0 * Y1 * P * Q) * skewRadAtom1_qT0_F01_eq s r μ hr hf hμ hs hs3 + (qT0 * Y2 * P * Q) * skewRadAtom1_qT0_F1_eq s r μ hr hf hμ hs hs3 + (qT0 * Y4 * P * Q) * skewRadAtom1_qT0_F2_eq s r μ hr hf hμ hs hs3 + (qT0 * Y6 * P * Q) * skewRadAtom1_qT0_H_eq s r μ hr hf hμ hs hs3 + (qT0 * Y7 * P * Q) * skewRadAtom1_qT0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT0_qT1 (s r μ : ℂ) : ℂ := (((24 : ℂ) + (2 : ℂ) * μ + (-7 : ℂ) * μ ^ (2 : ℕ) + (-552 : ℂ) * r ^ (2 : ℕ) + (44 : ℂ) * r ^ (2 : ℕ) * μ + (14 : ℂ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (1080 : ℂ) * r ^ (4 : ℕ) + (-18 : ℂ) * r ^ (4 : ℕ) * μ + (-7 : ℂ) * r ^ (4 : ℕ) * μ ^ (2 : ℕ) + (-600 : ℂ) * r ^ (6 : ℕ) + (-28 : ℂ) * r ^ (6 : ℕ) * μ + (48 : ℂ) * r ^ (8 : ℕ) + (-432 : ℂ) * s * r ^ (2 : ℕ) + (-24 : ℂ) * s * r ^ (2 : ℕ) * μ + (864 : ℂ) * s * r ^ (4 : ℕ) + (24 : ℂ) * s * r ^ (4 : ℕ) * μ + (-384 : ℂ) * s * r ^ (6 : ℕ) + (32 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-16 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (-32 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (16 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ) / ((r ^ (2 : ℕ) - 1) * (2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT0_qT1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1' : ℂ) :
    skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) = qT1' * skewRadQQ_qT0_qT1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT0_qT1 skewRadAtom1_qT0_F0 skewRadAtom1_qT0_F01 skewRadAtom1_qT0_F1 skewRadAtom1_qT0_F2 skewRadAtom1_qT0_H skewRadAtom1_qT0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT0_qT1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0 qT1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT0 * (skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT0 * Y0 * P * Q) * skewRadAtom1_qT0_F0_eq s r μ hr hf hμ hs hs3 + (qT0 * Y1 * P * Q) * skewRadAtom1_qT0_F01_eq s r μ hr hf hμ hs hs3 + (qT0 * Y2 * P * Q) * skewRadAtom1_qT0_F1_eq s r μ hr hf hμ hs hs3 + (qT0 * Y4 * P * Q) * skewRadAtom1_qT0_F2_eq s r μ hr hf hμ hs hs3 + (qT0 * Y6 * P * Q) * skewRadAtom1_qT0_H_eq s r μ hr hf hμ hs hs3 + (qT0 * Y7 * P * Q) * skewRadAtom1_qT0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT0_qT2 (s r μ : ℂ) : ℂ := (((-20 : ℂ) * r + (-6 : ℂ) * r * μ + (76 : ℂ) * r ^ (3 : ℕ) + (22 : ℂ) * r ^ (3 : ℕ) * μ + (-92 : ℂ) * r ^ (5 : ℕ) + (-16 : ℂ) * r ^ (5 : ℕ) * μ + (36 : ℂ) * r ^ (7 : ℕ) + (96 : ℂ) * s * r ^ (3 : ℕ) + (-48 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT0_qT2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2' : ℂ) :
    skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) = qT2' * skewRadQQ_qT0_qT2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT0_qT2 skewRadAtom1_qT0_F0 skewRadAtom1_qT0_F01 skewRadAtom1_qT0_F1 skewRadAtom1_qT0_F2 skewRadAtom1_qT0_H skewRadAtom1_qT0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT0_qT2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0 qT2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT0 * (skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT0 * Y0 * P * Q) * skewRadAtom1_qT0_F0_eq s r μ hr hf hμ hs hs3 + (qT0 * Y1 * P * Q) * skewRadAtom1_qT0_F01_eq s r μ hr hf hμ hs hs3 + (qT0 * Y2 * P * Q) * skewRadAtom1_qT0_F1_eq s r μ hr hf hμ hs hs3 + (qT0 * Y4 * P * Q) * skewRadAtom1_qT0_F2_eq s r μ hr hf hμ hs hs3 + (qT0 * Y6 * P * Q) * skewRadAtom1_qT0_H_eq s r μ hr hf hμ hs hs3 + (qT0 * Y7 * P * Q) * skewRadAtom1_qT0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT0_qT3 (s r μ : ℂ) : ℂ := (((-4 : ℂ) * r ^ (2 : ℕ) + (-2 : ℂ) * r ^ (2 : ℕ) * μ + (12 : ℂ) * r ^ (4 : ℕ) + (4 : ℂ) * r ^ (4 : ℕ) * μ + (-12 : ℂ) * r ^ (6 : ℕ) + (-2 : ℂ) * r ^ (6 : ℕ) * μ + (4 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT0_qT3_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3' : ℂ) :
    skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) = qT3' * skewRadQQ_qT0_qT3 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT0_qT3 skewRadAtom1_qT0_F0 skewRadAtom1_qT0_F01 skewRadAtom1_qT0_F1 skewRadAtom1_qT0_F2 skewRadAtom1_qT0_H skewRadAtom1_qT0_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT0_qT3 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0 qT3' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0 0 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT0 * (skewRadAtom1_qT0_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT0_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT0_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT0_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT0_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT0_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT0 * Y0 * P * Q) * skewRadAtom1_qT0_F0_eq s r μ hr hf hμ hs hs3 + (qT0 * Y1 * P * Q) * skewRadAtom1_qT0_F01_eq s r μ hr hf hμ hs hs3 + (qT0 * Y2 * P * Q) * skewRadAtom1_qT0_F1_eq s r μ hr hf hμ hs hs3 + (qT0 * Y4 * P * Q) * skewRadAtom1_qT0_F2_eq s r μ hr hf hμ hs hs3 + (qT0 * Y6 * P * Q) * skewRadAtom1_qT0_H_eq s r μ hr hf hμ hs hs3 + (qT0 * Y7 * P * Q) * skewRadAtom1_qT0_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT1_qtr0 (s r μ : ℂ) : ℂ := (((6 : ℂ) * r + (-3 : ℂ) * r * μ + (264 : ℂ) * r ^ (3 : ℕ) + (4 : ℂ) * r ^ (3 : ℕ) * μ + (-330 : ℂ) * r ^ (5 : ℕ) + (-1 : ℂ) * r ^ (5 : ℕ) * μ + (-12 : ℂ) * r ^ (7 : ℕ) + (144 : ℂ) * s * r ^ (3 : ℕ) + (-216 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT1_qtr0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0' : ℂ) :
    skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr0' * skewRadQQ_qT1_qtr0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT1_qtr0 skewRadAtom1_qT1_F0 skewRadAtom1_qT1_F01 skewRadAtom1_qT1_F1 skewRadAtom1_qT1_F2 skewRadAtom1_qT1_H skewRadAtom1_qT1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT1_qtr0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1 qtr0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT1 * (skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT1 * Y0 * P * Q) * skewRadAtom1_qT1_F0_eq s r μ hr hf hμ hs hs3 + (qT1 * Y1 * P * Q) * skewRadAtom1_qT1_F01_eq s r μ hr hf hμ hs hs3 + (qT1 * Y2 * P * Q) * skewRadAtom1_qT1_F1_eq s r μ hr hf hμ hs hs3 + (qT1 * Y4 * P * Q) * skewRadAtom1_qT1_F2_eq s r μ hr hf hμ hs hs3 + (qT1 * Y6 * P * Q) * skewRadAtom1_qT1_H_eq s r μ hr hf hμ hs hs3 + (qT1 * Y7 * P * Q) * skewRadAtom1_qT1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT1_qtr1 (s r μ : ℂ) : ℂ := (((-6 : ℂ) * r ^ (2 : ℕ) + (1 : ℂ) * r ^ (2 : ℕ) * μ + (28 : ℂ) * r ^ (4 : ℕ) + (-2 : ℂ) * r ^ (4 : ℕ) * μ + (-38 : ℂ) * r ^ (6 : ℕ) + (1 : ℂ) * r ^ (6 : ℕ) * μ + (16 : ℂ) * r ^ (8 : ℕ) + (24 : ℂ) * s * r ^ (4 : ℕ) + (-24 : ℂ) * s * r ^ (6 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT1_qtr1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1' : ℂ) :
    skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr1' * skewRadQQ_qT1_qtr1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT1_qtr1 skewRadAtom1_qT1_F0 skewRadAtom1_qT1_F01 skewRadAtom1_qT1_F1 skewRadAtom1_qT1_F2 skewRadAtom1_qT1_H skewRadAtom1_qT1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT1_qtr1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1 qtr1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT1 * (skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT1 * Y0 * P * Q) * skewRadAtom1_qT1_F0_eq s r μ hr hf hμ hs hs3 + (qT1 * Y1 * P * Q) * skewRadAtom1_qT1_F01_eq s r μ hr hf hμ hs hs3 + (qT1 * Y2 * P * Q) * skewRadAtom1_qT1_F1_eq s r μ hr hf hμ hs hs3 + (qT1 * Y4 * P * Q) * skewRadAtom1_qT1_F2_eq s r μ hr hf hμ hs hs3 + (qT1 * Y6 * P * Q) * skewRadAtom1_qT1_H_eq s r μ hr hf hμ hs hs3 + (qT1 * Y7 * P * Q) * skewRadAtom1_qT1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT1_qtr2 (s r μ : ℂ) : ℂ := (((-2 : ℂ) * r ^ (3 : ℕ) + (6 : ℂ) * r ^ (5 : ℕ) + (-6 : ℂ) * r ^ (7 : ℕ) + (2 : ℂ) * r ^ (9 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT1_qtr2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2' : ℂ) :
    skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr2' * skewRadQQ_qT1_qtr2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT1_qtr2 skewRadAtom1_qT1_F0 skewRadAtom1_qT1_F01 skewRadAtom1_qT1_F1 skewRadAtom1_qT1_F2 skewRadAtom1_qT1_H skewRadAtom1_qT1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT1_qtr2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1 qtr2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT1 * (skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT1 * Y0 * P * Q) * skewRadAtom1_qT1_F0_eq s r μ hr hf hμ hs hs3 + (qT1 * Y1 * P * Q) * skewRadAtom1_qT1_F01_eq s r μ hr hf hμ hs hs3 + (qT1 * Y2 * P * Q) * skewRadAtom1_qT1_F1_eq s r μ hr hf hμ hs hs3 + (qT1 * Y4 * P * Q) * skewRadAtom1_qT1_F2_eq s r μ hr hf hμ hs hs3 + (qT1 * Y6 * P * Q) * skewRadAtom1_qT1_H_eq s r μ hr hf hμ hs hs3 + (qT1 * Y7 * P * Q) * skewRadAtom1_qT1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT1_qt0 (s r μ : ℂ) : ℂ := (((24 : ℂ) + (-10 : ℂ) * μ + (-1 : ℂ) * μ ^ (2 : ℕ) + (480 : ℂ) * r ^ (2 : ℕ) + (18 : ℂ) * r ^ (2 : ℕ) * μ + (1 : ℂ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-600 : ℂ) * r ^ (4 : ℕ) + (-8 : ℂ) * r ^ (4 : ℕ) * μ + (-48 : ℂ) * r ^ (6 : ℕ) + (288 : ℂ) * s * r ^ (2 : ℕ) + (-24 : ℂ) * s * r ^ (2 : ℕ) * μ + (-384 : ℂ) * s * r ^ (4 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT1_qt0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0' : ℂ) :
    skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt0' * skewRadQQ_qT1_qt0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT1_qt0 skewRadAtom1_qT1_F0 skewRadAtom1_qT1_F01 skewRadAtom1_qT1_F1 skewRadAtom1_qT1_F2 skewRadAtom1_qT1_H skewRadAtom1_qT1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT1_qt0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1 qt0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT1 * (skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT1 * Y0 * P * Q) * skewRadAtom1_qT1_F0_eq s r μ hr hf hμ hs hs3 + (qT1 * Y1 * P * Q) * skewRadAtom1_qT1_F01_eq s r μ hr hf hμ hs hs3 + (qT1 * Y2 * P * Q) * skewRadAtom1_qT1_F1_eq s r μ hr hf hμ hs hs3 + (qT1 * Y4 * P * Q) * skewRadAtom1_qT1_F2_eq s r μ hr hf hμ hs hs3 + (qT1 * Y6 * P * Q) * skewRadAtom1_qT1_H_eq s r μ hr hf hμ hs hs3 + (qT1 * Y7 * P * Q) * skewRadAtom1_qT1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT1_qt1 (s r μ : ℂ) : ℂ := (((-8 : ℂ) * r + (4 : ℂ) * r * μ + (40 : ℂ) * r ^ (3 : ℕ) + (-8 : ℂ) * r ^ (3 : ℕ) * μ + (-56 : ℂ) * r ^ (5 : ℕ) + (4 : ℂ) * r ^ (5 : ℕ) * μ + (24 : ℂ) * r ^ (7 : ℕ) + (48 : ℂ) * s * r ^ (3 : ℕ) + (-48 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT1_qt1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1' : ℂ) :
    skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt1' * skewRadQQ_qT1_qt1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT1_qt1 skewRadAtom1_qT1_F0 skewRadAtom1_qT1_F01 skewRadAtom1_qT1_F1 skewRadAtom1_qT1_F2 skewRadAtom1_qT1_H skewRadAtom1_qT1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT1_qt1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1 qt1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT1 * (skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT1 * Y0 * P * Q) * skewRadAtom1_qT1_F0_eq s r μ hr hf hμ hs hs3 + (qT1 * Y1 * P * Q) * skewRadAtom1_qT1_F01_eq s r μ hr hf hμ hs hs3 + (qT1 * Y2 * P * Q) * skewRadAtom1_qT1_F1_eq s r μ hr hf hμ hs hs3 + (qT1 * Y4 * P * Q) * skewRadAtom1_qT1_F2_eq s r μ hr hf hμ hs hs3 + (qT1 * Y6 * P * Q) * skewRadAtom1_qT1_H_eq s r μ hr hf hμ hs hs3 + (qT1 * Y7 * P * Q) * skewRadAtom1_qT1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT1_qt2 (s r μ : ℂ) : ℂ := (((-4 : ℂ) * r ^ (2 : ℕ) + (12 : ℂ) * r ^ (4 : ℕ) + (-12 : ℂ) * r ^ (6 : ℕ) + (4 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT1_qt2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2' : ℂ) :
    skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt2' * skewRadQQ_qT1_qt2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT1_qt2 skewRadAtom1_qT1_F0 skewRadAtom1_qT1_F01 skewRadAtom1_qT1_F1 skewRadAtom1_qT1_F2 skewRadAtom1_qT1_H skewRadAtom1_qT1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT1_qt2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1 qt2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT1 * (skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT1 * Y0 * P * Q) * skewRadAtom1_qT1_F0_eq s r μ hr hf hμ hs hs3 + (qT1 * Y1 * P * Q) * skewRadAtom1_qT1_F01_eq s r μ hr hf hμ hs hs3 + (qT1 * Y2 * P * Q) * skewRadAtom1_qT1_F1_eq s r μ hr hf hμ hs hs3 + (qT1 * Y4 * P * Q) * skewRadAtom1_qT1_F2_eq s r μ hr hf hμ hs hs3 + (qT1 * Y6 * P * Q) * skewRadAtom1_qT1_H_eq s r μ hr hf hμ hs hs3 + (qT1 * Y7 * P * Q) * skewRadAtom1_qT1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT1_qT0 (s r μ : ℂ) : ℂ := (((-24 : ℂ) + (-2 : ℂ) * μ + (7 : ℂ) * μ ^ (2 : ℕ) + (-1032 : ℂ) * r ^ (2 : ℕ) + (28 : ℂ) * r ^ (2 : ℕ) * μ + (-14 : ℂ) * r ^ (2 : ℕ) * μ ^ (2 : ℕ) + (1800 : ℂ) * r ^ (4 : ℕ) + (-54 : ℂ) * r ^ (4 : ℕ) * μ + (7 : ℂ) * r ^ (4 : ℕ) * μ ^ (2 : ℕ) + (-552 : ℂ) * r ^ (6 : ℕ) + (28 : ℂ) * r ^ (6 : ℕ) * μ + (-48 : ℂ) * r ^ (8 : ℕ) + (-624 : ℂ) * s * r ^ (2 : ℕ) + (72 : ℂ) * s * r ^ (2 : ℕ) * μ + (1056 : ℂ) * s * r ^ (4 : ℕ) + (-72 : ℂ) * s * r ^ (4 : ℕ) * μ + (-384 : ℂ) * s * r ^ (6 : ℕ) + (-32 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (16 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) * μ + (32 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-16 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) * μ) / ((r ^ (2 : ℕ) - 1) * (2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT1_qT0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0' : ℂ) :
    skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) = qT0' * skewRadQQ_qT1_qT0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT1_qT0 skewRadAtom1_qT1_F0 skewRadAtom1_qT1_F01 skewRadAtom1_qT1_F1 skewRadAtom1_qT1_F2 skewRadAtom1_qT1_H skewRadAtom1_qT1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT1_qT0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1 qT0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT1 * (skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT1 * Y0 * P * Q) * skewRadAtom1_qT1_F0_eq s r μ hr hf hμ hs hs3 + (qT1 * Y1 * P * Q) * skewRadAtom1_qT1_F01_eq s r μ hr hf hμ hs hs3 + (qT1 * Y2 * P * Q) * skewRadAtom1_qT1_F1_eq s r μ hr hf hμ hs hs3 + (qT1 * Y4 * P * Q) * skewRadAtom1_qT1_F2_eq s r μ hr hf hμ hs hs3 + (qT1 * Y6 * P * Q) * skewRadAtom1_qT1_H_eq s r μ hr hf hμ hs hs3 + (qT1 * Y7 * P * Q) * skewRadAtom1_qT1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT1_qT1 (s r μ : ℂ) : ℂ := (((576 : ℂ) * r ^ (3 : ℕ) + (-720 : ℂ) * r ^ (5 : ℕ) + (384 : ℂ) * s * r ^ (3 : ℕ) + (-480 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT1_qT1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1' : ℂ) :
    skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) = qT1' * skewRadQQ_qT1_qT1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT1_qT1 skewRadAtom1_qT1_F0 skewRadAtom1_qT1_F01 skewRadAtom1_qT1_F1 skewRadAtom1_qT1_F2 skewRadAtom1_qT1_H skewRadAtom1_qT1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT1_qT1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1 qT1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT1 * (skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT1 * Y0 * P * Q) * skewRadAtom1_qT1_F0_eq s r μ hr hf hμ hs hs3 + (qT1 * Y1 * P * Q) * skewRadAtom1_qT1_F01_eq s r μ hr hf hμ hs hs3 + (qT1 * Y2 * P * Q) * skewRadAtom1_qT1_F1_eq s r μ hr hf hμ hs hs3 + (qT1 * Y4 * P * Q) * skewRadAtom1_qT1_F2_eq s r μ hr hf hμ hs hs3 + (qT1 * Y6 * P * Q) * skewRadAtom1_qT1_H_eq s r μ hr hf hμ hs hs3 + (qT1 * Y7 * P * Q) * skewRadAtom1_qT1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT1_qT2 (s r μ : ℂ) : ℂ := (((-20 : ℂ) * r ^ (2 : ℕ) + (2 : ℂ) * r ^ (2 : ℕ) * μ + (76 : ℂ) * r ^ (4 : ℕ) + (-4 : ℂ) * r ^ (4 : ℕ) * μ + (-92 : ℂ) * r ^ (6 : ℕ) + (2 : ℂ) * r ^ (6 : ℕ) * μ + (36 : ℂ) * r ^ (8 : ℕ) + (48 : ℂ) * s * r ^ (4 : ℕ) + (-48 : ℂ) * s * r ^ (6 : ℕ)) / ((2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT1_qT2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2' : ℂ) :
    skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) = qT2' * skewRadQQ_qT1_qT2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT1_qT2 skewRadAtom1_qT1_F0 skewRadAtom1_qT1_F01 skewRadAtom1_qT1_F1 skewRadAtom1_qT1_F2 skewRadAtom1_qT1_H skewRadAtom1_qT1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT1_qT2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1 qT2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT1 * (skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT1 * Y0 * P * Q) * skewRadAtom1_qT1_F0_eq s r μ hr hf hμ hs hs3 + (qT1 * Y1 * P * Q) * skewRadAtom1_qT1_F01_eq s r μ hr hf hμ hs hs3 + (qT1 * Y2 * P * Q) * skewRadAtom1_qT1_F1_eq s r μ hr hf hμ hs hs3 + (qT1 * Y4 * P * Q) * skewRadAtom1_qT1_F2_eq s r μ hr hf hμ hs hs3 + (qT1 * Y6 * P * Q) * skewRadAtom1_qT1_H_eq s r μ hr hf hμ hs hs3 + (qT1 * Y7 * P * Q) * skewRadAtom1_qT1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT1_qT3 (s r μ : ℂ) : ℂ := (((-4 : ℂ) * r ^ (3 : ℕ) + (12 : ℂ) * r ^ (5 : ℕ) + (-12 : ℂ) * r ^ (7 : ℕ) + (4 : ℂ) * r ^ (9 : ℕ)) / ((2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT1_qT3_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3' : ℂ) :
    skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) = qT3' * skewRadQQ_qT1_qT3 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT1_qT3 skewRadAtom1_qT1_F0 skewRadAtom1_qT1_F01 skewRadAtom1_qT1_F1 skewRadAtom1_qT1_F2 skewRadAtom1_qT1_H skewRadAtom1_qT1_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT1_qT3 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1 qT3' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1 0 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT1 * (skewRadAtom1_qT1_F0 s r μ * (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT1_F01 s r μ * (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT1_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT1_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT1_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT1_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT1 * Y0 * P * Q) * skewRadAtom1_qT1_F0_eq s r μ hr hf hμ hs hs3 + (qT1 * Y1 * P * Q) * skewRadAtom1_qT1_F01_eq s r μ hr hf hμ hs hs3 + (qT1 * Y2 * P * Q) * skewRadAtom1_qT1_F1_eq s r μ hr hf hμ hs hs3 + (qT1 * Y4 * P * Q) * skewRadAtom1_qT1_F2_eq s r μ hr hf hμ hs hs3 + (qT1 * Y6 * P * Q) * skewRadAtom1_qT1_H_eq s r μ hr hf hμ hs hs3 + (qT1 * Y7 * P * Q) * skewRadAtom1_qT1_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT2_qtr0 (s r μ : ℂ) : ℂ := (((8 : ℂ) * r ^ (2 : ℕ) + (38 : ℂ) * r ^ (4 : ℕ) + (-28 : ℂ) * r ^ (6 : ℕ) + (-18 : ℂ) * r ^ (8 : ℕ) + (24 : ℂ) * s * r ^ (4 : ℕ) + (-24 : ℂ) * s * r ^ (6 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT2_qtr0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0' : ℂ) :
    skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr0' * skewRadQQ_qT2_qtr0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT2_qtr0 skewRadAtom1_qT2_F1 skewRadAtom1_qT2_F2 skewRadAtom1_qT2_H skewRadAtom1_qT2_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT2_qtr0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2 qtr0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT2 * (skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT2 * Y2 * P * Q) * skewRadAtom1_qT2_F1_eq s r μ hr hf hμ hs hs3 + (qT2 * Y4 * P * Q) * skewRadAtom1_qT2_F2_eq s r μ hr hf hμ hs hs3 + (qT2 * Y6 * P * Q) * skewRadAtom1_qT2_H_eq s r μ hr hf hμ hs hs3 + (qT2 * Y7 * P * Q) * skewRadAtom1_qT2_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT2_qtr1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT2_qtr1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1' : ℂ) :
    skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr1' * skewRadQQ_qT2_qtr1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT2_qtr1 skewRadAtom1_qT2_F1 skewRadAtom1_qT2_F2 skewRadAtom1_qT2_H skewRadAtom1_qT2_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT2_qtr1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2 qtr1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT2 * (skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT2 * Y2 * P * Q) * skewRadAtom1_qT2_F1_eq s r μ hr hf hμ hs hs3 + (qT2 * Y4 * P * Q) * skewRadAtom1_qT2_F2_eq s r μ hr hf hμ hs hs3 + (qT2 * Y6 * P * Q) * skewRadAtom1_qT2_H_eq s r μ hr hf hμ hs hs3 + (qT2 * Y7 * P * Q) * skewRadAtom1_qT2_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT2_qtr2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT2_qtr2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2' : ℂ) :
    skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr2' * skewRadQQ_qT2_qtr2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT2_qtr2 skewRadAtom1_qT2_F1 skewRadAtom1_qT2_F2 skewRadAtom1_qT2_H skewRadAtom1_qT2_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT2_qtr2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2 qtr2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT2 * (skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT2 * Y2 * P * Q) * skewRadAtom1_qT2_F1_eq s r μ hr hf hμ hs hs3 + (qT2 * Y4 * P * Q) * skewRadAtom1_qT2_F2_eq s r μ hr hf hμ hs hs3 + (qT2 * Y6 * P * Q) * skewRadAtom1_qT2_H_eq s r μ hr hf hμ hs hs3 + (qT2 * Y7 * P * Q) * skewRadAtom1_qT2_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT2_qt0 (s r μ : ℂ) : ℂ := (((20 : ℂ) * r + (-2 : ℂ) * r * μ + (68 : ℂ) * r ^ (3 : ℕ) + (4 : ℂ) * r ^ (3 : ℕ) * μ + (-52 : ℂ) * r ^ (5 : ℕ) + (-2 : ℂ) * r ^ (5 : ℕ) * μ + (-36 : ℂ) * r ^ (7 : ℕ) + (48 : ℂ) * s * r ^ (3 : ℕ) + (-48 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT2_qt0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0' : ℂ) :
    skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt0' * skewRadQQ_qT2_qt0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT2_qt0 skewRadAtom1_qT2_F1 skewRadAtom1_qT2_F2 skewRadAtom1_qT2_H skewRadAtom1_qT2_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT2_qt0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2 qt0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT2 * (skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT2 * Y2 * P * Q) * skewRadAtom1_qT2_F1_eq s r μ hr hf hμ hs hs3 + (qT2 * Y4 * P * Q) * skewRadAtom1_qT2_F2_eq s r μ hr hf hμ hs hs3 + (qT2 * Y6 * P * Q) * skewRadAtom1_qT2_H_eq s r μ hr hf hμ hs hs3 + (qT2 * Y7 * P * Q) * skewRadAtom1_qT2_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT2_qt1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT2_qt1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1' : ℂ) :
    skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt1' * skewRadQQ_qT2_qt1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT2_qt1 skewRadAtom1_qT2_F1 skewRadAtom1_qT2_F2 skewRadAtom1_qT2_H skewRadAtom1_qT2_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT2_qt1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2 qt1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT2 * (skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT2 * Y2 * P * Q) * skewRadAtom1_qT2_F1_eq s r μ hr hf hμ hs hs3 + (qT2 * Y4 * P * Q) * skewRadAtom1_qT2_F2_eq s r μ hr hf hμ hs hs3 + (qT2 * Y6 * P * Q) * skewRadAtom1_qT2_H_eq s r μ hr hf hμ hs hs3 + (qT2 * Y7 * P * Q) * skewRadAtom1_qT2_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT2_qt2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT2_qt2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2' : ℂ) :
    skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt2' * skewRadQQ_qT2_qt2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT2_qt2 skewRadAtom1_qT2_F1 skewRadAtom1_qT2_F2 skewRadAtom1_qT2_H skewRadAtom1_qT2_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT2_qt2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2 qt2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT2 * (skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT2 * Y2 * P * Q) * skewRadAtom1_qT2_F1_eq s r μ hr hf hμ hs hs3 + (qT2 * Y4 * P * Q) * skewRadAtom1_qT2_F2_eq s r μ hr hf hμ hs hs3 + (qT2 * Y6 * P * Q) * skewRadAtom1_qT2_H_eq s r μ hr hf hμ hs hs3 + (qT2 * Y7 * P * Q) * skewRadAtom1_qT2_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT2_qT0 (s r μ : ℂ) : ℂ := (((20 : ℂ) * r + (6 : ℂ) * r * μ + (212 : ℂ) * r ^ (3 : ℕ) + (-22 : ℂ) * r ^ (3 : ℕ) * μ + (-52 : ℂ) * r ^ (5 : ℕ) + (16 : ℂ) * r ^ (5 : ℕ) * μ + (-36 : ℂ) * r ^ (7 : ℕ) + (96 : ℂ) * s * r ^ (3 : ℕ) + (-48 : ℂ) * s * r ^ (5 : ℕ)) / ((2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT2_qT0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0' : ℂ) :
    skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) = qT0' * skewRadQQ_qT2_qT0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT2_qT0 skewRadAtom1_qT2_F1 skewRadAtom1_qT2_F2 skewRadAtom1_qT2_H skewRadAtom1_qT2_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT2_qT0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2 qT0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT2 * (skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT2 * Y2 * P * Q) * skewRadAtom1_qT2_F1_eq s r μ hr hf hμ hs hs3 + (qT2 * Y4 * P * Q) * skewRadAtom1_qT2_F2_eq s r μ hr hf hμ hs hs3 + (qT2 * Y6 * P * Q) * skewRadAtom1_qT2_H_eq s r μ hr hf hμ hs hs3 + (qT2 * Y7 * P * Q) * skewRadAtom1_qT2_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT2_qT1 (s r μ : ℂ) : ℂ := (((20 : ℂ) * r ^ (2 : ℕ) + (-2 : ℂ) * r ^ (2 : ℕ) * μ + (68 : ℂ) * r ^ (4 : ℕ) + (4 : ℂ) * r ^ (4 : ℕ) * μ + (-52 : ℂ) * r ^ (6 : ℕ) + (-2 : ℂ) * r ^ (6 : ℕ) * μ + (-36 : ℂ) * r ^ (8 : ℕ) + (48 : ℂ) * s * r ^ (4 : ℕ) + (-48 : ℂ) * s * r ^ (6 : ℕ)) / ((2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT2_qT1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1' : ℂ) :
    skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) = qT1' * skewRadQQ_qT2_qT1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT2_qT1 skewRadAtom1_qT2_F1 skewRadAtom1_qT2_F2 skewRadAtom1_qT2_H skewRadAtom1_qT2_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT2_qT1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2 qT1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT2 * (skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT2 * Y2 * P * Q) * skewRadAtom1_qT2_F1_eq s r μ hr hf hμ hs hs3 + (qT2 * Y4 * P * Q) * skewRadAtom1_qT2_F2_eq s r μ hr hf hμ hs hs3 + (qT2 * Y6 * P * Q) * skewRadAtom1_qT2_H_eq s r μ hr hf hμ hs hs3 + (qT2 * Y7 * P * Q) * skewRadAtom1_qT2_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT2_qT2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT2_qT2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2' : ℂ) :
    skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) = qT2' * skewRadQQ_qT2_qT2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT2_qT2 skewRadAtom1_qT2_F1 skewRadAtom1_qT2_F2 skewRadAtom1_qT2_H skewRadAtom1_qT2_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT2_qT2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2 qT2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT2 * (skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT2 * Y2 * P * Q) * skewRadAtom1_qT2_F1_eq s r μ hr hf hμ hs hs3 + (qT2 * Y4 * P * Q) * skewRadAtom1_qT2_F2_eq s r μ hr hf hμ hs hs3 + (qT2 * Y6 * P * Q) * skewRadAtom1_qT2_H_eq s r μ hr hf hμ hs hs3 + (qT2 * Y7 * P * Q) * skewRadAtom1_qT2_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT2_qT3 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT2_qT3_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3' : ℂ) :
    skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) = qT3' * skewRadQQ_qT2_qT3 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT2_qT3 skewRadAtom1_qT2_F1 skewRadAtom1_qT2_F2 skewRadAtom1_qT2_H skewRadAtom1_qT2_H1
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT2_qT3 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2 qT3' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2 0 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT2 * (skewRadAtom1_qT2_F1 s r μ * (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT2_F2 s r μ * (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT2_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) + skewRadAtom1_qT2_H1 s r μ * (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT2 * Y2 * P * Q) * skewRadAtom1_qT2_F1_eq s r μ hr hf hμ hs hs3 + (qT2 * Y4 * P * Q) * skewRadAtom1_qT2_F2_eq s r μ hr hf hμ hs hs3 + (qT2 * Y6 * P * Q) * skewRadAtom1_qT2_H_eq s r μ hr hf hμ hs hs3 + (qT2 * Y7 * P * Q) * skewRadAtom1_qT2_H1_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT3_qtr0 (s r μ : ℂ) : ℂ := (((2 : ℂ) * r ^ (3 : ℕ) + (-6 : ℂ) * r ^ (5 : ℕ) + (6 : ℂ) * r ^ (7 : ℕ) + (-2 : ℂ) * r ^ (9 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT3_qtr0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr0' : ℂ) :
    skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr0' * skewRadQQ_qT3_qtr0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT3_qtr0 skewRadAtom1_qT3_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT3_qtr0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3 qtr0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT3 * (skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 qtr0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT3 * Y6 * P * Q) * skewRadAtom1_qT3_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT3_qtr1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT3_qtr1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr1' : ℂ) :
    skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr1' * skewRadQQ_qT3_qtr1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT3_qtr1 skewRadAtom1_qT3_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT3_qtr1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3 qtr1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT3 * (skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 qtr1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT3 * Y6 * P * Q) * skewRadAtom1_qT3_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT3_qtr2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT3_qtr2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qtr2' : ℂ) :
    skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qtr2' * skewRadQQ_qT3_qtr2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT3_qtr2 skewRadAtom1_qT3_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT3_qtr2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3 qtr2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT3 * (skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 qtr2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT3 * Y6 * P * Q) * skewRadAtom1_qT3_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT3_qt0 (s r μ : ℂ) : ℂ := (((4 : ℂ) * r ^ (2 : ℕ) + (-12 : ℂ) * r ^ (4 : ℕ) + (12 : ℂ) * r ^ (6 : ℕ) + (-4 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ) * (s + 3)))

theorem skewRadQQ_qT3_qt0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt0' : ℂ) :
    skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt0' * skewRadQQ_qT3_qt0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT3_qt0 skewRadAtom1_qT3_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT3_qt0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3 qt0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT3 * (skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt0' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT3 * Y6 * P * Q) * skewRadAtom1_qT3_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT3_qt1 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT3_qt1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt1' : ℂ) :
    skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt1' * skewRadQQ_qT3_qt1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT3_qt1 skewRadAtom1_qT3_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT3_qt1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3 qt1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT3 * (skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt1' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT3 * Y6 * P * Q) * skewRadAtom1_qT3_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT3_qt2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT3_qt2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qt2' : ℂ) :
    skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) = qt2' * skewRadQQ_qT3_qt2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT3_qt2 skewRadAtom1_qT3_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT3_qt2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3 qt2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT3 * (skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qt2' 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT3 * Y6 * P * Q) * skewRadAtom1_qT3_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT3_qT0 (s r μ : ℂ) : ℂ := (((4 : ℂ) * r ^ (2 : ℕ) + (2 : ℂ) * r ^ (2 : ℕ) * μ + (-12 : ℂ) * r ^ (4 : ℕ) + (-4 : ℂ) * r ^ (4 : ℕ) * μ + (12 : ℂ) * r ^ (6 : ℕ) + (2 : ℂ) * r ^ (6 : ℕ) * μ + (-4 : ℂ) * r ^ (8 : ℕ)) / ((2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT3_qT0_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT0' : ℂ) :
    skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) = qT0' * skewRadQQ_qT3_qT0 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT3_qT0 skewRadAtom1_qT3_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT3_qT0 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3 qT0' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT3 * (skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT0' 0 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT3 * Y6 * P * Q) * skewRadAtom1_qT3_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT3_qT1 (s r μ : ℂ) : ℂ := (((4 : ℂ) * r ^ (3 : ℕ) + (-12 : ℂ) * r ^ (5 : ℕ) + (12 : ℂ) * r ^ (7 : ℕ) + (-4 : ℂ) * r ^ (9 : ℕ)) / ((2 - μ) ^ (2 : ℕ)))

theorem skewRadQQ_qT3_qT1_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT1' : ℂ) :
    skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) = qT1' * skewRadQQ_qT3_qT1 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT3_qT1 skewRadAtom1_qT3_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT3_qT1 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3 qT1' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT3 * (skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT1' 0 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT3 * Y6 * P * Q) * skewRadAtom1_qT3_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT3_qT2 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT3_qT2_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT2' : ℂ) :
    skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) = qT2' * skewRadQQ_qT3_qT2 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT3_qT2 skewRadAtom1_qT3_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT3_qT2 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3 qT2' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT3 * (skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT2' 0 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT3 * Y6 * P * Q) * skewRadAtom1_qT3_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

def skewRadQQ_qT3_qT3 (s r μ : ℂ) : ℂ := (0 : ℂ)

theorem skewRadQQ_qT3_qT3_eq (s r μ : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3' : ℂ) :
    skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) = qT3' * skewRadQQ_qT3_qT3 s r μ := by
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  unfold skewRadQQ_qT3_qT3 skewRadAtom1_qT3_H
  field_simp
  all_goals ring

theorem evenSector_skewRadRadQQ_qT3_qT3 (s r y μ P Px Py Pxx Pxy Pyy Q Qx Qy Qxx Qxy Qyy F02 F12 F22 H2 G02 G12 G22 L2 : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (qT3 qT3' : ℂ) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet (2 * s) r y (recF0 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF01 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F02 (recF1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF11 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F12 (recF2 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recF21 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) F22 (recH s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) (recH1 s r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3 0 0 0 0 0 0) H2 P Px Py Pxx Pxy Pyy) (metricJet (2 * (-3 - s)) r y (recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G02 (recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G12 (recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) G22 (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) (recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0) L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      qT3 * (skewRadAtom1_qT3_H s r μ * (recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0)) * P * Q := by
  rw [streamCurrent_1 hr hy hf]
  generalize hY0 : recF0 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y0
  generalize hY1 : recF01 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y1
  generalize hY2 : recF1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y2
  generalize hY3 : recF11 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y3
  generalize hY4 : recF2 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y4
  generalize hY5 : recF21 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y5
  generalize hY6 : recH (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y6
  generalize hY7 : recH1 (-3 - s) r μ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 qT3' 0 0 0 0 0 0 = Y7
  simp only [recF0, recF01, recF1, recF11, recF2, recF21, recH, recH1]
  linear_combination (norm := ring_nf) (qT3 * Y6 * P * Q) * skewRadAtom1_qT3_H_eq s r μ hr hf hμ hs hs3
  all_goals (try field_simp)
  all_goals (try ring)

end
end RHTower.D4BMScalarStream
