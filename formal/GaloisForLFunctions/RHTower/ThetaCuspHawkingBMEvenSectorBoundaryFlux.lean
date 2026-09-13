import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorRadialCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamLaurentMaster
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorVectorLaurentMaster

/-!
# Boundary structure of the even-sector radial current at the fundamental harmonic

At the fundamental harmonic `μ = (s+1)(s+2)` of the `−` mode (the only harmonic that pairs with
it), the radial symplectic current between the `−` mode and the `++` Laurent responses, with the
Laurent coefficients at their actual values, is a single rational function of `r` with numerator of
degree eight and **no `r⁷` term** (`evenCurrentSS_eq`, `evenCurrentVV_eq`, Horner form in `r`).
Hence the coordinate flux `r²·(current)` is `slope · r` plus a remainder that is `O(1/r)` at the
AdS boundary (`evenCurrentSS_boundary`, `evenCurrentVV_boundary`): the boundary finite part of the
even-sector `++−` flux vanishes. The source-only currents are evaluated jet by jet
(`srcPieceSS_*`, `srcCurrentSS_eq`, vector–vector analogues), all closed forms in Horner form so
that every identity stays shallow. The resolvent denominators at this harmonic are
`2 − μ = −s(s+3)` and `μ − (2s+1)(2s+2) = −3s(s+1)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry
noncomputable section

/-! ## Horner forms at the fundamental harmonic -/
theorem ssSourceTR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR s r ((s + 1) * (s + 2)) = (((3 / 4 : ℂ) * s ^ 3 + (15 / 8 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-1 : ℂ) * s ^ 2 + (-7 / 2 : ℂ) * s ^ 3 + (-3 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((3 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 3))))) / (r ^ 5 * (r ^ 2 - 1)) := by
  unfold ssSourceTR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTR1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR1 s r ((s + 1) * (s + 2)) = (((15 / 4 : ℂ) * s ^ 3 + (87 / 8 : ℂ) * s ^ 4 + (45 / 4 : ℂ) * s ^ 5 + (39 / 8 : ℂ) * s ^ 6 + (3 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-3 : ℂ) * s ^ 2 + (-71 / 4 : ℂ) * s ^ 3 + (-197 / 8 : ℂ) * s ^ 4 + (-33 / 2 : ℂ) * s ^ 5 + (-37 / 8 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((8 : ℂ) * s ^ 2 + (23 : ℂ) * s ^ 3 + (13 / 2 : ℂ) * s ^ 4 + (5 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-9 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 3))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2) := by
  unfold ssSourceTR1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTR2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR2 s r ((s + 1) * (s + 2)) = (((45 / 2 : ℂ) * s ^ 3 + (291 / 4 : ℂ) * s ^ 4 + (357 / 4 : ℂ) * s ^ 5 + (207 / 4 : ℂ) * s ^ 6 + (57 / 4 : ℂ) * s ^ 7 + (3 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-12 : ℂ) * s ^ 2 + (-229 / 2 : ℂ) * s ^ 3 + (-971 / 4 : ℂ) * s ^ 4 + (-911 / 4 : ℂ) * s ^ 5 + (-401 / 4 : ℂ) * s ^ 6 + (-67 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((40 : ℂ) * s ^ 2 + (204 : ℂ) * s ^ 3 + (256 : ℂ) * s ^ 4 + (155 : ℂ) * s ^ 5 + (47 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-48 : ℂ) * s ^ 2 + (-156 : ℂ) * s ^ 3 + (-36 : ℂ) * s ^ 4 + (-30 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((36 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 3) := by
  unfold ssSourceTR2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceT_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT s r ((s + 1) * (s + 2)) = (((3 / 16 : ℂ) * s ^ 3 + (3 / 8 : ℂ) * s ^ 4 + (3 / 16 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1 / 2 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((1 / 2 : ℂ) * s))))) / (r ^ 4) := by
  unfold ssSourceT
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT1 s r ((s + 1) * (s + 2)) = (((3 / 4 : ℂ) * s ^ 3 + (15 / 8 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((1 : ℂ) * s ^ 2 + (3 / 4 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4 + (-3 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-1 / 2 : ℂ) * s ^ 3))))) / (r ^ 5 * (r ^ 2 - 1)) := by
  unfold ssSourceT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT2 s r ((s + 1) * (s + 2)) = (((15 / 4 : ℂ) * s ^ 3 + (87 / 8 : ℂ) * s ^ 4 + (45 / 4 : ℂ) * s ^ 5 + (39 / 8 : ℂ) * s ^ 6 + (3 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((3 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3 + (-117 / 8 : ℂ) * s ^ 4 + (-59 / 4 : ℂ) * s ^ 5 + (-33 / 8 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-5 : ℂ) * s ^ 2 + (-17 / 4 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4 + (15 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((3 / 2 : ℂ) * s ^ 3))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2) := by
  unfold ssSourceT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTF_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF s r ((s + 1) * (s + 2)) = (((-1 / 4 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((1 : ℂ) * s))) / (r ^ 4 * (s + 3)) := by
  unfold ssSourceTF
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTF1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-1 : ℂ) * s + (-5 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((3 : ℂ) * s + (4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-2 : ℂ) * s))))) / (r ^ 5 * (r ^ 2 - 1) * (s + 3)) := by
  unfold ssSourceTF1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTF2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF2 s r ((s + 1) * (s + 2)) = (((-5 : ℂ) * s + (-29 / 2 : ℂ) * s ^ 2 + (-15 : ℂ) * s ^ 3 + (-13 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((16 : ℂ) * s + (71 / 2 : ℂ) * s ^ 2 + (25 : ℂ) * s ^ 3 + (11 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-17 : ℂ) * s + (-24 : ℂ) * s ^ 2 + (-5 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((6 : ℂ) * s))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2 * (s + 3)) := by
  unfold ssSourceTF2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTF3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF3 s r ((s + 1) * (s + 2)) = (((-30 : ℂ) * s + (-97 : ℂ) * s ^ 2 + (-119 : ℂ) * s ^ 3 + (-69 : ℂ) * s ^ 4 + (-19 : ℂ) * s ^ 5 + (-2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((114 : ℂ) * s + (319 : ℂ) * s ^ 2 + (321 : ℂ) * s ^ 3 + (137 : ℂ) * s ^ 4 + (21 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-162 : ℂ) * s + (-366 : ℂ) * s ^ 2 + (-258 : ℂ) * s ^ 3 + (-54 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((102 : ℂ) * s + (156 : ℂ) * s ^ 2 + (30 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-24 : ℂ) * s))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 3 * (s + 3)) := by
  unfold ssSourceTF3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTR s r ((s + 1) * (s + 2)) = (((1 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((2 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5))) / (r ^ 5 * (r ^ 2 - 1)) := by
  unfold vvSourceTR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTR1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTR1 s r ((s + 1) * (s + 2)) = (((5 : ℂ) * s ^ 2 + (19 / 2 : ℂ) * s ^ 3 + (11 / 2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-7 : ℂ) * s ^ 2 + (-9 / 2 : ℂ) * s ^ 3 + (19 / 2 : ℂ) * s ^ 4 + (9 : ℂ) * s ^ 5 + (2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-10 : ℂ) * s ^ 3 + (-15 : ℂ) * s ^ 4 + (-5 : ℂ) * s ^ 5))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2) := by
  unfold vvSourceTR1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTR2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTR2 s r ((s + 1) * (s + 2)) = (((30 : ℂ) * s ^ 2 + (67 : ℂ) * s ^ 3 + (52 : ℂ) * s ^ 4 + (17 : ℂ) * s ^ 5 + (2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-78 : ℂ) * s ^ 2 + (-127 : ℂ) * s ^ 3 + (-26 : ℂ) * s ^ 4 + (45 : ℂ) * s ^ 5 + (26 : ℂ) * s ^ 6 + (4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((56 : ℂ) * s ^ 2 + (16 : ℂ) * s ^ 3 + (-126 : ℂ) * s ^ 4 + (-112 : ℂ) * s ^ 5 + (-26 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((60 : ℂ) * s ^ 3 + (90 : ℂ) * s ^ 4 + (30 : ℂ) * s ^ 5))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 3) := by
  unfold vvSourceTR2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceT_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceT s r ((s + 1) * (s + 2)) = ((3 / 2 : ℂ) * s ^ 2 + (9 / 4 : ℂ) * s ^ 3 + (3 / 4 : ℂ) * s ^ 4) / (r ^ 4) := by
  unfold vvSourceT
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceT1 s r ((s + 1) * (s + 2)) = (((6 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3 + (15 / 2 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-6 : ℂ) * s ^ 2 + (-9 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 4))) / (r ^ 5 * (r ^ 2 - 1)) := by
  unfold vvSourceT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceT2 s r ((s + 1) * (s + 2)) = (((30 : ℂ) * s ^ 2 + (72 : ℂ) * s ^ 3 + (123 / 2 : ℂ) * s ^ 4 + (45 / 2 : ℂ) * s ^ 5 + (3 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-60 : ℂ) * s ^ 2 + (-123 : ℂ) * s ^ 3 + (-159 / 2 : ℂ) * s ^ 4 + (-33 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((30 : ℂ) * s ^ 2 + (45 : ℂ) * s ^ 3 + (15 : ℂ) * s ^ 4))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2) := by
  unfold vvSourceT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTF_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTF s r ((s + 1) * (s + 2)) = ((11 : ℂ) * s + (57 / 2 : ℂ) * s ^ 2 + (53 / 2 : ℂ) * s ^ 3 + (21 / 2 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5) / (r ^ 4 * (s + 3)) := by
  unfold vvSourceTF
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTF1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTF1 s r ((s + 1) * (s + 2)) = (((44 : ℂ) * s + (136 : ℂ) * s ^ 2 + (163 : ℂ) * s ^ 3 + (95 : ℂ) * s ^ 4 + (27 : ℂ) * s ^ 5 + (3 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-44 : ℂ) * s + (-114 : ℂ) * s ^ 2 + (-106 : ℂ) * s ^ 3 + (-42 : ℂ) * s ^ 4 + (-6 : ℂ) * s ^ 5))) / (r ^ 5 * (r ^ 2 - 1) * (s + 3)) := by
  unfold vvSourceTF1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTF2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTF2 s r ((s + 1) * (s + 2)) = (((220 : ℂ) * s + (768 : ℂ) * s ^ 2 + (1087 : ℂ) * s ^ 3 + (801 : ℂ) * s ^ 4 + (325 : ℂ) * s ^ 5 + (69 : ℂ) * s ^ 6 + (6 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-440 : ℂ) * s + (-1382 : ℂ) * s ^ 2 + (-1687 : ℂ) * s ^ 3 + (-1003 : ℂ) * s ^ 4 + (-291 : ℂ) * s ^ 5 + (-33 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((220 : ℂ) * s + (570 : ℂ) * s ^ 2 + (530 : ℂ) * s ^ 3 + (210 : ℂ) * s ^ 4 + (30 : ℂ) * s ^ 5))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2 * (s + 3)) := by
  unfold vvSourceTF2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTF3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTF3 s r ((s + 1) * (s + 2)) = (((1320 : ℂ) * s + (5048 : ℂ) * s ^ 2 + (8058 : ℂ) * s ^ 3 + (6980 : ℂ) * s ^ 4 + (3552 : ℂ) * s ^ 5 + (1064 : ℂ) * s ^ 6 + (174 : ℂ) * s ^ 7 + (12 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-3960 : ℂ) * s + (-14088 : ℂ) * s ^ 2 + (-20382 : ℂ) * s ^ 3 + (-15396 : ℂ) * s ^ 4 + (-6420 : ℂ) * s ^ 5 + (-1404 : ℂ) * s ^ 6 + (-126 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((3960 : ℂ) * s + (12636 : ℂ) * s ^ 2 + (15696 : ℂ) * s ^ 3 + (9504 : ℂ) * s ^ 4 + (2808 : ℂ) * s ^ 5 + (324 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-1320 : ℂ) * s + (-3420 : ℂ) * s ^ 2 + (-3180 : ℂ) * s ^ 3 + (-1260 : ℂ) * s ^ 4 + (-180 : ℂ) * s ^ 5))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 3 * (s + 3)) := by
  unfold vvSourceTF3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qtr0 s r ((s + 1) * (s + 2)) = (((-3 : ℂ) * s + (-5 / 2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((3 : ℂ) + (35 / 2 : ℂ) * s + (-19 / 2 : ℂ) * s ^ 2 + (-17 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-20 : ℂ) + (74 : ℂ) * s + (77 / 2 : ℂ) * s ^ 2 + (23 / 2 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-43 : ℂ) + (-69 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))))) / (r ^ 2 * (r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold srcCoeff_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qtr1 s r ((s + 1) * (s + 2)) = (((-6 : ℂ) + (-2 : ℂ) * s + (3 / 2 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((1 : ℂ) + (29 / 2 : ℂ) * s + (6 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-23 : ℂ) + (-43 / 2 : ℂ) * s + (-7 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))))) / (r * s ^ 3 * (s + 3) ^ 2) := by
  unfold srcCoeff_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qtr2 s r ((s + 1) * (s + 2)) = (((-3 : ℂ) + (-5 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((5 : ℂ) + (5 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-1 : ℂ) + (-5 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-1 : ℂ)))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold srcCoeff_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qt0 s r ((s + 1) * (s + 2)) = (((9 : ℂ) * s + (39 / 2 : ℂ) * s ^ 2 + (29 / 2 : ℂ) * s ^ 3 + (9 / 2 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-7 : ℂ) * s + (-83 / 2 : ℂ) * s ^ 2 + (-63 / 2 : ℂ) * s ^ 3 + (-9 / 2 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-64 : ℂ) + (40 : ℂ) * s + (9 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-56 : ℂ) + (-42 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))))) / (r ^ 3 * (r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold srcCoeff_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qt1 s r ((s + 1) * (s + 2)) = (((15 : ℂ) * s + (31 / 2 : ℂ) * s ^ 2 + (5 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-18 : ℂ) + (3 : ℂ) * s + (-3 / 2 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-42 : ℂ) + (-36 : ℂ) * s + (-6 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (r ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  unfold srcCoeff_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qt2 s r ((s + 1) * (s + 2)) = (((-6 : ℂ) + (-5 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((10 : ℂ) + (10 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-2 : ℂ) + (-5 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-2 : ℂ)))))))) / (r * s ^ 3 * (s + 3) ^ 2) := by
  unfold srcCoeff_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qT0 s r ((s + 1) * (s + 2)) = (((27 : ℂ) * s + (117 / 2 : ℂ) * s ^ 2 + (87 / 2 : ℂ) * s ^ 3 + (27 / 2 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-91 : ℂ) * s + (-152 : ℂ) * s ^ 2 + (-80 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-52 : ℂ) + (215 : ℂ) * s + (257 / 2 : ℂ) * s ^ 2 + (75 / 2 : ℂ) * s ^ 3 + (-5 / 2 : ℂ) * s ^ 4 + (-5 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((8 : ℂ) + (-49 : ℂ) * s + (3 : ℂ) * s ^ 2 + (-17 : ℂ) * s ^ 3 + (-5 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((44 : ℂ) + (42 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))))))) / (r ^ 3 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold srcCoeff_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qT1 s r ((s + 1) * (s + 2)) = (((45 : ℂ) * s + (93 / 2 : ℂ) * s ^ 2 + (15 : ℂ) * s ^ 3 + (3 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-66 : ℂ) + (-121 : ℂ) * s + (-66 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-10 : ℂ) + (-164 : ℂ) * s + (-69 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3 + (-3 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((112 : ℂ) + (114 : ℂ) * s + (10 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((36 : ℂ)))))))))) / (r ^ 2 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold srcCoeff_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qT2 s r ((s + 1) * (s + 2)) = (((24 : ℂ) + (14 : ℂ) * s + (-1 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-16 : ℂ) + (-44 : ℂ) * s + (-15 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((46 : ℂ) + (48 : ℂ) * s + (8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((18 : ℂ)))))))) / (r * s ^ 2 * (s + 3) ^ 2) := by
  unfold srcCoeff_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qT3 s r ((s + 1) * (s + 2)) = (((6 : ℂ) + (5 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-10 : ℂ) + (-10 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((2 : ℂ) + (5 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold srcCoeff_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem evenCurrent_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : evenCurrent_lauR s r ((s + 1) * (s + 2)) = (((-33 / 2 : ℂ) * s + (-211 / 4 : ℂ) * s ^ 2 + (-15 / 4 : ℂ) * s ^ 3 + (79 / 4 : ℂ) * s ^ 4 + (21 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((6 : ℂ) + (167 / 2 : ℂ) * s + (-1 / 4 : ℂ) * s ^ 2 + (-31 / 4 : ℂ) * s ^ 3 + (-55 / 4 : ℂ) * s ^ 4 + (-15 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((32 : ℂ) + (14 : ℂ) * s + (29 / 2 : ℂ) * s ^ 2 + (-14 : ℂ) * s ^ 3 + (-5 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((28 : ℂ) + (27 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((6 : ℂ)))))))))) / (r ^ 3 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold evenCurrent_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem evenCurrent_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : evenCurrent_lauI1 s r ((s + 1) * (s + 2)) = (((45 / 2 : ℂ) + (291 / 4 : ℂ) * s + (321 / 4 : ℂ) * s ^ 2 + (141 / 4 : ℂ) * s ^ 3 + (21 / 4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-159 / 2 : ℂ) + (-561 / 4 : ℂ) * s + (-339 / 4 : ℂ) * s ^ 2 + (-111 / 4 : ℂ) * s ^ 3 + (-15 / 4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-3 : ℂ) * s + (-3 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((3 : ℂ) + (3 : ℂ) * s))))))) / (r ^ 5 * (r ^ 2 - 1) * s * (s + 3) ^ 2) := by
  unfold evenCurrent_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem evenCurrent_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : evenCurrent_lauI3 s r ((s + 1) * (s + 2)) = (((120 : ℂ) + (659 / 2 : ℂ) * s + (1433 / 4 : ℂ) * s ^ 2 + (769 / 4 : ℂ) * s ^ 3 + (203 / 4 : ℂ) * s ^ 4 + (21 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-422 : ℂ) + (-1581 / 2 : ℂ) * s + (-2289 / 4 : ℂ) * s ^ 2 + (-839 / 4 : ℂ) * s ^ 3 + (-167 / 4 : ℂ) * s ^ 4 + (-15 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((152 : ℂ) + (206 : ℂ) * s + (231 / 2 : ℂ) * s ^ 2 + (28 : ℂ) * s ^ 3 + (5 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((84 : ℂ) + (39 : ℂ) * s + (3 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-6 : ℂ)))))))))) / (r ^ 7 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold evenCurrent_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

/-! ## The SS source current at the fundamental harmonic -/
theorem srcPieceSS_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-27 / 4 : ℂ) * s ^ 3 + (-99 / 4 : ℂ) * s ^ 4 + (-579 / 16 : ℂ) * s ^ 5 + (-27 : ℂ) * s ^ 6 + (-87 / 8 : ℂ) * s ^ 7 + (-9 / 4 : ℂ) * s ^ 8 + (-3 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((63 / 4 : ℂ) * s ^ 2 + (201 / 2 : ℂ) * s ^ 3 + (2617 / 16 : ℂ) * s ^ 4 + (479 / 8 : ℂ) * s ^ 5 + (-901 / 8 : ℂ) * s ^ 6 + (-295 / 2 : ℂ) * s ^ 7 + (-1171 / 16 : ℂ) * s ^ 8 + (-135 / 8 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-9 : ℂ) * s + (-159 : ℂ) * s ^ 2 + (-739 / 4 : ℂ) * s ^ 3 + (3447 / 8 : ℂ) * s ^ 4 + (14285 / 16 : ℂ) * s ^ 5 + (1435 / 2 : ℂ) * s ^ 6 + (2663 / 8 : ℂ) * s ^ 7 + (739 / 8 : ℂ) * s ^ 8 + (217 / 16 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((87 : ℂ) * s + (293 / 4 : ℂ) * s ^ 2 + (-1219 : ℂ) * s ^ 3 + (-26407 / 16 : ℂ) * s ^ 4 + (-1152 : ℂ) * s ^ 5 + (-3757 / 8 : ℂ) * s ^ 6 + (-237 / 2 : ℂ) * s ^ 7 + (-331 / 16 : ℂ) * s ^ 8 + (-2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-51 : ℂ) * s + (1207 : ℂ) * s ^ 2 + (4533 / 4 : ℂ) * s ^ 3 + (523 : ℂ) * s ^ 4 + (747 / 4 : ℂ) * s ^ 5 + (59 / 2 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-351 : ℂ) * s + (-237 : ℂ) * s ^ 2 + (245 / 4 : ℂ) * s ^ 3 + (141 / 2 : ℂ) * s ^ 4 + (49 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s + (-18 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [srcCoeff_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((-135 / 2 : ℂ) * s ^ 2 + (-963 / 4 : ℂ) * s ^ 3 + (-2589 / 8 : ℂ) * s ^ 4 + (-2949 / 16 : ℂ) * s ^ 5 + (-75 / 8 : ℂ) * s ^ 6 + (339 / 8 : ℂ) * s ^ 7 + (177 / 8 : ℂ) * s ^ 8 + (75 / 16 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((54 : ℂ) * s + (1467 / 4 : ℂ) * s ^ 2 + (3393 / 4 : ℂ) * s ^ 3 + (18859 / 16 : ℂ) * s ^ 4 + (4247 / 4 : ℂ) * s ^ 5 + (2399 / 4 : ℂ) * s ^ 6 + (833 / 4 : ℂ) * s ^ 7 + (711 / 16 : ℂ) * s ^ 8 + (23 / 4 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-153 : ℂ) * s + (-1911 / 2 : ℂ) * s ^ 2 + (-9651 / 4 : ℂ) * s ^ 3 + (-3679 : ℂ) * s ^ 4 + (-53371 / 16 : ℂ) * s ^ 5 + (-3537 / 2 : ℂ) * s ^ 6 + (-4233 / 8 : ℂ) * s ^ 7 + (-163 / 2 : ℂ) * s ^ 8 + (-79 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((393 : ℂ) * s + (7613 / 4 : ℂ) * s ^ 2 + (17279 / 4 : ℂ) * s ^ 3 + (73651 / 16 : ℂ) * s ^ 4 + (12065 / 4 : ℂ) * s ^ 5 + (9483 / 8 : ℂ) * s ^ 6 + (481 / 2 : ℂ) * s ^ 7 + (299 / 16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-507 : ℂ) * s + (-2233 : ℂ) * s ^ 2 + (-8839 / 4 : ℂ) * s ^ 3 + (-2207 / 2 : ℂ) * s ^ 4 + (-1905 / 4 : ℂ) * s ^ 5 + (-145 : ℂ) * s ^ 6 + (-35 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((429 : ℂ) * s + (68 : ℂ) * s ^ 2 + (-733 / 4 : ℂ) * s ^ 3 + (-377 / 2 : ℂ) * s ^ 4 + (-181 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((216 : ℂ) * s + (36 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [srcCoeff_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((405 / 2 : ℂ) * s ^ 2 + (891 : ℂ) * s ^ 3 + (13257 / 8 : ℂ) * s ^ 4 + (13641 / 8 : ℂ) * s ^ 5 + (1065 : ℂ) * s ^ 6 + (1659 / 4 : ℂ) * s ^ 7 + (789 / 8 : ℂ) * s ^ 8 + (105 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-108 : ℂ) * s + (-2583 / 2 : ℂ) * s ^ 2 + (-16341 / 4 : ℂ) * s ^ 3 + (-25517 / 4 : ℂ) * s ^ 4 + (-11565 / 2 : ℂ) * s ^ 5 + (-12825 / 4 : ℂ) * s ^ 6 + (-4347 / 4 : ℂ) * s ^ 7 + (-857 / 4 : ℂ) * s ^ 8 + (-43 / 2 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((432 : ℂ) * s + (5979 / 2 : ℂ) * s ^ 2 + (13915 / 2 : ℂ) * s ^ 3 + (69721 / 8 : ℂ) * s ^ 4 + (53803 / 8 : ℂ) * s ^ 5 + (12929 / 4 : ℂ) * s ^ 6 + (3683 / 4 : ℂ) * s ^ 7 + (1113 / 8 : ℂ) * s ^ 8 + (67 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-636 : ℂ) * s + (-6313 / 2 : ℂ) * s ^ 2 + (-19781 / 4 : ℂ) * s ^ 3 + (-4568 : ℂ) * s ^ 4 + (-2889 : ℂ) * s ^ 5 + (-1182 : ℂ) * s ^ 6 + (-1055 / 4 : ℂ) * s ^ 7 + (-47 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((492 : ℂ) * s + (1064 : ℂ) * s ^ 2 + (999 : ℂ) * s ^ 3 + (443 : ℂ) * s ^ 4 + (208 : ℂ) * s ^ 5 + (91 : ℂ) * s ^ 6 + (15 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-72 : ℂ) * s + (210 : ℂ) * s ^ 2 + (177 : ℂ) * s ^ 3 + (132 : ℂ) * s ^ 4 + (33 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s + (-18 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [srcCoeff_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt0 s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((-81 / 16 : ℂ) * s ^ 3 + (-729 / 32 : ℂ) * s ^ 4 + (-675 / 16 : ℂ) * s ^ 5 + (-1329 / 32 : ℂ) * s ^ 6 + (-375 / 16 : ℂ) * s ^ 7 + (-243 / 32 : ℂ) * s ^ 8 + (-21 / 16 : ℂ) * s ^ 9 + (-3 / 32 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-27 / 4 : ℂ) * s ^ 2 + (-63 / 4 : ℂ) * s ^ 3 + (291 / 16 : ℂ) * s ^ 4 + (1495 / 16 : ℂ) * s ^ 5 + (925 / 8 : ℂ) * s ^ 6 + (517 / 8 : ℂ) * s ^ 7 + (271 / 16 : ℂ) * s ^ 8 + (27 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((9 / 2 : ℂ) * s + (69 / 2 : ℂ) * s ^ 2 + (1997 / 16 : ℂ) * s ^ 3 + (3005 / 32 : ℂ) * s ^ 4 + (-633 / 16 : ℂ) * s ^ 5 + (-2871 / 32 : ℂ) * s ^ 6 + (-861 / 16 : ℂ) * s ^ 7 + (-441 / 32 : ℂ) * s ^ 8 + (-15 / 16 : ℂ) * s ^ 9 + (3 / 32 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((18 : ℂ) + (108 : ℂ) * s + (179 / 2 : ℂ) * s ^ 2 + (109 / 8 : ℂ) * s ^ 3 + (103 / 16 : ℂ) * s ^ 4 + (325 / 16 : ℂ) * s ^ 5 + (125 / 8 : ℂ) * s ^ 6 + (23 / 2 : ℂ) * s ^ 7 + (71 / 16 : ℂ) * s ^ 8 + (9 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((78 : ℂ) + (-113 / 2 : ℂ) * s + (-11 : ℂ) * s ^ 2 + (-439 / 8 : ℂ) * s ^ 3 + (-85 : ℂ) * s ^ 4 + (-127 / 4 : ℂ) * s ^ 5 + (9 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (53 : ℂ) * s + (-293 / 4 : ℂ) * s ^ 2 + (-243 / 4 : ℂ) * s ^ 3 + (-43 / 4 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-66 : ℂ) + (-103 : ℂ) * s + (-33 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-18 : ℂ) + (-6 : ℂ) * s))))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [srcCoeff_qt0_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-135 / 4 : ℂ) * s ^ 3 + (-261 / 2 : ℂ) * s ^ 4 + (-3291 / 16 : ℂ) * s ^ 5 + (-2739 / 16 : ℂ) * s ^ 6 + (-651 / 8 : ℂ) * s ^ 7 + (-177 / 8 : ℂ) * s ^ 8 + (-51 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-9 / 2 : ℂ) * s ^ 2 + (93 / 2 : ℂ) * s ^ 3 + (1583 / 8 : ℂ) * s ^ 4 + (316 : ℂ) * s ^ 5 + (2169 / 8 : ℂ) * s ^ 6 + (271 / 2 : ℂ) * s ^ 7 + (313 / 8 : ℂ) * s ^ 8 + (6 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((54 : ℂ) * s + (297 / 2 : ℂ) * s ^ 2 + (1251 / 4 : ℂ) * s ^ 3 + (1745 / 4 : ℂ) * s ^ 4 + (4593 / 16 : ℂ) * s ^ 5 + (705 / 16 : ℂ) * s ^ 6 + (-293 / 8 : ℂ) * s ^ 7 + (-149 / 8 : ℂ) * s ^ 8 + (-51 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((72 : ℂ) * s + (201 / 2 : ℂ) * s ^ 2 + (-213 : ℂ) * s ^ 3 + (-5007 / 8 : ℂ) * s ^ 4 + (-4265 / 8 : ℂ) * s ^ 5 + (-753 / 4 : ℂ) * s ^ 6 + (-89 / 4 : ℂ) * s ^ 7 + (13 / 8 : ℂ) * s ^ 8 + (3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-90 : ℂ) * s + (-537 / 2 : ℂ) * s ^ 2 + (-429 / 2 : ℂ) * s ^ 3 + (225 / 4 : ℂ) * s ^ 4 + (495 / 4 : ℂ) * s ^ 5 + (177 / 4 : ℂ) * s ^ 6 + (19 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-36 : ℂ) * s + (6 : ℂ) * s ^ 2 + (96 : ℂ) * s ^ 3 + (66 : ℂ) * s ^ 4 + (12 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((18 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [srcCoeff_qt1_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((-135 / 2 : ℂ) * s ^ 2 + (-549 / 2 : ℂ) * s ^ 3 + (-3687 / 8 : ℂ) * s ^ 4 + (-1659 / 4 : ℂ) * s ^ 5 + (-867 / 4 : ℂ) * s ^ 6 + (-66 : ℂ) * s ^ 7 + (-87 / 8 : ℂ) * s ^ 8 + (-3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-54 : ℂ) * s + (135 / 2 : ℂ) * s ^ 2 + (1473 / 2 : ℂ) * s ^ 3 + (11281 / 8 : ℂ) * s ^ 4 + (5119 / 4 : ℂ) * s ^ 5 + (1277 / 2 : ℂ) * s ^ 6 + (713 / 4 : ℂ) * s ^ 7 + (207 / 8 : ℂ) * s ^ 8 + (3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((180 : ℂ) * s + (249 : ℂ) * s ^ 2 + (-1005 / 2 : ℂ) * s ^ 3 + (-11459 / 8 : ℂ) * s ^ 4 + (-2735 / 2 : ℂ) * s ^ 5 + (-1305 / 2 : ℂ) * s ^ 6 + (-649 / 4 : ℂ) * s ^ 7 + (-153 / 8 : ℂ) * s ^ 8 + (-3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-168 : ℂ) * s + (-422 : ℂ) * s ^ 2 + (-307 / 2 : ℂ) * s ^ 3 + (3483 / 8 : ℂ) * s ^ 4 + (2183 / 4 : ℂ) * s ^ 5 + (513 / 2 : ℂ) * s ^ 6 + (215 / 4 : ℂ) * s ^ 7 + (33 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((12 : ℂ) * s + (311 / 2 : ℂ) * s ^ 2 + (238 : ℂ) * s ^ 3 + (361 / 4 : ℂ) * s ^ 4 + (-137 / 4 : ℂ) * s ^ 5 + (-103 / 4 : ℂ) * s ^ 6 + (-15 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((30 : ℂ) * s + (53 / 2 : ℂ) * s ^ 2 + (-41 : ℂ) * s ^ 3 + (-85 / 2 : ℂ) * s ^ 4 + (-9 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-9 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [srcCoeff_qt2_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((-27 / 4 : ℂ) * s ^ 2 + (-225 / 8 : ℂ) * s ^ 3 + (-375 / 8 : ℂ) * s ^ 4 + (-159 / 4 : ℂ) * s ^ 5 + (-18 : ℂ) * s ^ 6 + (-33 / 8 : ℂ) * s ^ 7 + (-3 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3 : ℂ) * s + (223 / 4 : ℂ) * s ^ 2 + (145 : ℂ) * s ^ 3 + (649 / 4 : ℂ) * s ^ 4 + (94 : ℂ) * s ^ 5 + (105 / 4 : ℂ) * s ^ 6 + (2 : ℂ) * s ^ 7 + (-1 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1 : ℂ) * s + (-475 / 4 : ℂ) * s ^ 2 + (-2229 / 8 : ℂ) * s ^ 3 + (-1659 / 8 : ℂ) * s ^ 4 + (-241 / 4 : ℂ) * s ^ 5 + (-13 / 2 : ℂ) * s ^ 6 + (15 / 8 : ℂ) * s ^ 7 + (5 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-54 : ℂ) * s + (893 / 4 : ℂ) * s ^ 2 + (601 / 4 : ℂ) * s ^ 3 + (105 / 2 : ℂ) * s ^ 4 + (13 / 2 : ℂ) * s ^ 5 + (17 / 4 : ℂ) * s ^ 6 + (5 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-3 : ℂ) * s + (-163 / 2 : ℂ) * s ^ 2 + (-57 / 2 : ℂ) * s ^ 3 + (-53 / 2 : ℂ) * s ^ 4 + (-9 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((41 : ℂ) * s + (36 : ℂ) * s ^ 2 + (-5 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((12 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [srcCoeff_qT0_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-45 : ℂ) * s ^ 2 + (-159 : ℂ) * s ^ 3 + (-885 / 4 : ℂ) * s ^ 4 + (-309 / 2 : ℂ) * s ^ 5 + (-57 : ℂ) * s ^ 6 + (-21 / 2 : ℂ) * s ^ 7 + (-3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((66 : ℂ) * s + (421 : ℂ) * s ^ 2 + (820 : ℂ) * s ^ 3 + (715 : ℂ) * s ^ 4 + (297 : ℂ) * s ^ 5 + (42 : ℂ) * s ^ 6 + (-7 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-188 : ℂ) * s + (-528 : ℂ) * s ^ 2 + (-753 / 2 : ℂ) * s ^ 3 + (37 / 4 : ℂ) * s ^ 4 + (209 / 2 : ℂ) * s ^ 5 + (42 : ℂ) * s ^ 6 + (8 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-10 : ℂ) * s + (-684 : ℂ) * s ^ 2 + (-2313 / 2 : ℂ) * s ^ 3 + (-619 : ℂ) * s ^ 4 + (-132 : ℂ) * s ^ 5 + (-13 : ℂ) * s ^ 6 + (-3 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((320 : ℂ) * s + (1028 : ℂ) * s ^ 2 + (595 : ℂ) * s ^ 3 + (140 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-116 : ℂ) * s + (-84 : ℂ) * s ^ 2 + (16 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-72 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [srcCoeff_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((-120 : ℂ) * s + (-418 : ℂ) * s ^ 2 + (-558 : ℂ) * s ^ 3 + (-693 / 2 : ℂ) * s ^ 4 + (-171 / 2 : ℂ) * s ^ 5 + (15 / 2 : ℂ) * s ^ 6 + (15 / 2 : ℂ) * s ^ 7 + (1 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((464 : ℂ) * s + (1528 : ℂ) * s ^ 2 + (2034 : ℂ) * s ^ 3 + (1417 : ℂ) * s ^ 4 + (558 : ℂ) * s ^ 5 + (126 : ℂ) * s ^ 6 + (16 : ℂ) * s ^ 7 + (1 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-894 : ℂ) * s + (-2993 : ℂ) * s ^ 2 + (-4067 : ℂ) * s ^ 3 + (-5801 / 2 : ℂ) * s ^ 4 + (-2203 / 2 : ℂ) * s ^ 5 + (-405 / 2 : ℂ) * s ^ 6 + (-27 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((1062 : ℂ) * s + (3356 : ℂ) * s ^ 2 + (4097 : ℂ) * s ^ 3 + (2211 : ℂ) * s ^ 4 + (545 : ℂ) * s ^ 5 + (49 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-590 : ℂ) * s + (-1545 : ℂ) * s ^ 2 + (-1158 : ℂ) * s ^ 3 + (-339 : ℂ) * s ^ 4 + (-40 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-30 : ℂ) * s + (-144 : ℂ) * s ^ 2 + (-42 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((108 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [srcCoeff_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((180 : ℂ) * s + (732 : ℂ) * s ^ 2 + (1229 : ℂ) * s ^ 3 + (1106 : ℂ) * s ^ 4 + (578 : ℂ) * s ^ 5 + (176 : ℂ) * s ^ 6 + (29 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-804 : ℂ) * s + (-3022 : ℂ) * s ^ 2 + (-4626 : ℂ) * s ^ 3 + (-3714 : ℂ) * s ^ 4 + (-1672 : ℂ) * s ^ 5 + (-414 : ℂ) * s ^ 6 + (-50 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1368 : ℂ) * s + (4658 : ℂ) * s ^ 2 + (6295 : ℂ) * s ^ 3 + (4314 : ℂ) * s ^ 4 + (1580 : ℂ) * s ^ 5 + (292 : ℂ) * s ^ 6 + (21 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1032 : ℂ) * s + (-3082 : ℂ) * s ^ 2 + (-3444 : ℂ) * s ^ 3 + (-1904 : ℂ) * s ^ 4 + (-516 : ℂ) * s ^ 5 + (-54 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((228 : ℂ) * s + (522 : ℂ) * s ^ 2 + (510 : ℂ) * s ^ 3 + (198 : ℂ) * s ^ 4 + (30 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((108 : ℂ) * s + (192 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-48 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [srcCoeff_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  ring

/-- The source-only radial current of the SS harmonic sources at the fundamental harmonic. -/
def srcCurrentSS (s r : ℂ) : ℂ := (((60 : ℂ) * s + (1319 / 4 : ℂ) * s ^ 2 + (13025 / 16 : ℂ) * s ^ 3 + (37951 / 32 : ℂ) * s ^ 4 + (4481 / 4 : ℂ) * s ^ 5 + (22645 / 32 : ℂ) * s ^ 6 + (4757 / 16 : ℂ) * s ^ 7 + (2553 / 32 : ℂ) * s ^ 8 + (99 / 8 : ℂ) * s ^ 9 + (27 / 32 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-379 : ℂ) * s + (-1870 : ℂ) * s ^ 2 + (-15985 / 4 : ℂ) * s ^ 3 + (-77289 / 16 : ℂ) * s ^ 4 + (-59115 / 16 : ℂ) * s ^ 5 + (-15309 / 8 : ℂ) * s ^ 6 + (-5493 / 8 : ℂ) * s ^ 7 + (-2629 / 16 : ℂ) * s ^ 8 + (-375 / 16 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1591 / 2 : ℂ) * s + (13301 / 4 : ℂ) * s ^ 2 + (93887 / 16 : ℂ) * s ^ 3 + (184965 / 32 : ℂ) * s ^ 4 + (14741 / 4 : ℂ) * s ^ 5 + (51459 / 32 : ℂ) * s ^ 6 + (7827 / 16 : ℂ) * s ^ 7 + (3195 / 32 : ℂ) * s ^ 8 + (97 / 8 : ℂ) * s ^ 9 + (21 / 32 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((18 : ℂ) + (-178 : ℂ) * s + (-6395 / 4 : ℂ) * s ^ 2 + (-20405 / 8 : ℂ) * s ^ 3 + (-32941 / 16 : ℂ) * s ^ 4 + (-17413 / 16 : ℂ) * s ^ 5 + (-3169 / 8 : ℂ) * s ^ 6 + (-99 : ℂ) * s ^ 7 + (-245 / 16 : ℂ) * s ^ 8 + (-17 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((78 : ℂ) + (-491 / 2 : ℂ) * s + (-325 / 2 : ℂ) * s ^ 2 + (-1523 / 8 : ℂ) * s ^ 3 + (-207 / 2 : ℂ) * s ^ 4 + (-101 / 4 : ℂ) * s ^ 5 + (-6 : ℂ) * s ^ 6 + (-7 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (56 : ℂ) * s + (1 / 4 : ℂ) * s ^ 2 + (217 / 4 : ℂ) * s ^ 3 + (107 / 4 : ℂ) * s ^ 4 + (11 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-66 : ℂ) + (-103 : ℂ) * s + (-24 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-18 : ℂ) + (-6 : ℂ) * s))))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3)

theorem srcCurrentSS_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCurrent s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = srcCurrentSS s r := by
  unfold srcCurrent
  rw [srcPieceSS_qtr0 s r hr hf hs hs3 hs1, srcPieceSS_qtr1 s r hr hf hs hs3 hs1, srcPieceSS_qtr2 s r hr hf hs hs3 hs1, srcPieceSS_qt0 s r hr hf hs hs3 hs1, srcPieceSS_qt1 s r hr hf hs hs3 hs1, srcPieceSS_qt2 s r hr hf hs hs3 hs1, srcPieceSS_qT0 s r hr hf hs hs3 hs1, srcPieceSS_qT1 s r hr hf hs hs3 hs1, srcPieceSS_qT2 s r hr hf hs hs3 hs1, srcPieceSS_qT3 s r hr hf hs hs3 hs1]
  unfold srcCurrentSS
  simp only [← add_div]
  ring

/-! ## The VV source current at the fundamental harmonic -/
theorem srcPieceVV_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr0 s r ((s + 1) * (s + 2)) * vvSourceTR s r ((s + 1) * (s + 2)) = (((-9 : ℂ) * s + (-24 : ℂ) * s ^ 2 + (-97 / 4 : ℂ) * s ^ 3 + (-47 / 4 : ℂ) * s ^ 4 + (-11 / 4 : ℂ) * s ^ 5 + (-1 / 4 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((9 : ℂ) + (69 : ℂ) * s + (235 / 4 : ℂ) * s ^ 2 + (-389 / 4 : ℂ) * s ^ 3 + (-695 / 4 : ℂ) * s ^ 4 + (-405 / 4 : ℂ) * s ^ 5 + (-26 : ℂ) * s ^ 6 + (-5 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-60 : ℂ) + (130 : ℂ) * s + (1201 / 2 : ℂ) * s ^ 2 + (2447 / 4 : ℂ) * s ^ 3 + (493 / 4 : ℂ) * s ^ 4 + (-743 / 4 : ℂ) * s ^ 5 + (-575 / 4 : ℂ) * s ^ 6 + (-40 : ℂ) * s ^ 7 + (-4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-129 : ℂ) + (-460 : ℂ) * s + (-385 / 4 : ℂ) * s ^ 2 + (3189 / 4 : ℂ) * s ^ 3 + (3591 / 4 : ℂ) * s ^ 4 + (1773 / 4 : ℂ) * s ^ 5 + (259 / 2 : ℂ) * s ^ 6 + (47 / 2 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-36 : ℂ) + (-324 : ℂ) * s + (-716 : ℂ) * s ^ 2 + (-1293 / 2 : ℂ) * s ^ 3 + (-511 / 2 : ℂ) * s ^ 4 + (-75 / 2 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-72 : ℂ) * s + (-132 : ℂ) * s ^ 2 + (-72 : ℂ) * s ^ 3 + (-12 : ℂ) * s ^ 4))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  rw [srcCoeff_qtr0_lam s r hs hs3 hs1, vvSourceTR_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr1 s r ((s + 1) * (s + 2)) * vvSourceTR1 s r ((s + 1) * (s + 2)) = (((-90 : ℂ) + (-231 : ℂ) * s + (-401 / 2 : ℂ) * s ^ 2 + (-181 / 4 : ℂ) * s ^ 3 + (131 / 4 : ℂ) * s ^ 4 + (95 / 4 : ℂ) * s ^ 5 + (23 / 4 : ℂ) * s ^ 6 + (1 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((141 : ℂ) + (416 : ℂ) * s + (1869 / 4 : ℂ) * s ^ 2 + (1143 / 4 : ℂ) * s ^ 3 + (639 / 4 : ℂ) * s ^ 4 + (413 / 4 : ℂ) * s ^ 5 + (47 : ℂ) * s ^ 6 + (11 : ℂ) * s ^ 7 + (1 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-366 : ℂ) + (-1238 : ℂ) * s + (-1380 : ℂ) * s ^ 2 + (-1503 / 4 : ℂ) * s ^ 3 + (1495 / 4 : ℂ) * s ^ 4 + (1347 / 4 : ℂ) * s ^ 5 + (445 / 4 : ℂ) * s ^ 6 + (17 : ℂ) * s ^ 7 + (1 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((363 : ℂ) + (625 : ℂ) * s + (-2943 / 4 : ℂ) * s ^ 2 + (-9437 / 4 : ℂ) * s ^ 3 + (-8027 / 4 : ℂ) * s ^ 4 + (-3105 / 4 : ℂ) * s ^ 5 + (-281 / 2 : ℂ) * s ^ 6 + (-19 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((168 : ℂ) + (854 : ℂ) * s + (1718 : ℂ) * s ^ 2 + (3371 / 2 : ℂ) * s ^ 3 + (1665 / 2 : ℂ) * s ^ 4 + (393 / 2 : ℂ) * s ^ 5 + (35 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((240 : ℂ) * s + (440 : ℂ) * s ^ 2 + (240 : ℂ) * s ^ 3 + (40 : ℂ) * s ^ 4))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  rw [srcCoeff_qtr1_lam s r hs hs3 hs1, vvSourceTR1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr2 s r ((s + 1) * (s + 2)) * vvSourceTR2 s r ((s + 1) * (s + 2)) = (((270 : ℂ) + (918 : ℂ) * s + (2583 / 2 : ℂ) * s ^ 2 + (982 : ℂ) * s ^ 3 + (438 : ℂ) * s ^ 4 + (115 : ℂ) * s ^ 5 + (33 / 2 : ℂ) * s ^ 6 + (1 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-882 : ℂ) + (-2649 : ℂ) * s + (-2948 : ℂ) * s ^ 2 + (-1294 : ℂ) * s ^ 3 + (124 : ℂ) * s ^ 4 + (363 : ℂ) * s ^ 5 + (152 : ℂ) * s ^ 6 + (28 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((882 : ℂ) + (2004 : ℂ) * s + (1419 / 2 : ℂ) * s ^ 2 + (-1818 : ℂ) * s ^ 3 + (-2345 : ℂ) * s ^ 4 + (-1224 : ℂ) * s ^ 5 + (-649 / 2 : ℂ) * s ^ 6 + (-42 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-102 : ℂ) + (371 : ℂ) * s + (2025 : ℂ) * s ^ 2 + (3123 : ℂ) * s ^ 3 + (2298 : ℂ) * s ^ 4 + (885 : ℂ) * s ^ 5 + (171 : ℂ) * s ^ 6 + (13 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-168 : ℂ) + (-464 : ℂ) * s + (-748 : ℂ) * s ^ 2 + (-813 : ℂ) * s ^ 3 + (-485 : ℂ) * s ^ 4 + (-139 : ℂ) * s ^ 5 + (-15 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-180 : ℂ) * s + (-330 : ℂ) * s ^ 2 + (-180 : ℂ) * s ^ 3 + (-30 : ℂ) * s ^ 4))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  rw [srcCoeff_qtr2_lam s r hs hs3 hs1, vvSourceTR2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt0 s r ((s + 1) * (s + 2)) * vvSourceT s r ((s + 1) * (s + 2)) = (((-81 / 2 : ℂ) * s + (-162 : ℂ) * s ^ 2 + (-2133 / 8 : ℂ) * s ^ 3 + (-1875 / 8 : ℂ) * s ^ 4 + (-477 / 4 : ℂ) * s ^ 5 + (-141 / 4 : ℂ) * s ^ 6 + (-45 / 8 : ℂ) * s ^ 7 + (-3 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((54 : ℂ) + (171 : ℂ) * s + (921 / 2 : ℂ) * s ^ 2 + (3165 / 4 : ℂ) * s ^ 3 + (1413 / 2 : ℂ) * s ^ 4 + (327 : ℂ) * s ^ 5 + (75 : ℂ) * s ^ 6 + (27 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((234 : ℂ) + (435 / 2 : ℂ) * s + (-381 : ℂ) * s ^ 2 + (-6135 / 8 : ℂ) * s ^ 3 + (-4977 / 8 : ℂ) * s ^ 4 + (-1101 / 4 : ℂ) * s ^ 5 + (-237 / 4 : ℂ) * s ^ 6 + (-27 / 8 : ℂ) * s ^ 7 + (3 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-36 : ℂ) + (303 : ℂ) * s + (672 : ℂ) * s ^ 2 + (1827 / 4 : ℂ) * s ^ 3 + (345 / 2 : ℂ) * s ^ 4 + (66 : ℂ) * s ^ 5 + (39 / 2 : ℂ) * s ^ 6 + (9 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-198 : ℂ) + (-552 : ℂ) * s + (-1071 / 2 : ℂ) * s ^ 2 + (-411 / 2 : ℂ) * s ^ 3 + (-45 / 2 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-54 : ℂ) + (-99 : ℂ) * s + (-54 : ℂ) * s ^ 2 + (-9 : ℂ) * s ^ 3))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  rw [srcCoeff_qt0_lam s r hs hs3 hs1, vvSourceT_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt1 s r ((s + 1) * (s + 2)) * vvSourceT1 s r ((s + 1) * (s + 2)) = (((-270 : ℂ) * s + (-909 : ℂ) * s ^ 2 + (-2517 / 2 : ℂ) * s ^ 3 + (-3735 / 4 : ℂ) * s ^ 4 + (-402 : ℂ) * s ^ 5 + (-201 / 2 : ℂ) * s ^ 6 + (-27 / 2 : ℂ) * s ^ 7 + (-3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((324 : ℂ) + (1242 : ℂ) * s + (2205 : ℂ) * s ^ 2 + (4719 / 2 : ℂ) * s ^ 3 + (3219 / 2 : ℂ) * s ^ 4 + (693 : ℂ) * s ^ 5 + (180 : ℂ) * s ^ 6 + (51 / 2 : ℂ) * s ^ 7 + (3 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((108 : ℂ) + (900 : ℂ) * s + (1521 : ℂ) * s ^ 2 + (1587 / 2 : ℂ) * s ^ 3 + (-399 / 4 : ℂ) * s ^ 4 + (-240 : ℂ) * s ^ 5 + (-177 / 2 : ℂ) * s ^ 6 + (-27 / 2 : ℂ) * s ^ 7 + (-3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-972 : ℂ) + (-3402 : ℂ) * s + (-4455 : ℂ) * s ^ 2 + (-5445 / 2 : ℂ) * s ^ 3 + (-774 : ℂ) * s ^ 4 + (-69 : ℂ) * s ^ 5 + (9 : ℂ) * s ^ 6 + (3 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((324 : ℂ) + (1134 : ℂ) * s + (1422 : ℂ) * s ^ 2 + (792 : ℂ) * s ^ 3 + (198 : ℂ) * s ^ 4 + (18 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((216 : ℂ) + (396 : ℂ) * s + (216 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  rw [srcCoeff_qt1_lam s r hs hs3 hs1, vvSourceT1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt2 s r ((s + 1) * (s + 2)) * vvSourceT2 s r ((s + 1) * (s + 2)) = (((-540 : ℂ) + (-1926 : ℂ) * s + (-2859 : ℂ) * s ^ 2 + (-4605 / 2 : ℂ) * s ^ 3 + (-2181 / 2 : ℂ) * s ^ 4 + (-609 / 2 : ℂ) * s ^ 5 + (-93 / 2 : ℂ) * s ^ 6 + (-3 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((1980 : ℂ) + (6834 : ℂ) * s + (9699 : ℂ) * s ^ 2 + (14715 / 2 : ℂ) * s ^ 3 + (6447 / 2 : ℂ) * s ^ 4 + (1629 / 2 : ℂ) * s ^ 5 + (219 / 2 : ℂ) * s ^ 6 + (6 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2520 : ℂ) + (-8472 : ℂ) * s + (-11553 : ℂ) * s ^ 2 + (-16509 / 2 : ℂ) * s ^ 3 + (-6615 / 2 : ℂ) * s ^ 4 + (-1461 / 2 : ℂ) * s ^ 5 + (-159 / 2 : ℂ) * s ^ 6 + (-3 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((1080 : ℂ) + (3816 : ℂ) * s + (5265 : ℂ) * s ^ 2 + (7233 / 2 : ℂ) * s ^ 3 + (2613 / 2 : ℂ) * s ^ 4 + (471 / 2 : ℂ) * s ^ 5 + (33 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((180 : ℂ) + (78 : ℂ) * s + (-372 : ℂ) * s ^ 2 + (-387 : ℂ) * s ^ 3 + (-132 : ℂ) * s ^ 4 + (-15 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-180 : ℂ) + (-330 : ℂ) * s + (-180 : ℂ) * s ^ 2 + (-30 : ℂ) * s ^ 3))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  rw [srcCoeff_qt2_lam s r hs hs3 hs1, vvSourceT2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT0 s r ((s + 1) * (s + 2)) * vvSourceTF s r ((s + 1) * (s + 2)) = (((297 : ℂ) * s + (1413 : ℂ) * s ^ 2 + (11445 / 4 : ℂ) * s ^ 3 + (3222 : ℂ) * s ^ 4 + (8835 / 4 : ℂ) * s ^ 5 + (945 : ℂ) * s ^ 6 + (987 / 4 : ℂ) * s ^ 7 + (36 : ℂ) * s ^ 8 + (9 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-132 : ℂ) + (-1343 : ℂ) * s + (-9167 / 2 : ℂ) * s ^ 2 + (-15499 / 2 : ℂ) * s ^ 3 + (-14783 / 2 : ℂ) * s ^ 4 + (-8253 / 2 : ℂ) * s ^ 5 + (-2609 / 2 : ℂ) * s ^ 6 + (-397 / 2 : ℂ) * s ^ 7 + (-9 / 2 : ℂ) * s ^ 8 + (3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-572 : ℂ) + (883 : ℂ) * s + (6163 : ℂ) * s ^ 2 + (36905 / 4 : ℂ) * s ^ 3 + (6626 : ℂ) * s ^ 4 + (10267 / 4 : ℂ) * s ^ 5 + (449 : ℂ) * s ^ 6 + (-145 / 4 : ℂ) * s ^ 7 + (-30 : ℂ) * s ^ 8 + (-15 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((88 : ℂ) + (-311 : ℂ) * s + (-2303 / 2 : ℂ) * s ^ 2 + (-1316 : ℂ) * s ^ 3 + (-1925 / 2 : ℂ) * s ^ 4 + (-635 : ℂ) * s ^ 5 + (-613 / 2 : ℂ) * s ^ 6 + (-78 : ℂ) * s ^ 7 + (-15 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((484 : ℂ) + (1716 : ℂ) * s + (2341 : ℂ) * s ^ 2 + (1518 : ℂ) * s ^ 3 + (454 : ℂ) * s ^ 4 + (42 : ℂ) * s ^ 5 + (-3 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((132 : ℂ) + (342 : ℂ) * s + (318 : ℂ) * s ^ 2 + (126 : ℂ) * s ^ 3 + (18 : ℂ) * s ^ 4))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  rw [srcCoeff_qT0_lam s r hs hs3 hs1, vvSourceTF_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT1 s r ((s + 1) * (s + 2)) * vvSourceTF1 s r ((s + 1) * (s + 2)) = (((1980 : ℂ) * s + (8166 : ℂ) * s ^ 2 + (14319 : ℂ) * s ^ 3 + (27921 / 2 : ℂ) * s ^ 4 + (16563 / 2 : ℂ) * s ^ 5 + (3060 : ℂ) * s ^ 6 + (687 : ℂ) * s ^ 7 + (171 / 2 : ℂ) * s ^ 8 + (9 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2904 : ℂ) + (-16280 : ℂ) * s + (-37294 : ℂ) * s ^ 2 + (-45656 : ℂ) * s ^ 3 + (-32318 : ℂ) * s ^ 4 + (-13012 : ℂ) * s ^ 5 + (-2466 : ℂ) * s ^ 6 + (56 : ℂ) * s ^ 7 + (102 : ℂ) * s ^ 8 + (12 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((2464 : ℂ) + (4272 : ℂ) * s + (-1758 : ℂ) * s ^ 2 + (-9384 : ℂ) * s ^ 3 + (-19255 / 2 : ℂ) * s ^ 4 + (-10659 / 2 : ℂ) * s ^ 5 + (-1928 : ℂ) * s ^ 6 + (-474 : ℂ) * s ^ 7 + (-141 / 2 : ℂ) * s ^ 8 + (-9 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((5368 : ℂ) + (28604 : ℂ) * s + (55474 : ℂ) * s ^ 2 + (52407 : ℂ) * s ^ 3 + (26383 : ℂ) * s ^ 4 + (7180 : ℂ) * s ^ 5 + (1062 : ℂ) * s ^ 6 + (105 : ℂ) * s ^ 7 + (9 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-3344 : ℂ) + (-12888 : ℂ) * s + (-19440 : ℂ) * s ^ 2 + (-14508 : ℂ) * s ^ 3 + (-5548 : ℂ) * s ^ 4 + (-996 : ℂ) * s ^ 5 + (-60 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-1584 : ℂ) + (-4104 : ℂ) * s + (-3816 : ℂ) * s ^ 2 + (-1512 : ℂ) * s ^ 3 + (-216 : ℂ) * s ^ 4))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  rw [srcCoeff_qT1_lam s r hs hs3 hs1, vvSourceTF1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT2 s r ((s + 1) * (s + 2)) * vvSourceTF2 s r ((s + 1) * (s + 2)) = (((5280 : ℂ) + (21512 : ℂ) * s + (36620 : ℂ) * s ^ 2 + (33454 : ℂ) * s ^ 3 + (17159 : ℂ) * s ^ 4 + (4318 : ℂ) * s ^ 5 + (-16 : ℂ) * s ^ 6 + (-310 : ℂ) * s ^ 7 + (-75 : ℂ) * s ^ 8 + (-6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-14080 : ℂ) + (-61296 : ℂ) * s + (-113880 : ℂ) * s ^ 2 + (-118252 : ℂ) * s ^ 3 + (-75474 : ℂ) * s ^ 4 + (-30682 : ℂ) * s ^ 5 + (-7976 : ℂ) * s ^ 6 + (-1300 : ℂ) * s ^ 7 + (-126 : ℂ) * s ^ 8 + (-6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((22440 : ℂ) + (104120 : ℂ) * s + (203506 : ℂ) * s ^ 2 + (218282 : ℂ) * s ^ 3 + (140129 : ℂ) * s ^ 4 + (54926 : ℂ) * s ^ 5 + (12768 : ℂ) * s ^ 6 + (1596 : ℂ) * s ^ 7 + (81 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-19800 : ℂ) + (-89668 : ℂ) * s + (-164752 : ℂ) * s ^ 2 + (-159202 : ℂ) * s ^ 3 + (-87416 : ℂ) * s ^ 4 + (-27268 : ℂ) * s ^ 5 + (-4464 : ℂ) * s ^ 6 + (-294 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((2200 : ℂ) + (11904 : ℂ) * s + (23134 : ℂ) * s ^ 2 + (21606 : ℂ) * s ^ 3 + (10462 : ℂ) * s ^ 4 + (2526 : ℂ) * s ^ 5 + (240 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((3960 : ℂ) + (10260 : ℂ) * s + (9540 : ℂ) * s ^ 2 + (3780 : ℂ) * s ^ 3 + (540 : ℂ) * s ^ 4))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  rw [srcCoeff_qT2_lam s r hs hs3 hs1, vvSourceTF2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT3 s r ((s + 1) * (s + 2)) * vvSourceTF3 s r ((s + 1) * (s + 2)) = (((-7920 : ℂ) + (-36888 : ℂ) * s + (-74908 : ℂ) * s ^ 2 + (-87218 : ℂ) * s ^ 3 + (-64270 : ℂ) * s ^ 4 + (-31124 : ℂ) * s ^ 5 + (-9916 : ℂ) * s ^ 6 + (-2006 : ℂ) * s ^ 7 + (-234 : ℂ) * s ^ 8 + (-12 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((29040 : ℂ) + (131120 : ℂ) * s + (255484 : ℂ) * s ^ 2 + (281632 : ℂ) * s ^ 3 + (193048 : ℂ) * s ^ 4 + (84916 : ℂ) * s ^ 5 + (23764 : ℂ) * s ^ 6 + (4016 : ℂ) * s ^ 7 + (360 : ℂ) * s ^ 8 + (12 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-36960 : ℂ) + (-161672 : ℂ) * s + (-301128 : ℂ) * s ^ 2 + (-311762 : ℂ) * s ^ 3 + (-196002 : ℂ) * s ^ 4 + (-76472 : ℂ) * s ^ 5 + (-18024 : ℂ) * s ^ 6 + (-2334 : ℂ) * s ^ 7 + (-126 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((15840 : ℂ) + (69288 : ℂ) * s + (126660 : ℂ) * s ^ 2 + (125220 : ℂ) * s ^ 3 + (72168 : ℂ) * s ^ 4 + (24192 : ℂ) * s ^ 5 + (4356 : ℂ) * s ^ 6 + (324 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((2640 : ℂ) + (4992 : ℂ) * s + (252 : ℂ) * s ^ 2 + (-5352 : ℂ) * s ^ 3 + (-4584 : ℂ) * s ^ 4 + (-1512 : ℂ) * s ^ 5 + (-180 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-2640 : ℂ) + (-6840 : ℂ) * s + (-6360 : ℂ) * s ^ 2 + (-2520 : ℂ) * s ^ 3 + (-360 : ℂ) * s ^ 4))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  rw [srcCoeff_qT3_lam s r hs hs3 hs1, vvSourceTF3_lam s r hs hs3 hs1]
  field_simp
  ring

/-- The source-only radial current of the VV harmonic sources at the fundamental harmonic. -/
def srcCurrentVV (s r : ℂ) : ℂ := (((-3000 : ℂ) + (-29315 / 2 : ℂ) * s + (-31572 : ℂ) * s ^ 2 + (-315991 / 8 : ℂ) * s ^ 3 + (-253825 / 8 : ℂ) * s ^ 4 + (-34011 / 2 : ℂ) * s ^ 5 + (-24349 / 4 : ℂ) * s ^ 6 + (-11223 / 8 : ℂ) * s ^ 7 + (-1509 / 8 : ℂ) * s ^ 8 + (-45 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((13550 : ℂ) + (58284 : ℂ) * s + (109669 : ℂ) * s ^ 2 + (477509 / 4 : ℂ) * s ^ 3 + (83514 : ℂ) * s ^ 4 + (39295 : ℂ) * s ^ 5 + (12555 : ℂ) * s ^ 6 + (10593 / 4 : ℂ) * s ^ 7 + (336 : ℂ) * s ^ 8 + (39 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-14350 : ℂ) + (-117711 / 2 : ℂ) * s + (-103700 : ℂ) * s ^ 2 + (-827581 / 8 : ℂ) * s ^ 3 + (-518015 / 8 : ℂ) * s ^ 4 + (-53255 / 2 : ℂ) * s ^ 5 + (-29277 / 4 : ℂ) * s ^ 6 + (-10665 / 8 : ℂ) * s ^ 7 + (-1207 / 8 : ℂ) * s ^ 8 + (-33 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1700 : ℂ) + (9166 : ℂ) * s + (37811 / 2 : ℂ) * s ^ 2 + (80083 / 4 : ℂ) * s ^ 3 + (24133 / 2 : ℂ) * s ^ 4 + (8507 / 2 : ℂ) * s ^ 5 + (1705 / 2 : ℂ) * s ^ 6 + (351 / 4 : ℂ) * s ^ 7 + (7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2250 : ℂ) + (6450 : ℂ) * s + (14111 / 2 : ℂ) * s ^ 2 + (7379 / 2 : ℂ) * s ^ 3 + (1839 / 2 : ℂ) * s ^ 4 + (169 / 2 : ℂ) * s ^ 5 + (-1 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-150 : ℂ) + (-387 : ℂ) * s + (-358 : ℂ) * s ^ 2 + (-141 : ℂ) * s ^ 3 + (-20 : ℂ) * s ^ 4))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3)

theorem srcCurrentVV_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCurrent s r ((s + 1) * (s + 2)) (vvSourceTR s r ((s + 1) * (s + 2))) (vvSourceTR1 s r ((s + 1) * (s + 2))) (vvSourceTR2 s r ((s + 1) * (s + 2))) (vvSourceT s r ((s + 1) * (s + 2))) (vvSourceT1 s r ((s + 1) * (s + 2))) (vvSourceT2 s r ((s + 1) * (s + 2))) (vvSourceTF s r ((s + 1) * (s + 2))) (vvSourceTF1 s r ((s + 1) * (s + 2))) (vvSourceTF2 s r ((s + 1) * (s + 2))) (vvSourceTF3 s r ((s + 1) * (s + 2))) = srcCurrentVV s r := by
  unfold srcCurrent
  rw [srcPieceVV_qtr0 s r hr hf hs hs3 hs1, srcPieceVV_qtr1 s r hr hf hs hs3 hs1, srcPieceVV_qtr2 s r hr hf hs hs3 hs1, srcPieceVV_qt0 s r hr hf hs hs3 hs1, srcPieceVV_qt1 s r hr hf hs hs3 hs1, srcPieceVV_qt2 s r hr hf hs hs3 hs1, srcPieceVV_qT0 s r hr hf hs hs3 hs1, srcPieceVV_qT1 s r hr hf hs hs3 hs1, srcPieceVV_qT2 s r hr hf hs hs3 hs1, srcPieceVV_qT3 s r hr hf hs hs3 hs1]
  unfold srcCurrentVV
  simp only [← add_div]
  ring

/-! ## The SS `++` Laurent response against the `−` mode -/

theorem ssLaurentA_lam (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : laurentMasterA s ((s + 1) * (s + 2)) = (((-6 : ℂ) + (-23 / 2 : ℂ) * s + (-5 / 2 : ℂ) * s ^ 2) / ((s + 3))) := by
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  rw [laurentMasterA_resolvents s _ hμ hres]
  all_goals (try field_simp)
  all_goals (try ring_nf)
  all_goals (try field_simp)
  all_goals (try ring)

theorem ssLaurentB_lam (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) : laurentMasterB s ((s + 1) * (s + 2)) = (((1 / 2 : ℂ) * s + (11 / 8 : ℂ) * s ^ 2 + (11 / 8 : ℂ) * s ^ 3 + (5 / 8 : ℂ) * s ^ 4 + (1 / 8 : ℂ) * s ^ 5) / ((s + 3))) := by
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  rw [laurentMasterB_resolvent s _ hμ]
  all_goals (try field_simp)
  all_goals (try ring)

/-- The radial current with the SS Laurent coefficients at their actual values. -/
theorem evenCurrentSS_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    evenCurrentSS s r ((s + 1) * (s + 2)) (laurentMasterA s ((s + 1) * (s + 2))) (laurentMasterB s ((s + 1) * (s + 2))) = (((15 / 8 : ℂ) * s ^ 2 + (103 / 16 : ℂ) * s ^ 3 + (17 / 2 : ℂ) * s ^ 4 + (43 / 8 : ℂ) * s ^ 5 + (13 / 8 : ℂ) * s ^ 6 + (3 / 16 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((3 : ℂ) + (25 / 2 : ℂ) * s + (75 / 8 : ℂ) * s ^ 2 + (-19 / 2 : ℂ) * s ^ 3 + (-115 / 8 : ℂ) * s ^ 4 + (-23 / 4 : ℂ) * s ^ 5 + (-3 / 4 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((5 / 2 : ℂ) * s + (3 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-3 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2))))))) / (r ^ 7 * s * (s + 3)) := by
  unfold evenCurrentSS
  rw [srcCurrentSS_eq s r hr hf hs hs3 hs1, ssLaurentA_lam s hs hs3 hs1, ssLaurentB_lam s hs hs3, evenCurrent_lauR_lam s r hs hs3 hs1, evenCurrent_lauI1_lam s r hs hs3 hs1, evenCurrent_lauI3_lam s r hs hs3 hs1]
  unfold srcCurrentSS
  field_simp
  ring

/-- Slope of the linear boundary divergence of the SS flux `r²·(current)`. -/
def evenSlopeSS (s : ℂ) : ℂ := (((-3 : ℂ) + (-1 / 2 : ℂ) * s) / ((s + 3)))
/-- The `O(1/r)` remainder of the SS flux at the AdS boundary. -/
def evenRemSS (s r : ℂ) : ℂ := (((15 / 8 : ℂ) * s ^ 2 + (103 / 16 : ℂ) * s ^ 3 + (17 / 2 : ℂ) * s ^ 4 + (43 / 8 : ℂ) * s ^ 5 + (13 / 8 : ℂ) * s ^ 6 + (3 / 16 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((3 : ℂ) + (25 / 2 : ℂ) * s + (75 / 8 : ℂ) * s ^ 2 + (-19 / 2 : ℂ) * s ^ 3 + (-115 / 8 : ℂ) * s ^ 4 + (-23 / 4 : ℂ) * s ^ 5 + (-3 / 4 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((5 / 2 : ℂ) * s + (3 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 4))))) / (r ^ 5 * s * (s + 3))

/-- Boundary structure of the SS flux at the fundamental harmonic: a pure linear divergence
and no finite part. -/
theorem evenCurrentSS_boundary (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    r ^ 2 * evenCurrentSS s r ((s + 1) * (s + 2)) (laurentMasterA s ((s + 1) * (s + 2))) (laurentMasterB s ((s + 1) * (s + 2))) = evenSlopeSS s * r + evenRemSS s r := by
  rw [evenCurrentSS_eq s r hr hf hs hs3 hs1]
  unfold evenSlopeSS evenRemSS
  field_simp
  ring

/-! ## The VV `++` Laurent response against the `−` mode -/

theorem vvLaurentA_lam (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvLaurentMasterA s ((s + 1) * (s + 2)) = ((22 / 3 : ℂ) * s + (8 / 3 : ℂ) * s ^ 2) := by
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  rw [vvLaurentMasterA_eq s _ hμ]
  all_goals (try field_simp)
  all_goals (try ring_nf)
  all_goals (try field_simp)
  all_goals (try ring)

theorem vvLaurentB_lam (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) : vvLaurentMasterB s ((s + 1) * (s + 2)) = (((-25 : ℂ) * s + (-107 / 2 : ℂ) * s ^ 2 + (-41 : ℂ) * s ^ 3 + (-29 / 2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 5) / ((s + 3))) := by
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  unfold vvLaurentMasterB
  all_goals (try field_simp)
  all_goals (try ring)

/-- The radial current with the VV Laurent coefficients at their actual values. -/
theorem evenCurrentVV_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    evenCurrentVV s r ((s + 1) * (s + 2)) (vvLaurentMasterA s ((s + 1) * (s + 2))) (vvLaurentMasterB s ((s + 1) * (s + 2))) = (((-15 / 2 : ℂ) * s + (-103 / 4 : ℂ) * s ^ 2 + (-34 : ℂ) * s ^ 3 + (-43 / 2 : ℂ) * s ^ 4 + (-13 / 2 : ℂ) * s ^ 5 + (-3 / 4 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((88 : ℂ) + (184 : ℂ) * s + (120 : ℂ) * s ^ 2 + (20 : ℂ) * s ^ 3 + (-11 / 2 : ℂ) * s ^ 4 + (-3 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((66 : ℂ) + (70 : ℂ) * s + (-3 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3))))) / (r ^ 7 * (s + 3)) := by
  unfold evenCurrentVV
  rw [srcCurrentVV_eq s r hr hf hs hs3 hs1, vvLaurentA_lam s hs hs3 hs1, vvLaurentB_lam s hs hs3, evenCurrent_lauI1_lam s r hs hs3 hs1, evenCurrent_lauI3_lam s r hs hs3 hs1]
  unfold srcCurrentVV
  field_simp
  ring

/-- Slope of the linear boundary divergence of the VV flux `r²·(current)` (none for the vector–vector block). -/
def evenSlopeVV (s : ℂ) : ℂ := (0 : ℂ)
/-- The `O(1/r)` remainder of the VV flux at the AdS boundary. -/
def evenRemVV (s r : ℂ) : ℂ := (((-15 / 2 : ℂ) * s + (-103 / 4 : ℂ) * s ^ 2 + (-34 : ℂ) * s ^ 3 + (-43 / 2 : ℂ) * s ^ 4 + (-13 / 2 : ℂ) * s ^ 5 + (-3 / 4 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((88 : ℂ) + (184 : ℂ) * s + (120 : ℂ) * s ^ 2 + (20 : ℂ) * s ^ 3 + (-11 / 2 : ℂ) * s ^ 4 + (-3 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((66 : ℂ) + (70 : ℂ) * s + (-3 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3))))) / (r ^ 5 * (s + 3))

/-- Boundary structure of the VV flux at the fundamental harmonic: a pure linear divergence
and no finite part. -/
theorem evenCurrentVV_boundary (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    r ^ 2 * evenCurrentVV s r ((s + 1) * (s + 2)) (vvLaurentMasterA s ((s + 1) * (s + 2))) (vvLaurentMasterB s ((s + 1) * (s + 2))) = evenSlopeVV s * r + evenRemVV s r := by
  rw [evenCurrentVV_eq s r hr hf hs hs3 hs1]
  unfold evenSlopeVV evenRemVV
  field_simp
  ring

end
end RHTower.D4BMScalarStream
