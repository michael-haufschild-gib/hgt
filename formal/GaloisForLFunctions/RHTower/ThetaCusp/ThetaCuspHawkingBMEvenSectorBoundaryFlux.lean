import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorRadialCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarStreamLaurentMaster
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorVectorLaurentMaster

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
theorem ssSourceTR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR s r ((s + 1) * (s + 2)) = (((3 / 4 : ℂ) * s ^ (3 : ℕ) + (15 / 8 : ℂ) * s ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-1 : ℂ) * s ^ (2 : ℕ) + (-7 / 2 : ℂ) * s ^ (3 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((3 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ)))))) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) := by
  unfold ssSourceTR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTR1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR1 s r ((s + 1) * (s + 2)) = (((15 / 4 : ℂ) * s ^ (3 : ℕ) + (87 / 8 : ℂ) * s ^ (4 : ℕ) + (45 / 4 : ℂ) * s ^ (5 : ℕ) + (39 / 8 : ℂ) * s ^ (6 : ℕ) + (3 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-3 : ℂ) * s ^ (2 : ℕ) + (-71 / 4 : ℂ) * s ^ (3 : ℕ) + (-197 / 8 : ℂ) * s ^ (4 : ℕ) + (-33 / 2 : ℂ) * s ^ (5 : ℕ) + (-37 / 8 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((8 : ℂ) * s ^ (2 : ℕ) + (23 : ℂ) * s ^ (3 : ℕ) + (13 / 2 : ℂ) * s ^ (4 : ℕ) + (5 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-9 : ℂ) * s ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ)))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) := by
  unfold ssSourceTR1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTR2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR2 s r ((s + 1) * (s + 2)) = (((45 / 2 : ℂ) * s ^ (3 : ℕ) + (291 / 4 : ℂ) * s ^ (4 : ℕ) + (357 / 4 : ℂ) * s ^ (5 : ℕ) + (207 / 4 : ℂ) * s ^ (6 : ℕ) + (57 / 4 : ℂ) * s ^ (7 : ℕ) + (3 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-12 : ℂ) * s ^ (2 : ℕ) + (-229 / 2 : ℂ) * s ^ (3 : ℕ) + (-971 / 4 : ℂ) * s ^ (4 : ℕ) + (-911 / 4 : ℂ) * s ^ (5 : ℕ) + (-401 / 4 : ℂ) * s ^ (6 : ℕ) + (-67 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((40 : ℂ) * s ^ (2 : ℕ) + (204 : ℂ) * s ^ (3 : ℕ) + (256 : ℂ) * s ^ (4 : ℕ) + (155 : ℂ) * s ^ (5 : ℕ) + (47 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-48 : ℂ) * s ^ (2 : ℕ) + (-156 : ℂ) * s ^ (3 : ℕ) + (-36 : ℂ) * s ^ (4 : ℕ) + (-30 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((36 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ)))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)) := by
  unfold ssSourceTR2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceT_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT s r ((s + 1) * (s + 2)) = (((3 / 16 : ℂ) * s ^ (3 : ℕ) + (3 / 8 : ℂ) * s ^ (4 : ℕ) + (3 / 16 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((1 / 2 : ℂ) * s))))) / (r ^ (4 : ℕ)) := by
  unfold ssSourceT
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT1 s r ((s + 1) * (s + 2)) = (((3 / 4 : ℂ) * s ^ (3 : ℕ) + (15 / 8 : ℂ) * s ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((1 : ℂ) * s ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-3 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-1 / 2 : ℂ) * s ^ (3 : ℕ)))))) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) := by
  unfold ssSourceT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT2 s r ((s + 1) * (s + 2)) = (((15 / 4 : ℂ) * s ^ (3 : ℕ) + (87 / 8 : ℂ) * s ^ (4 : ℕ) + (45 / 4 : ℂ) * s ^ (5 : ℕ) + (39 / 8 : ℂ) * s ^ (6 : ℕ) + (3 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((3 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-117 / 8 : ℂ) * s ^ (4 : ℕ) + (-59 / 4 : ℂ) * s ^ (5 : ℕ) + (-33 / 8 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-5 : ℂ) * s ^ (2 : ℕ) + (-17 / 4 : ℂ) * s ^ (3 : ℕ) + (4 : ℂ) * s ^ (4 : ℕ) + (15 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((3 / 2 : ℂ) * s ^ (3 : ℕ)))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) := by
  unfold ssSourceT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTF_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF s r ((s + 1) * (s + 2)) = (((-1 / 4 : ℂ) * s + (-1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((1 : ℂ) * s))) / (r ^ (4 : ℕ) * (s + 3)) := by
  unfold ssSourceTF
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTF1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-1 : ℂ) * s + (-5 / 2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((3 : ℂ) * s + (4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-2 : ℂ) * s))))) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) * (s + 3)) := by
  unfold ssSourceTF1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTF2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF2 s r ((s + 1) * (s + 2)) = (((-5 : ℂ) * s + (-29 / 2 : ℂ) * s ^ (2 : ℕ) + (-15 : ℂ) * s ^ (3 : ℕ) + (-13 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((16 : ℂ) * s + (71 / 2 : ℂ) * s ^ (2 : ℕ) + (25 : ℂ) * s ^ (3 : ℕ) + (11 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-17 : ℂ) * s + (-24 : ℂ) * s ^ (2 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((6 : ℂ) * s))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * (s + 3)) := by
  unfold ssSourceTF2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem ssSourceTF3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF3 s r ((s + 1) * (s + 2)) = (((-30 : ℂ) * s + (-97 : ℂ) * s ^ (2 : ℕ) + (-119 : ℂ) * s ^ (3 : ℕ) + (-69 : ℂ) * s ^ (4 : ℕ) + (-19 : ℂ) * s ^ (5 : ℕ) + (-2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((114 : ℂ) * s + (319 : ℂ) * s ^ (2 : ℕ) + (321 : ℂ) * s ^ (3 : ℕ) + (137 : ℂ) * s ^ (4 : ℕ) + (21 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-162 : ℂ) * s + (-366 : ℂ) * s ^ (2 : ℕ) + (-258 : ℂ) * s ^ (3 : ℕ) + (-54 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((102 : ℂ) * s + (156 : ℂ) * s ^ (2 : ℕ) + (30 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-24 : ℂ) * s))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (s + 3)) := by
  unfold ssSourceTF3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTR s r ((s + 1) * (s + 2)) = (((1 : ℂ) * s ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((2 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ)))) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) := by
  unfold vvSourceTR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTR1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTR1 s r ((s + 1) * (s + 2)) = (((5 : ℂ) * s ^ (2 : ℕ) + (19 / 2 : ℂ) * s ^ (3 : ℕ) + (11 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-7 : ℂ) * s ^ (2 : ℕ) + (-9 / 2 : ℂ) * s ^ (3 : ℕ) + (19 / 2 : ℂ) * s ^ (4 : ℕ) + (9 : ℂ) * s ^ (5 : ℕ) + (2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-10 : ℂ) * s ^ (3 : ℕ) + (-15 : ℂ) * s ^ (4 : ℕ) + (-5 : ℂ) * s ^ (5 : ℕ)))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) := by
  unfold vvSourceTR1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTR2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTR2 s r ((s + 1) * (s + 2)) = (((30 : ℂ) * s ^ (2 : ℕ) + (67 : ℂ) * s ^ (3 : ℕ) + (52 : ℂ) * s ^ (4 : ℕ) + (17 : ℂ) * s ^ (5 : ℕ) + (2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-78 : ℂ) * s ^ (2 : ℕ) + (-127 : ℂ) * s ^ (3 : ℕ) + (-26 : ℂ) * s ^ (4 : ℕ) + (45 : ℂ) * s ^ (5 : ℕ) + (26 : ℂ) * s ^ (6 : ℕ) + (4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((56 : ℂ) * s ^ (2 : ℕ) + (16 : ℂ) * s ^ (3 : ℕ) + (-126 : ℂ) * s ^ (4 : ℕ) + (-112 : ℂ) * s ^ (5 : ℕ) + (-26 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((60 : ℂ) * s ^ (3 : ℕ) + (90 : ℂ) * s ^ (4 : ℕ) + (30 : ℂ) * s ^ (5 : ℕ)))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)) := by
  unfold vvSourceTR2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceT_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceT s r ((s + 1) * (s + 2)) = ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (9 / 4 : ℂ) * s ^ (3 : ℕ) + (3 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) := by
  unfold vvSourceT
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceT1 s r ((s + 1) * (s + 2)) = (((6 : ℂ) * s ^ (2 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ) + (15 / 2 : ℂ) * s ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-6 : ℂ) * s ^ (2 : ℕ) + (-9 : ℂ) * s ^ (3 : ℕ) + (-3 : ℂ) * s ^ (4 : ℕ)))) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) := by
  unfold vvSourceT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceT2 s r ((s + 1) * (s + 2)) = (((30 : ℂ) * s ^ (2 : ℕ) + (72 : ℂ) * s ^ (3 : ℕ) + (123 / 2 : ℂ) * s ^ (4 : ℕ) + (45 / 2 : ℂ) * s ^ (5 : ℕ) + (3 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-60 : ℂ) * s ^ (2 : ℕ) + (-123 : ℂ) * s ^ (3 : ℕ) + (-159 / 2 : ℂ) * s ^ (4 : ℕ) + (-33 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((30 : ℂ) * s ^ (2 : ℕ) + (45 : ℂ) * s ^ (3 : ℕ) + (15 : ℂ) * s ^ (4 : ℕ)))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) := by
  unfold vvSourceT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTF_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTF s r ((s + 1) * (s + 2)) = ((11 : ℂ) * s + (57 / 2 : ℂ) * s ^ (2 : ℕ) + (53 / 2 : ℂ) * s ^ (3 : ℕ) + (21 / 2 : ℂ) * s ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ) * (s + 3)) := by
  unfold vvSourceTF
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTF1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTF1 s r ((s + 1) * (s + 2)) = (((44 : ℂ) * s + (136 : ℂ) * s ^ (2 : ℕ) + (163 : ℂ) * s ^ (3 : ℕ) + (95 : ℂ) * s ^ (4 : ℕ) + (27 : ℂ) * s ^ (5 : ℕ) + (3 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-44 : ℂ) * s + (-114 : ℂ) * s ^ (2 : ℕ) + (-106 : ℂ) * s ^ (3 : ℕ) + (-42 : ℂ) * s ^ (4 : ℕ) + (-6 : ℂ) * s ^ (5 : ℕ)))) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) * (s + 3)) := by
  unfold vvSourceTF1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTF2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTF2 s r ((s + 1) * (s + 2)) = (((220 : ℂ) * s + (768 : ℂ) * s ^ (2 : ℕ) + (1087 : ℂ) * s ^ (3 : ℕ) + (801 : ℂ) * s ^ (4 : ℕ) + (325 : ℂ) * s ^ (5 : ℕ) + (69 : ℂ) * s ^ (6 : ℕ) + (6 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-440 : ℂ) * s + (-1382 : ℂ) * s ^ (2 : ℕ) + (-1687 : ℂ) * s ^ (3 : ℕ) + (-1003 : ℂ) * s ^ (4 : ℕ) + (-291 : ℂ) * s ^ (5 : ℕ) + (-33 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((220 : ℂ) * s + (570 : ℂ) * s ^ (2 : ℕ) + (530 : ℂ) * s ^ (3 : ℕ) + (210 : ℂ) * s ^ (4 : ℕ) + (30 : ℂ) * s ^ (5 : ℕ)))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * (s + 3)) := by
  unfold vvSourceTF2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem vvSourceTF3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvSourceTF3 s r ((s + 1) * (s + 2)) = (((1320 : ℂ) * s + (5048 : ℂ) * s ^ (2 : ℕ) + (8058 : ℂ) * s ^ (3 : ℕ) + (6980 : ℂ) * s ^ (4 : ℕ) + (3552 : ℂ) * s ^ (5 : ℕ) + (1064 : ℂ) * s ^ (6 : ℕ) + (174 : ℂ) * s ^ (7 : ℕ) + (12 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-3960 : ℂ) * s + (-14088 : ℂ) * s ^ (2 : ℕ) + (-20382 : ℂ) * s ^ (3 : ℕ) + (-15396 : ℂ) * s ^ (4 : ℕ) + (-6420 : ℂ) * s ^ (5 : ℕ) + (-1404 : ℂ) * s ^ (6 : ℕ) + (-126 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((3960 : ℂ) * s + (12636 : ℂ) * s ^ (2 : ℕ) + (15696 : ℂ) * s ^ (3 : ℕ) + (9504 : ℂ) * s ^ (4 : ℕ) + (2808 : ℂ) * s ^ (5 : ℕ) + (324 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-1320 : ℂ) * s + (-3420 : ℂ) * s ^ (2 : ℕ) + (-3180 : ℂ) * s ^ (3 : ℕ) + (-1260 : ℂ) * s ^ (4 : ℕ) + (-180 : ℂ) * s ^ (5 : ℕ)))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (s + 3)) := by
  unfold vvSourceTF3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qtr0 s r ((s + 1) * (s + 2)) = (((-3 : ℂ) * s + (-5 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((3 : ℂ) + (35 / 2 : ℂ) * s + (-19 / 2 : ℂ) * s ^ (2 : ℕ) + (-17 : ℂ) * s ^ (3 : ℕ) + (-4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-20 : ℂ) + (74 : ℂ) * s + (77 / 2 : ℂ) * s ^ (2 : ℕ) + (23 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-43 : ℂ) + (-69 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold srcCoeff_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qtr1 s r ((s + 1) * (s + 2)) = (((-6 : ℂ) + (-2 : ℂ) * s + (3 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((1 : ℂ) + (29 / 2 : ℂ) * s + (6 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-23 : ℂ) + (-43 / 2 : ℂ) * s + (-7 / 2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))))) / (r * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold srcCoeff_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qtr2 s r ((s + 1) * (s + 2)) = (((-3 : ℂ) + (-5 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((5 : ℂ) + (5 : ℂ) * s + (1 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((-1 : ℂ) + (-5 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-1 : ℂ)))))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold srcCoeff_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qt0 s r ((s + 1) * (s + 2)) = (((9 : ℂ) * s + (39 / 2 : ℂ) * s ^ (2 : ℕ) + (29 / 2 : ℂ) * s ^ (3 : ℕ) + (9 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-7 : ℂ) * s + (-83 / 2 : ℂ) * s ^ (2 : ℕ) + (-63 / 2 : ℂ) * s ^ (3 : ℕ) + (-9 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-64 : ℂ) + (40 : ℂ) * s + (9 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-56 : ℂ) + (-42 : ℂ) * s + (2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))))) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold srcCoeff_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qt1 s r ((s + 1) * (s + 2)) = (((15 : ℂ) * s + (31 / 2 : ℂ) * s ^ (2 : ℕ) + (5 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-18 : ℂ) + (3 : ℂ) * s + (-3 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-42 : ℂ) + (-36 : ℂ) * s + (-6 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (r ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold srcCoeff_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qt2 s r ((s + 1) * (s + 2)) = (((-6 : ℂ) + (-5 : ℂ) * s + (-1 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((10 : ℂ) + (10 : ℂ) * s + (2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((-2 : ℂ) + (-5 : ℂ) * s + (-1 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-2 : ℂ)))))))) / (r * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold srcCoeff_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qT0 s r ((s + 1) * (s + 2)) = (((27 : ℂ) * s + (117 / 2 : ℂ) * s ^ (2 : ℕ) + (87 / 2 : ℂ) * s ^ (3 : ℕ) + (27 / 2 : ℂ) * s ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-91 : ℂ) * s + (-152 : ℂ) * s ^ (2 : ℕ) + (-80 : ℂ) * s ^ (3 : ℕ) + (-10 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-52 : ℂ) + (215 : ℂ) * s + (257 / 2 : ℂ) * s ^ (2 : ℕ) + (75 / 2 : ℂ) * s ^ (3 : ℕ) + (-5 / 2 : ℂ) * s ^ (4 : ℕ) + (-5 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((8 : ℂ) + (-49 : ℂ) * s + (3 : ℂ) * s ^ (2 : ℕ) + (-17 : ℂ) * s ^ (3 : ℕ) + (-5 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((44 : ℂ) + (42 : ℂ) * s + (-2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))))))) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold srcCoeff_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qT1 s r ((s + 1) * (s + 2)) = (((45 : ℂ) * s + (93 / 2 : ℂ) * s ^ (2 : ℕ) + (15 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-66 : ℂ) + (-121 : ℂ) * s + (-66 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-10 : ℂ) + (-164 : ℂ) * s + (-69 / 2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((112 : ℂ) + (114 : ℂ) * s + (10 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((36 : ℂ)))))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold srcCoeff_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qT2 s r ((s + 1) * (s + 2)) = (((24 : ℂ) + (14 : ℂ) * s + (-1 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-16 : ℂ) + (-44 : ℂ) * s + (-15 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((46 : ℂ) + (48 : ℂ) * s + (8 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((18 : ℂ)))))))) / (r * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold srcCoeff_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem srcCoeff_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : srcCoeff_qT3 s r ((s + 1) * (s + 2)) = (((6 : ℂ) + (5 : ℂ) * s + (1 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((-10 : ℂ) + (-10 : ℂ) * s + (-2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((2 : ℂ) + (5 : ℂ) * s + (1 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))) / (s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold srcCoeff_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem evenCurrent_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : evenCurrent_lauR s r ((s + 1) * (s + 2)) = (((-33 / 2 : ℂ) * s + (-211 / 4 : ℂ) * s ^ (2 : ℕ) + (-15 / 4 : ℂ) * s ^ (3 : ℕ) + (79 / 4 : ℂ) * s ^ (4 : ℕ) + (21 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((6 : ℂ) + (167 / 2 : ℂ) * s + (-1 / 4 : ℂ) * s ^ (2 : ℕ) + (-31 / 4 : ℂ) * s ^ (3 : ℕ) + (-55 / 4 : ℂ) * s ^ (4 : ℕ) + (-15 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((32 : ℂ) + (14 : ℂ) * s + (29 / 2 : ℂ) * s ^ (2 : ℕ) + (-14 : ℂ) * s ^ (3 : ℕ) + (-5 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((28 : ℂ) + (27 : ℂ) * s + (-1 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((6 : ℂ)))))))))) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold evenCurrent_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem evenCurrent_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : evenCurrent_lauI1 s r ((s + 1) * (s + 2)) = (((45 / 2 : ℂ) + (291 / 4 : ℂ) * s + (321 / 4 : ℂ) * s ^ (2 : ℕ) + (141 / 4 : ℂ) * s ^ (3 : ℕ) + (21 / 4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-159 / 2 : ℂ) + (-561 / 4 : ℂ) * s + (-339 / 4 : ℂ) * s ^ (2 : ℕ) + (-111 / 4 : ℂ) * s ^ (3 : ℕ) + (-15 / 4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-3 : ℂ) * s + (-3 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((3 : ℂ) + (3 : ℂ) * s))))))) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) * s * (s + 3) ^ (2 : ℕ)) := by
  unfold evenCurrent_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem evenCurrent_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : evenCurrent_lauI3 s r ((s + 1) * (s + 2)) = (((120 : ℂ) + (659 / 2 : ℂ) * s + (1433 / 4 : ℂ) * s ^ (2 : ℕ) + (769 / 4 : ℂ) * s ^ (3 : ℕ) + (203 / 4 : ℂ) * s ^ (4 : ℕ) + (21 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-422 : ℂ) + (-1581 / 2 : ℂ) * s + (-2289 / 4 : ℂ) * s ^ (2 : ℕ) + (-839 / 4 : ℂ) * s ^ (3 : ℕ) + (-167 / 4 : ℂ) * s ^ (4 : ℕ) + (-15 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((152 : ℂ) + (206 : ℂ) * s + (231 / 2 : ℂ) * s ^ (2 : ℕ) + (28 : ℂ) * s ^ (3 : ℕ) + (5 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((84 : ℂ) + (39 : ℂ) * s + (3 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-6 : ℂ)))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold evenCurrent_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

/-! ## The SS source current at the fundamental harmonic -/
theorem srcPieceSS_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-27 / 4 : ℂ) * s ^ (3 : ℕ) + (-99 / 4 : ℂ) * s ^ (4 : ℕ) + (-579 / 16 : ℂ) * s ^ (5 : ℕ) + (-27 : ℂ) * s ^ (6 : ℕ) + (-87 / 8 : ℂ) * s ^ (7 : ℕ) + (-9 / 4 : ℂ) * s ^ (8 : ℕ) + (-3 / 16 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((63 / 4 : ℂ) * s ^ (2 : ℕ) + (201 / 2 : ℂ) * s ^ (3 : ℕ) + (2617 / 16 : ℂ) * s ^ (4 : ℕ) + (479 / 8 : ℂ) * s ^ (5 : ℕ) + (-901 / 8 : ℂ) * s ^ (6 : ℕ) + (-295 / 2 : ℂ) * s ^ (7 : ℕ) + (-1171 / 16 : ℂ) * s ^ (8 : ℕ) + (-135 / 8 : ℂ) * s ^ (9 : ℕ) + (-3 / 2 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-9 : ℂ) * s + (-159 : ℂ) * s ^ (2 : ℕ) + (-739 / 4 : ℂ) * s ^ (3 : ℕ) + (3447 / 8 : ℂ) * s ^ (4 : ℕ) + (14285 / 16 : ℂ) * s ^ (5 : ℕ) + (1435 / 2 : ℂ) * s ^ (6 : ℕ) + (2663 / 8 : ℂ) * s ^ (7 : ℕ) + (739 / 8 : ℂ) * s ^ (8 : ℕ) + (217 / 16 : ℂ) * s ^ (9 : ℕ) + (3 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((87 : ℂ) * s + (293 / 4 : ℂ) * s ^ (2 : ℕ) + (-1219 : ℂ) * s ^ (3 : ℕ) + (-26407 / 16 : ℂ) * s ^ (4 : ℕ) + (-1152 : ℂ) * s ^ (5 : ℕ) + (-3757 / 8 : ℂ) * s ^ (6 : ℕ) + (-237 / 2 : ℂ) * s ^ (7 : ℕ) + (-331 / 16 : ℂ) * s ^ (8 : ℕ) + (-2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-51 : ℂ) * s + (1207 : ℂ) * s ^ (2 : ℕ) + (4533 / 4 : ℂ) * s ^ (3 : ℕ) + (523 : ℂ) * s ^ (4 : ℕ) + (747 / 4 : ℂ) * s ^ (5 : ℕ) + (59 / 2 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-351 : ℂ) * s + (-237 : ℂ) * s ^ (2 : ℕ) + (245 / 4 : ℂ) * s ^ (3 : ℕ) + (141 / 2 : ℂ) * s ^ (4 : ℕ) + (49 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s + (-18 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((-135 / 2 : ℂ) * s ^ (2 : ℕ) + (-963 / 4 : ℂ) * s ^ (3 : ℕ) + (-2589 / 8 : ℂ) * s ^ (4 : ℕ) + (-2949 / 16 : ℂ) * s ^ (5 : ℕ) + (-75 / 8 : ℂ) * s ^ (6 : ℕ) + (339 / 8 : ℂ) * s ^ (7 : ℕ) + (177 / 8 : ℂ) * s ^ (8 : ℕ) + (75 / 16 : ℂ) * s ^ (9 : ℕ) + (3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((54 : ℂ) * s + (1467 / 4 : ℂ) * s ^ (2 : ℕ) + (3393 / 4 : ℂ) * s ^ (3 : ℕ) + (18859 / 16 : ℂ) * s ^ (4 : ℕ) + (4247 / 4 : ℂ) * s ^ (5 : ℕ) + (2399 / 4 : ℂ) * s ^ (6 : ℕ) + (833 / 4 : ℂ) * s ^ (7 : ℕ) + (711 / 16 : ℂ) * s ^ (8 : ℕ) + (23 / 4 : ℂ) * s ^ (9 : ℕ) + (3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-153 : ℂ) * s + (-1911 / 2 : ℂ) * s ^ (2 : ℕ) + (-9651 / 4 : ℂ) * s ^ (3 : ℕ) + (-3679 : ℂ) * s ^ (4 : ℕ) + (-53371 / 16 : ℂ) * s ^ (5 : ℕ) + (-3537 / 2 : ℂ) * s ^ (6 : ℕ) + (-4233 / 8 : ℂ) * s ^ (7 : ℕ) + (-163 / 2 : ℂ) * s ^ (8 : ℕ) + (-79 / 16 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((393 : ℂ) * s + (7613 / 4 : ℂ) * s ^ (2 : ℕ) + (17279 / 4 : ℂ) * s ^ (3 : ℕ) + (73651 / 16 : ℂ) * s ^ (4 : ℕ) + (12065 / 4 : ℂ) * s ^ (5 : ℕ) + (9483 / 8 : ℂ) * s ^ (6 : ℕ) + (481 / 2 : ℂ) * s ^ (7 : ℕ) + (299 / 16 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-507 : ℂ) * s + (-2233 : ℂ) * s ^ (2 : ℕ) + (-8839 / 4 : ℂ) * s ^ (3 : ℕ) + (-2207 / 2 : ℂ) * s ^ (4 : ℕ) + (-1905 / 4 : ℂ) * s ^ (5 : ℕ) + (-145 : ℂ) * s ^ (6 : ℕ) + (-35 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((429 : ℂ) * s + (68 : ℂ) * s ^ (2 : ℕ) + (-733 / 4 : ℂ) * s ^ (3 : ℕ) + (-377 / 2 : ℂ) * s ^ (4 : ℕ) + (-181 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((216 : ℂ) * s + (36 : ℂ) * s ^ (2 : ℕ) + (-12 : ℂ) * s ^ (3 : ℕ)))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((405 / 2 : ℂ) * s ^ (2 : ℕ) + (891 : ℂ) * s ^ (3 : ℕ) + (13257 / 8 : ℂ) * s ^ (4 : ℕ) + (13641 / 8 : ℂ) * s ^ (5 : ℕ) + (1065 : ℂ) * s ^ (6 : ℕ) + (1659 / 4 : ℂ) * s ^ (7 : ℕ) + (789 / 8 : ℂ) * s ^ (8 : ℕ) + (105 / 8 : ℂ) * s ^ (9 : ℕ) + (3 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-108 : ℂ) * s + (-2583 / 2 : ℂ) * s ^ (2 : ℕ) + (-16341 / 4 : ℂ) * s ^ (3 : ℕ) + (-25517 / 4 : ℂ) * s ^ (4 : ℕ) + (-11565 / 2 : ℂ) * s ^ (5 : ℕ) + (-12825 / 4 : ℂ) * s ^ (6 : ℕ) + (-4347 / 4 : ℂ) * s ^ (7 : ℕ) + (-857 / 4 : ℂ) * s ^ (8 : ℕ) + (-43 / 2 : ℂ) * s ^ (9 : ℕ) + (-3 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((432 : ℂ) * s + (5979 / 2 : ℂ) * s ^ (2 : ℕ) + (13915 / 2 : ℂ) * s ^ (3 : ℕ) + (69721 / 8 : ℂ) * s ^ (4 : ℕ) + (53803 / 8 : ℂ) * s ^ (5 : ℕ) + (12929 / 4 : ℂ) * s ^ (6 : ℕ) + (3683 / 4 : ℂ) * s ^ (7 : ℕ) + (1113 / 8 : ℂ) * s ^ (8 : ℕ) + (67 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-636 : ℂ) * s + (-6313 / 2 : ℂ) * s ^ (2 : ℕ) + (-19781 / 4 : ℂ) * s ^ (3 : ℕ) + (-4568 : ℂ) * s ^ (4 : ℕ) + (-2889 : ℂ) * s ^ (5 : ℕ) + (-1182 : ℂ) * s ^ (6 : ℕ) + (-1055 / 4 : ℂ) * s ^ (7 : ℕ) + (-47 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((492 : ℂ) * s + (1064 : ℂ) * s ^ (2 : ℕ) + (999 : ℂ) * s ^ (3 : ℕ) + (443 : ℂ) * s ^ (4 : ℕ) + (208 : ℂ) * s ^ (5 : ℕ) + (91 : ℂ) * s ^ (6 : ℕ) + (15 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-72 : ℂ) * s + (210 : ℂ) * s ^ (2 : ℕ) + (177 : ℂ) * s ^ (3 : ℕ) + (132 : ℂ) * s ^ (4 : ℕ) + (33 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s + (-18 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt0 s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((-81 / 16 : ℂ) * s ^ (3 : ℕ) + (-729 / 32 : ℂ) * s ^ (4 : ℕ) + (-675 / 16 : ℂ) * s ^ (5 : ℕ) + (-1329 / 32 : ℂ) * s ^ (6 : ℕ) + (-375 / 16 : ℂ) * s ^ (7 : ℕ) + (-243 / 32 : ℂ) * s ^ (8 : ℕ) + (-21 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 32 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-27 / 4 : ℂ) * s ^ (2 : ℕ) + (-63 / 4 : ℂ) * s ^ (3 : ℕ) + (291 / 16 : ℂ) * s ^ (4 : ℕ) + (1495 / 16 : ℂ) * s ^ (5 : ℕ) + (925 / 8 : ℂ) * s ^ (6 : ℕ) + (517 / 8 : ℂ) * s ^ (7 : ℕ) + (271 / 16 : ℂ) * s ^ (8 : ℕ) + (27 / 16 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((9 / 2 : ℂ) * s + (69 / 2 : ℂ) * s ^ (2 : ℕ) + (1997 / 16 : ℂ) * s ^ (3 : ℕ) + (3005 / 32 : ℂ) * s ^ (4 : ℕ) + (-633 / 16 : ℂ) * s ^ (5 : ℕ) + (-2871 / 32 : ℂ) * s ^ (6 : ℕ) + (-861 / 16 : ℂ) * s ^ (7 : ℕ) + (-441 / 32 : ℂ) * s ^ (8 : ℕ) + (-15 / 16 : ℂ) * s ^ (9 : ℕ) + (3 / 32 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((18 : ℂ) + (108 : ℂ) * s + (179 / 2 : ℂ) * s ^ (2 : ℕ) + (109 / 8 : ℂ) * s ^ (3 : ℕ) + (103 / 16 : ℂ) * s ^ (4 : ℕ) + (325 / 16 : ℂ) * s ^ (5 : ℕ) + (125 / 8 : ℂ) * s ^ (6 : ℕ) + (23 / 2 : ℂ) * s ^ (7 : ℕ) + (71 / 16 : ℂ) * s ^ (8 : ℕ) + (9 / 16 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((78 : ℂ) + (-113 / 2 : ℂ) * s + (-11 : ℂ) * s ^ (2 : ℕ) + (-439 / 8 : ℂ) * s ^ (3 : ℕ) + (-85 : ℂ) * s ^ (4 : ℕ) + (-127 / 4 : ℂ) * s ^ (5 : ℕ) + (9 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (53 : ℂ) * s + (-293 / 4 : ℂ) * s ^ (2 : ℕ) + (-243 / 4 : ℂ) * s ^ (3 : ℕ) + (-43 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-66 : ℂ) + (-103 : ℂ) * s + (-33 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-18 : ℂ) + (-6 : ℂ) * s))))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qt0_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-135 / 4 : ℂ) * s ^ (3 : ℕ) + (-261 / 2 : ℂ) * s ^ (4 : ℕ) + (-3291 / 16 : ℂ) * s ^ (5 : ℕ) + (-2739 / 16 : ℂ) * s ^ (6 : ℕ) + (-651 / 8 : ℂ) * s ^ (7 : ℕ) + (-177 / 8 : ℂ) * s ^ (8 : ℕ) + (-51 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 16 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-9 / 2 : ℂ) * s ^ (2 : ℕ) + (93 / 2 : ℂ) * s ^ (3 : ℕ) + (1583 / 8 : ℂ) * s ^ (4 : ℕ) + (316 : ℂ) * s ^ (5 : ℕ) + (2169 / 8 : ℂ) * s ^ (6 : ℕ) + (271 / 2 : ℂ) * s ^ (7 : ℕ) + (313 / 8 : ℂ) * s ^ (8 : ℕ) + (6 : ℂ) * s ^ (9 : ℕ) + (3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((54 : ℂ) * s + (297 / 2 : ℂ) * s ^ (2 : ℕ) + (1251 / 4 : ℂ) * s ^ (3 : ℕ) + (1745 / 4 : ℂ) * s ^ (4 : ℕ) + (4593 / 16 : ℂ) * s ^ (5 : ℕ) + (705 / 16 : ℂ) * s ^ (6 : ℕ) + (-293 / 8 : ℂ) * s ^ (7 : ℕ) + (-149 / 8 : ℂ) * s ^ (8 : ℕ) + (-51 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 16 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((72 : ℂ) * s + (201 / 2 : ℂ) * s ^ (2 : ℕ) + (-213 : ℂ) * s ^ (3 : ℕ) + (-5007 / 8 : ℂ) * s ^ (4 : ℕ) + (-4265 / 8 : ℂ) * s ^ (5 : ℕ) + (-753 / 4 : ℂ) * s ^ (6 : ℕ) + (-89 / 4 : ℂ) * s ^ (7 : ℕ) + (13 / 8 : ℂ) * s ^ (8 : ℕ) + (3 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-90 : ℂ) * s + (-537 / 2 : ℂ) * s ^ (2 : ℕ) + (-429 / 2 : ℂ) * s ^ (3 : ℕ) + (225 / 4 : ℂ) * s ^ (4 : ℕ) + (495 / 4 : ℂ) * s ^ (5 : ℕ) + (177 / 4 : ℂ) * s ^ (6 : ℕ) + (19 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-36 : ℂ) * s + (6 : ℂ) * s ^ (2 : ℕ) + (96 : ℂ) * s ^ (3 : ℕ) + (66 : ℂ) * s ^ (4 : ℕ) + (12 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((18 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qt1_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((-135 / 2 : ℂ) * s ^ (2 : ℕ) + (-549 / 2 : ℂ) * s ^ (3 : ℕ) + (-3687 / 8 : ℂ) * s ^ (4 : ℕ) + (-1659 / 4 : ℂ) * s ^ (5 : ℕ) + (-867 / 4 : ℂ) * s ^ (6 : ℕ) + (-66 : ℂ) * s ^ (7 : ℕ) + (-87 / 8 : ℂ) * s ^ (8 : ℕ) + (-3 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-54 : ℂ) * s + (135 / 2 : ℂ) * s ^ (2 : ℕ) + (1473 / 2 : ℂ) * s ^ (3 : ℕ) + (11281 / 8 : ℂ) * s ^ (4 : ℕ) + (5119 / 4 : ℂ) * s ^ (5 : ℕ) + (1277 / 2 : ℂ) * s ^ (6 : ℕ) + (713 / 4 : ℂ) * s ^ (7 : ℕ) + (207 / 8 : ℂ) * s ^ (8 : ℕ) + (3 / 2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((180 : ℂ) * s + (249 : ℂ) * s ^ (2 : ℕ) + (-1005 / 2 : ℂ) * s ^ (3 : ℕ) + (-11459 / 8 : ℂ) * s ^ (4 : ℕ) + (-2735 / 2 : ℂ) * s ^ (5 : ℕ) + (-1305 / 2 : ℂ) * s ^ (6 : ℕ) + (-649 / 4 : ℂ) * s ^ (7 : ℕ) + (-153 / 8 : ℂ) * s ^ (8 : ℕ) + (-3 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-168 : ℂ) * s + (-422 : ℂ) * s ^ (2 : ℕ) + (-307 / 2 : ℂ) * s ^ (3 : ℕ) + (3483 / 8 : ℂ) * s ^ (4 : ℕ) + (2183 / 4 : ℂ) * s ^ (5 : ℕ) + (513 / 2 : ℂ) * s ^ (6 : ℕ) + (215 / 4 : ℂ) * s ^ (7 : ℕ) + (33 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((12 : ℂ) * s + (311 / 2 : ℂ) * s ^ (2 : ℕ) + (238 : ℂ) * s ^ (3 : ℕ) + (361 / 4 : ℂ) * s ^ (4 : ℕ) + (-137 / 4 : ℂ) * s ^ (5 : ℕ) + (-103 / 4 : ℂ) * s ^ (6 : ℕ) + (-15 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((30 : ℂ) * s + (53 / 2 : ℂ) * s ^ (2 : ℕ) + (-41 : ℂ) * s ^ (3 : ℕ) + (-85 / 2 : ℂ) * s ^ (4 : ℕ) + (-9 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-9 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ)))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qt2_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((-27 / 4 : ℂ) * s ^ (2 : ℕ) + (-225 / 8 : ℂ) * s ^ (3 : ℕ) + (-375 / 8 : ℂ) * s ^ (4 : ℕ) + (-159 / 4 : ℂ) * s ^ (5 : ℕ) + (-18 : ℂ) * s ^ (6 : ℕ) + (-33 / 8 : ℂ) * s ^ (7 : ℕ) + (-3 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((3 : ℂ) * s + (223 / 4 : ℂ) * s ^ (2 : ℕ) + (145 : ℂ) * s ^ (3 : ℕ) + (649 / 4 : ℂ) * s ^ (4 : ℕ) + (94 : ℂ) * s ^ (5 : ℕ) + (105 / 4 : ℂ) * s ^ (6 : ℕ) + (2 : ℂ) * s ^ (7 : ℕ) + (-1 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((1 : ℂ) * s + (-475 / 4 : ℂ) * s ^ (2 : ℕ) + (-2229 / 8 : ℂ) * s ^ (3 : ℕ) + (-1659 / 8 : ℂ) * s ^ (4 : ℕ) + (-241 / 4 : ℂ) * s ^ (5 : ℕ) + (-13 / 2 : ℂ) * s ^ (6 : ℕ) + (15 / 8 : ℂ) * s ^ (7 : ℕ) + (5 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-54 : ℂ) * s + (893 / 4 : ℂ) * s ^ (2 : ℕ) + (601 / 4 : ℂ) * s ^ (3 : ℕ) + (105 / 2 : ℂ) * s ^ (4 : ℕ) + (13 / 2 : ℂ) * s ^ (5 : ℕ) + (17 / 4 : ℂ) * s ^ (6 : ℕ) + (5 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-3 : ℂ) * s + (-163 / 2 : ℂ) * s ^ (2 : ℕ) + (-57 / 2 : ℂ) * s ^ (3 : ℕ) + (-53 / 2 : ℂ) * s ^ (4 : ℕ) + (-9 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((41 : ℂ) * s + (36 : ℂ) * s ^ (2 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((12 : ℂ) * s))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qT0_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-45 : ℂ) * s ^ (2 : ℕ) + (-159 : ℂ) * s ^ (3 : ℕ) + (-885 / 4 : ℂ) * s ^ (4 : ℕ) + (-309 / 2 : ℂ) * s ^ (5 : ℕ) + (-57 : ℂ) * s ^ (6 : ℕ) + (-21 / 2 : ℂ) * s ^ (7 : ℕ) + (-3 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((66 : ℂ) * s + (421 : ℂ) * s ^ (2 : ℕ) + (820 : ℂ) * s ^ (3 : ℕ) + (715 : ℂ) * s ^ (4 : ℕ) + (297 : ℂ) * s ^ (5 : ℕ) + (42 : ℂ) * s ^ (6 : ℕ) + (-7 : ℂ) * s ^ (7 : ℕ) + (-2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-188 : ℂ) * s + (-528 : ℂ) * s ^ (2 : ℕ) + (-753 / 2 : ℂ) * s ^ (3 : ℕ) + (37 / 4 : ℂ) * s ^ (4 : ℕ) + (209 / 2 : ℂ) * s ^ (5 : ℕ) + (42 : ℂ) * s ^ (6 : ℕ) + (8 : ℂ) * s ^ (7 : ℕ) + (3 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-10 : ℂ) * s + (-684 : ℂ) * s ^ (2 : ℕ) + (-2313 / 2 : ℂ) * s ^ (3 : ℕ) + (-619 : ℂ) * s ^ (4 : ℕ) + (-132 : ℂ) * s ^ (5 : ℕ) + (-13 : ℂ) * s ^ (6 : ℕ) + (-3 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((320 : ℂ) * s + (1028 : ℂ) * s ^ (2 : ℕ) + (595 : ℂ) * s ^ (3 : ℕ) + (140 : ℂ) * s ^ (4 : ℕ) + (13 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-116 : ℂ) * s + (-84 : ℂ) * s ^ (2 : ℕ) + (16 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ) * s))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((-120 : ℂ) * s + (-418 : ℂ) * s ^ (2 : ℕ) + (-558 : ℂ) * s ^ (3 : ℕ) + (-693 / 2 : ℂ) * s ^ (4 : ℕ) + (-171 / 2 : ℂ) * s ^ (5 : ℕ) + (15 / 2 : ℂ) * s ^ (6 : ℕ) + (15 / 2 : ℂ) * s ^ (7 : ℕ) + (1 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((464 : ℂ) * s + (1528 : ℂ) * s ^ (2 : ℕ) + (2034 : ℂ) * s ^ (3 : ℕ) + (1417 : ℂ) * s ^ (4 : ℕ) + (558 : ℂ) * s ^ (5 : ℕ) + (126 : ℂ) * s ^ (6 : ℕ) + (16 : ℂ) * s ^ (7 : ℕ) + (1 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-894 : ℂ) * s + (-2993 : ℂ) * s ^ (2 : ℕ) + (-4067 : ℂ) * s ^ (3 : ℕ) + (-5801 / 2 : ℂ) * s ^ (4 : ℕ) + (-2203 / 2 : ℂ) * s ^ (5 : ℕ) + (-405 / 2 : ℂ) * s ^ (6 : ℕ) + (-27 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((1062 : ℂ) * s + (3356 : ℂ) * s ^ (2 : ℕ) + (4097 : ℂ) * s ^ (3 : ℕ) + (2211 : ℂ) * s ^ (4 : ℕ) + (545 : ℂ) * s ^ (5 : ℕ) + (49 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-590 : ℂ) * s + (-1545 : ℂ) * s ^ (2 : ℕ) + (-1158 : ℂ) * s ^ (3 : ℕ) + (-339 : ℂ) * s ^ (4 : ℕ) + (-40 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-30 : ℂ) * s + (-144 : ℂ) * s ^ (2 : ℕ) + (-42 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((108 : ℂ) * s))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceSS_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((180 : ℂ) * s + (732 : ℂ) * s ^ (2 : ℕ) + (1229 : ℂ) * s ^ (3 : ℕ) + (1106 : ℂ) * s ^ (4 : ℕ) + (578 : ℂ) * s ^ (5 : ℕ) + (176 : ℂ) * s ^ (6 : ℕ) + (29 : ℂ) * s ^ (7 : ℕ) + (2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-804 : ℂ) * s + (-3022 : ℂ) * s ^ (2 : ℕ) + (-4626 : ℂ) * s ^ (3 : ℕ) + (-3714 : ℂ) * s ^ (4 : ℕ) + (-1672 : ℂ) * s ^ (5 : ℕ) + (-414 : ℂ) * s ^ (6 : ℕ) + (-50 : ℂ) * s ^ (7 : ℕ) + (-2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((1368 : ℂ) * s + (4658 : ℂ) * s ^ (2 : ℕ) + (6295 : ℂ) * s ^ (3 : ℕ) + (4314 : ℂ) * s ^ (4 : ℕ) + (1580 : ℂ) * s ^ (5 : ℕ) + (292 : ℂ) * s ^ (6 : ℕ) + (21 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-1032 : ℂ) * s + (-3082 : ℂ) * s ^ (2 : ℕ) + (-3444 : ℂ) * s ^ (3 : ℕ) + (-1904 : ℂ) * s ^ (4 : ℕ) + (-516 : ℂ) * s ^ (5 : ℕ) + (-54 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((228 : ℂ) * s + (522 : ℂ) * s ^ (2 : ℕ) + (510 : ℂ) * s ^ (3 : ℕ) + (198 : ℂ) * s ^ (4 : ℕ) + (30 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((108 : ℂ) * s + (192 : ℂ) * s ^ (2 : ℕ) + (36 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-48 : ℂ) * s))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  ring

/-- The source-only radial current of the SS harmonic sources at the fundamental harmonic. -/
def srcCurrentSS (s r : ℂ) : ℂ := (((60 : ℂ) * s + (1319 / 4 : ℂ) * s ^ (2 : ℕ) + (13025 / 16 : ℂ) * s ^ (3 : ℕ) + (37951 / 32 : ℂ) * s ^ (4 : ℕ) + (4481 / 4 : ℂ) * s ^ (5 : ℕ) + (22645 / 32 : ℂ) * s ^ (6 : ℕ) + (4757 / 16 : ℂ) * s ^ (7 : ℕ) + (2553 / 32 : ℂ) * s ^ (8 : ℕ) + (99 / 8 : ℂ) * s ^ (9 : ℕ) + (27 / 32 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-379 : ℂ) * s + (-1870 : ℂ) * s ^ (2 : ℕ) + (-15985 / 4 : ℂ) * s ^ (3 : ℕ) + (-77289 / 16 : ℂ) * s ^ (4 : ℕ) + (-59115 / 16 : ℂ) * s ^ (5 : ℕ) + (-15309 / 8 : ℂ) * s ^ (6 : ℕ) + (-5493 / 8 : ℂ) * s ^ (7 : ℕ) + (-2629 / 16 : ℂ) * s ^ (8 : ℕ) + (-375 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 2 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((1591 / 2 : ℂ) * s + (13301 / 4 : ℂ) * s ^ (2 : ℕ) + (93887 / 16 : ℂ) * s ^ (3 : ℕ) + (184965 / 32 : ℂ) * s ^ (4 : ℕ) + (14741 / 4 : ℂ) * s ^ (5 : ℕ) + (51459 / 32 : ℂ) * s ^ (6 : ℕ) + (7827 / 16 : ℂ) * s ^ (7 : ℕ) + (3195 / 32 : ℂ) * s ^ (8 : ℕ) + (97 / 8 : ℂ) * s ^ (9 : ℕ) + (21 / 32 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((18 : ℂ) + (-178 : ℂ) * s + (-6395 / 4 : ℂ) * s ^ (2 : ℕ) + (-20405 / 8 : ℂ) * s ^ (3 : ℕ) + (-32941 / 16 : ℂ) * s ^ (4 : ℕ) + (-17413 / 16 : ℂ) * s ^ (5 : ℕ) + (-3169 / 8 : ℂ) * s ^ (6 : ℕ) + (-99 : ℂ) * s ^ (7 : ℕ) + (-245 / 16 : ℂ) * s ^ (8 : ℕ) + (-17 / 16 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((78 : ℂ) + (-491 / 2 : ℂ) * s + (-325 / 2 : ℂ) * s ^ (2 : ℕ) + (-1523 / 8 : ℂ) * s ^ (3 : ℕ) + (-207 / 2 : ℂ) * s ^ (4 : ℕ) + (-101 / 4 : ℂ) * s ^ (5 : ℕ) + (-6 : ℂ) * s ^ (6 : ℕ) + (-7 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (56 : ℂ) * s + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (217 / 4 : ℂ) * s ^ (3 : ℕ) + (107 / 4 : ℂ) * s ^ (4 : ℕ) + (11 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-66 : ℂ) + (-103 : ℂ) * s + (-24 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-18 : ℂ) + (-6 : ℂ) * s))))))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ))

theorem srcCurrentSS_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCurrent s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = srcCurrentSS s r := by
  unfold srcCurrent
  rw [srcPieceSS_qtr0 s r hr hf hs hs3 hs1, srcPieceSS_qtr1 s r hr hf hs hs3 hs1, srcPieceSS_qtr2 s r hr hf hs hs3 hs1, srcPieceSS_qt0 s r hr hf hs hs3 hs1, srcPieceSS_qt1 s r hr hf hs hs3 hs1, srcPieceSS_qt2 s r hr hf hs hs3 hs1, srcPieceSS_qT0 s r hr hf hs hs3 hs1, srcPieceSS_qT1 s r hr hf hs hs3 hs1, srcPieceSS_qT2 s r hr hf hs hs3 hs1, srcPieceSS_qT3 s r hr hf hs hs3 hs1]
  unfold srcCurrentSS
  simp only [← add_div]
  ring

/-! ## The VV source current at the fundamental harmonic -/
theorem srcPieceVV_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr0 s r ((s + 1) * (s + 2)) * vvSourceTR s r ((s + 1) * (s + 2)) = (((-9 : ℂ) * s + (-24 : ℂ) * s ^ (2 : ℕ) + (-97 / 4 : ℂ) * s ^ (3 : ℕ) + (-47 / 4 : ℂ) * s ^ (4 : ℕ) + (-11 / 4 : ℂ) * s ^ (5 : ℕ) + (-1 / 4 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((9 : ℂ) + (69 : ℂ) * s + (235 / 4 : ℂ) * s ^ (2 : ℕ) + (-389 / 4 : ℂ) * s ^ (3 : ℕ) + (-695 / 4 : ℂ) * s ^ (4 : ℕ) + (-405 / 4 : ℂ) * s ^ (5 : ℕ) + (-26 : ℂ) * s ^ (6 : ℕ) + (-5 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-60 : ℂ) + (130 : ℂ) * s + (1201 / 2 : ℂ) * s ^ (2 : ℕ) + (2447 / 4 : ℂ) * s ^ (3 : ℕ) + (493 / 4 : ℂ) * s ^ (4 : ℕ) + (-743 / 4 : ℂ) * s ^ (5 : ℕ) + (-575 / 4 : ℂ) * s ^ (6 : ℕ) + (-40 : ℂ) * s ^ (7 : ℕ) + (-4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-129 : ℂ) + (-460 : ℂ) * s + (-385 / 4 : ℂ) * s ^ (2 : ℕ) + (3189 / 4 : ℂ) * s ^ (3 : ℕ) + (3591 / 4 : ℂ) * s ^ (4 : ℕ) + (1773 / 4 : ℂ) * s ^ (5 : ℕ) + (259 / 2 : ℂ) * s ^ (6 : ℕ) + (47 / 2 : ℂ) * s ^ (7 : ℕ) + (2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-36 : ℂ) + (-324 : ℂ) * s + (-716 : ℂ) * s ^ (2 : ℕ) + (-1293 / 2 : ℂ) * s ^ (3 : ℕ) + (-511 / 2 : ℂ) * s ^ (4 : ℕ) + (-75 / 2 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ) * s + (-132 : ℂ) * s ^ (2 : ℕ) + (-72 : ℂ) * s ^ (3 : ℕ) + (-12 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qtr0_lam s r hs hs3 hs1, vvSourceTR_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr1 s r ((s + 1) * (s + 2)) * vvSourceTR1 s r ((s + 1) * (s + 2)) = (((-90 : ℂ) + (-231 : ℂ) * s + (-401 / 2 : ℂ) * s ^ (2 : ℕ) + (-181 / 4 : ℂ) * s ^ (3 : ℕ) + (131 / 4 : ℂ) * s ^ (4 : ℕ) + (95 / 4 : ℂ) * s ^ (5 : ℕ) + (23 / 4 : ℂ) * s ^ (6 : ℕ) + (1 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((141 : ℂ) + (416 : ℂ) * s + (1869 / 4 : ℂ) * s ^ (2 : ℕ) + (1143 / 4 : ℂ) * s ^ (3 : ℕ) + (639 / 4 : ℂ) * s ^ (4 : ℕ) + (413 / 4 : ℂ) * s ^ (5 : ℕ) + (47 : ℂ) * s ^ (6 : ℕ) + (11 : ℂ) * s ^ (7 : ℕ) + (1 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-366 : ℂ) + (-1238 : ℂ) * s + (-1380 : ℂ) * s ^ (2 : ℕ) + (-1503 / 4 : ℂ) * s ^ (3 : ℕ) + (1495 / 4 : ℂ) * s ^ (4 : ℕ) + (1347 / 4 : ℂ) * s ^ (5 : ℕ) + (445 / 4 : ℂ) * s ^ (6 : ℕ) + (17 : ℂ) * s ^ (7 : ℕ) + (1 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((363 : ℂ) + (625 : ℂ) * s + (-2943 / 4 : ℂ) * s ^ (2 : ℕ) + (-9437 / 4 : ℂ) * s ^ (3 : ℕ) + (-8027 / 4 : ℂ) * s ^ (4 : ℕ) + (-3105 / 4 : ℂ) * s ^ (5 : ℕ) + (-281 / 2 : ℂ) * s ^ (6 : ℕ) + (-19 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((168 : ℂ) + (854 : ℂ) * s + (1718 : ℂ) * s ^ (2 : ℕ) + (3371 / 2 : ℂ) * s ^ (3 : ℕ) + (1665 / 2 : ℂ) * s ^ (4 : ℕ) + (393 / 2 : ℂ) * s ^ (5 : ℕ) + (35 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((240 : ℂ) * s + (440 : ℂ) * s ^ (2 : ℕ) + (240 : ℂ) * s ^ (3 : ℕ) + (40 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qtr1_lam s r hs hs3 hs1, vvSourceTR1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qtr2 s r ((s + 1) * (s + 2)) * vvSourceTR2 s r ((s + 1) * (s + 2)) = (((270 : ℂ) + (918 : ℂ) * s + (2583 / 2 : ℂ) * s ^ (2 : ℕ) + (982 : ℂ) * s ^ (3 : ℕ) + (438 : ℂ) * s ^ (4 : ℕ) + (115 : ℂ) * s ^ (5 : ℕ) + (33 / 2 : ℂ) * s ^ (6 : ℕ) + (1 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-882 : ℂ) + (-2649 : ℂ) * s + (-2948 : ℂ) * s ^ (2 : ℕ) + (-1294 : ℂ) * s ^ (3 : ℕ) + (124 : ℂ) * s ^ (4 : ℕ) + (363 : ℂ) * s ^ (5 : ℕ) + (152 : ℂ) * s ^ (6 : ℕ) + (28 : ℂ) * s ^ (7 : ℕ) + (2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((882 : ℂ) + (2004 : ℂ) * s + (1419 / 2 : ℂ) * s ^ (2 : ℕ) + (-1818 : ℂ) * s ^ (3 : ℕ) + (-2345 : ℂ) * s ^ (4 : ℕ) + (-1224 : ℂ) * s ^ (5 : ℕ) + (-649 / 2 : ℂ) * s ^ (6 : ℕ) + (-42 : ℂ) * s ^ (7 : ℕ) + (-2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-102 : ℂ) + (371 : ℂ) * s + (2025 : ℂ) * s ^ (2 : ℕ) + (3123 : ℂ) * s ^ (3 : ℕ) + (2298 : ℂ) * s ^ (4 : ℕ) + (885 : ℂ) * s ^ (5 : ℕ) + (171 : ℂ) * s ^ (6 : ℕ) + (13 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-168 : ℂ) + (-464 : ℂ) * s + (-748 : ℂ) * s ^ (2 : ℕ) + (-813 : ℂ) * s ^ (3 : ℕ) + (-485 : ℂ) * s ^ (4 : ℕ) + (-139 : ℂ) * s ^ (5 : ℕ) + (-15 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-180 : ℂ) * s + (-330 : ℂ) * s ^ (2 : ℕ) + (-180 : ℂ) * s ^ (3 : ℕ) + (-30 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qtr2_lam s r hs hs3 hs1, vvSourceTR2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt0 s r ((s + 1) * (s + 2)) * vvSourceT s r ((s + 1) * (s + 2)) = (((-81 / 2 : ℂ) * s + (-162 : ℂ) * s ^ (2 : ℕ) + (-2133 / 8 : ℂ) * s ^ (3 : ℕ) + (-1875 / 8 : ℂ) * s ^ (4 : ℕ) + (-477 / 4 : ℂ) * s ^ (5 : ℕ) + (-141 / 4 : ℂ) * s ^ (6 : ℕ) + (-45 / 8 : ℂ) * s ^ (7 : ℕ) + (-3 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((54 : ℂ) + (171 : ℂ) * s + (921 / 2 : ℂ) * s ^ (2 : ℕ) + (3165 / 4 : ℂ) * s ^ (3 : ℕ) + (1413 / 2 : ℂ) * s ^ (4 : ℕ) + (327 : ℂ) * s ^ (5 : ℕ) + (75 : ℂ) * s ^ (6 : ℕ) + (27 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((234 : ℂ) + (435 / 2 : ℂ) * s + (-381 : ℂ) * s ^ (2 : ℕ) + (-6135 / 8 : ℂ) * s ^ (3 : ℕ) + (-4977 / 8 : ℂ) * s ^ (4 : ℕ) + (-1101 / 4 : ℂ) * s ^ (5 : ℕ) + (-237 / 4 : ℂ) * s ^ (6 : ℕ) + (-27 / 8 : ℂ) * s ^ (7 : ℕ) + (3 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-36 : ℂ) + (303 : ℂ) * s + (672 : ℂ) * s ^ (2 : ℕ) + (1827 / 4 : ℂ) * s ^ (3 : ℕ) + (345 / 2 : ℂ) * s ^ (4 : ℕ) + (66 : ℂ) * s ^ (5 : ℕ) + (39 / 2 : ℂ) * s ^ (6 : ℕ) + (9 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-198 : ℂ) + (-552 : ℂ) * s + (-1071 / 2 : ℂ) * s ^ (2 : ℕ) + (-411 / 2 : ℂ) * s ^ (3 : ℕ) + (-45 / 2 : ℂ) * s ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-54 : ℂ) + (-99 : ℂ) * s + (-54 : ℂ) * s ^ (2 : ℕ) + (-9 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qt0_lam s r hs hs3 hs1, vvSourceT_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt1 s r ((s + 1) * (s + 2)) * vvSourceT1 s r ((s + 1) * (s + 2)) = (((-270 : ℂ) * s + (-909 : ℂ) * s ^ (2 : ℕ) + (-2517 / 2 : ℂ) * s ^ (3 : ℕ) + (-3735 / 4 : ℂ) * s ^ (4 : ℕ) + (-402 : ℂ) * s ^ (5 : ℕ) + (-201 / 2 : ℂ) * s ^ (6 : ℕ) + (-27 / 2 : ℂ) * s ^ (7 : ℕ) + (-3 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((324 : ℂ) + (1242 : ℂ) * s + (2205 : ℂ) * s ^ (2 : ℕ) + (4719 / 2 : ℂ) * s ^ (3 : ℕ) + (3219 / 2 : ℂ) * s ^ (4 : ℕ) + (693 : ℂ) * s ^ (5 : ℕ) + (180 : ℂ) * s ^ (6 : ℕ) + (51 / 2 : ℂ) * s ^ (7 : ℕ) + (3 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((108 : ℂ) + (900 : ℂ) * s + (1521 : ℂ) * s ^ (2 : ℕ) + (1587 / 2 : ℂ) * s ^ (3 : ℕ) + (-399 / 4 : ℂ) * s ^ (4 : ℕ) + (-240 : ℂ) * s ^ (5 : ℕ) + (-177 / 2 : ℂ) * s ^ (6 : ℕ) + (-27 / 2 : ℂ) * s ^ (7 : ℕ) + (-3 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-972 : ℂ) + (-3402 : ℂ) * s + (-4455 : ℂ) * s ^ (2 : ℕ) + (-5445 / 2 : ℂ) * s ^ (3 : ℕ) + (-774 : ℂ) * s ^ (4 : ℕ) + (-69 : ℂ) * s ^ (5 : ℕ) + (9 : ℂ) * s ^ (6 : ℕ) + (3 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((324 : ℂ) + (1134 : ℂ) * s + (1422 : ℂ) * s ^ (2 : ℕ) + (792 : ℂ) * s ^ (3 : ℕ) + (198 : ℂ) * s ^ (4 : ℕ) + (18 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((216 : ℂ) + (396 : ℂ) * s + (216 : ℂ) * s ^ (2 : ℕ) + (36 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qt1_lam s r hs hs3 hs1, vvSourceT1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qt2 s r ((s + 1) * (s + 2)) * vvSourceT2 s r ((s + 1) * (s + 2)) = (((-540 : ℂ) + (-1926 : ℂ) * s + (-2859 : ℂ) * s ^ (2 : ℕ) + (-4605 / 2 : ℂ) * s ^ (3 : ℕ) + (-2181 / 2 : ℂ) * s ^ (4 : ℕ) + (-609 / 2 : ℂ) * s ^ (5 : ℕ) + (-93 / 2 : ℂ) * s ^ (6 : ℕ) + (-3 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((1980 : ℂ) + (6834 : ℂ) * s + (9699 : ℂ) * s ^ (2 : ℕ) + (14715 / 2 : ℂ) * s ^ (3 : ℕ) + (6447 / 2 : ℂ) * s ^ (4 : ℕ) + (1629 / 2 : ℂ) * s ^ (5 : ℕ) + (219 / 2 : ℂ) * s ^ (6 : ℕ) + (6 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-2520 : ℂ) + (-8472 : ℂ) * s + (-11553 : ℂ) * s ^ (2 : ℕ) + (-16509 / 2 : ℂ) * s ^ (3 : ℕ) + (-6615 / 2 : ℂ) * s ^ (4 : ℕ) + (-1461 / 2 : ℂ) * s ^ (5 : ℕ) + (-159 / 2 : ℂ) * s ^ (6 : ℕ) + (-3 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((1080 : ℂ) + (3816 : ℂ) * s + (5265 : ℂ) * s ^ (2 : ℕ) + (7233 / 2 : ℂ) * s ^ (3 : ℕ) + (2613 / 2 : ℂ) * s ^ (4 : ℕ) + (471 / 2 : ℂ) * s ^ (5 : ℕ) + (33 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((180 : ℂ) + (78 : ℂ) * s + (-372 : ℂ) * s ^ (2 : ℕ) + (-387 : ℂ) * s ^ (3 : ℕ) + (-132 : ℂ) * s ^ (4 : ℕ) + (-15 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-180 : ℂ) + (-330 : ℂ) * s + (-180 : ℂ) * s ^ (2 : ℕ) + (-30 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qt2_lam s r hs hs3 hs1, vvSourceT2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT0 s r ((s + 1) * (s + 2)) * vvSourceTF s r ((s + 1) * (s + 2)) = (((297 : ℂ) * s + (1413 : ℂ) * s ^ (2 : ℕ) + (11445 / 4 : ℂ) * s ^ (3 : ℕ) + (3222 : ℂ) * s ^ (4 : ℕ) + (8835 / 4 : ℂ) * s ^ (5 : ℕ) + (945 : ℂ) * s ^ (6 : ℕ) + (987 / 4 : ℂ) * s ^ (7 : ℕ) + (36 : ℂ) * s ^ (8 : ℕ) + (9 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-132 : ℂ) + (-1343 : ℂ) * s + (-9167 / 2 : ℂ) * s ^ (2 : ℕ) + (-15499 / 2 : ℂ) * s ^ (3 : ℕ) + (-14783 / 2 : ℂ) * s ^ (4 : ℕ) + (-8253 / 2 : ℂ) * s ^ (5 : ℕ) + (-2609 / 2 : ℂ) * s ^ (6 : ℕ) + (-397 / 2 : ℂ) * s ^ (7 : ℕ) + (-9 / 2 : ℂ) * s ^ (8 : ℕ) + (3 / 2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-572 : ℂ) + (883 : ℂ) * s + (6163 : ℂ) * s ^ (2 : ℕ) + (36905 / 4 : ℂ) * s ^ (3 : ℕ) + (6626 : ℂ) * s ^ (4 : ℕ) + (10267 / 4 : ℂ) * s ^ (5 : ℕ) + (449 : ℂ) * s ^ (6 : ℕ) + (-145 / 4 : ℂ) * s ^ (7 : ℕ) + (-30 : ℂ) * s ^ (8 : ℕ) + (-15 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((88 : ℂ) + (-311 : ℂ) * s + (-2303 / 2 : ℂ) * s ^ (2 : ℕ) + (-1316 : ℂ) * s ^ (3 : ℕ) + (-1925 / 2 : ℂ) * s ^ (4 : ℕ) + (-635 : ℂ) * s ^ (5 : ℕ) + (-613 / 2 : ℂ) * s ^ (6 : ℕ) + (-78 : ℂ) * s ^ (7 : ℕ) + (-15 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((484 : ℂ) + (1716 : ℂ) * s + (2341 : ℂ) * s ^ (2 : ℕ) + (1518 : ℂ) * s ^ (3 : ℕ) + (454 : ℂ) * s ^ (4 : ℕ) + (42 : ℂ) * s ^ (5 : ℕ) + (-3 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((132 : ℂ) + (342 : ℂ) * s + (318 : ℂ) * s ^ (2 : ℕ) + (126 : ℂ) * s ^ (3 : ℕ) + (18 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qT0_lam s r hs hs3 hs1, vvSourceTF_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT1 s r ((s + 1) * (s + 2)) * vvSourceTF1 s r ((s + 1) * (s + 2)) = (((1980 : ℂ) * s + (8166 : ℂ) * s ^ (2 : ℕ) + (14319 : ℂ) * s ^ (3 : ℕ) + (27921 / 2 : ℂ) * s ^ (4 : ℕ) + (16563 / 2 : ℂ) * s ^ (5 : ℕ) + (3060 : ℂ) * s ^ (6 : ℕ) + (687 : ℂ) * s ^ (7 : ℕ) + (171 / 2 : ℂ) * s ^ (8 : ℕ) + (9 / 2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-2904 : ℂ) + (-16280 : ℂ) * s + (-37294 : ℂ) * s ^ (2 : ℕ) + (-45656 : ℂ) * s ^ (3 : ℕ) + (-32318 : ℂ) * s ^ (4 : ℕ) + (-13012 : ℂ) * s ^ (5 : ℕ) + (-2466 : ℂ) * s ^ (6 : ℕ) + (56 : ℂ) * s ^ (7 : ℕ) + (102 : ℂ) * s ^ (8 : ℕ) + (12 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((2464 : ℂ) + (4272 : ℂ) * s + (-1758 : ℂ) * s ^ (2 : ℕ) + (-9384 : ℂ) * s ^ (3 : ℕ) + (-19255 / 2 : ℂ) * s ^ (4 : ℕ) + (-10659 / 2 : ℂ) * s ^ (5 : ℕ) + (-1928 : ℂ) * s ^ (6 : ℕ) + (-474 : ℂ) * s ^ (7 : ℕ) + (-141 / 2 : ℂ) * s ^ (8 : ℕ) + (-9 / 2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((5368 : ℂ) + (28604 : ℂ) * s + (55474 : ℂ) * s ^ (2 : ℕ) + (52407 : ℂ) * s ^ (3 : ℕ) + (26383 : ℂ) * s ^ (4 : ℕ) + (7180 : ℂ) * s ^ (5 : ℕ) + (1062 : ℂ) * s ^ (6 : ℕ) + (105 : ℂ) * s ^ (7 : ℕ) + (9 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-3344 : ℂ) + (-12888 : ℂ) * s + (-19440 : ℂ) * s ^ (2 : ℕ) + (-14508 : ℂ) * s ^ (3 : ℕ) + (-5548 : ℂ) * s ^ (4 : ℕ) + (-996 : ℂ) * s ^ (5 : ℕ) + (-60 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-1584 : ℂ) + (-4104 : ℂ) * s + (-3816 : ℂ) * s ^ (2 : ℕ) + (-1512 : ℂ) * s ^ (3 : ℕ) + (-216 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qT1_lam s r hs hs3 hs1, vvSourceTF1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT2 s r ((s + 1) * (s + 2)) * vvSourceTF2 s r ((s + 1) * (s + 2)) = (((5280 : ℂ) + (21512 : ℂ) * s + (36620 : ℂ) * s ^ (2 : ℕ) + (33454 : ℂ) * s ^ (3 : ℕ) + (17159 : ℂ) * s ^ (4 : ℕ) + (4318 : ℂ) * s ^ (5 : ℕ) + (-16 : ℂ) * s ^ (6 : ℕ) + (-310 : ℂ) * s ^ (7 : ℕ) + (-75 : ℂ) * s ^ (8 : ℕ) + (-6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-14080 : ℂ) + (-61296 : ℂ) * s + (-113880 : ℂ) * s ^ (2 : ℕ) + (-118252 : ℂ) * s ^ (3 : ℕ) + (-75474 : ℂ) * s ^ (4 : ℕ) + (-30682 : ℂ) * s ^ (5 : ℕ) + (-7976 : ℂ) * s ^ (6 : ℕ) + (-1300 : ℂ) * s ^ (7 : ℕ) + (-126 : ℂ) * s ^ (8 : ℕ) + (-6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((22440 : ℂ) + (104120 : ℂ) * s + (203506 : ℂ) * s ^ (2 : ℕ) + (218282 : ℂ) * s ^ (3 : ℕ) + (140129 : ℂ) * s ^ (4 : ℕ) + (54926 : ℂ) * s ^ (5 : ℕ) + (12768 : ℂ) * s ^ (6 : ℕ) + (1596 : ℂ) * s ^ (7 : ℕ) + (81 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-19800 : ℂ) + (-89668 : ℂ) * s + (-164752 : ℂ) * s ^ (2 : ℕ) + (-159202 : ℂ) * s ^ (3 : ℕ) + (-87416 : ℂ) * s ^ (4 : ℕ) + (-27268 : ℂ) * s ^ (5 : ℕ) + (-4464 : ℂ) * s ^ (6 : ℕ) + (-294 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((2200 : ℂ) + (11904 : ℂ) * s + (23134 : ℂ) * s ^ (2 : ℕ) + (21606 : ℂ) * s ^ (3 : ℕ) + (10462 : ℂ) * s ^ (4 : ℕ) + (2526 : ℂ) * s ^ (5 : ℕ) + (240 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((3960 : ℂ) + (10260 : ℂ) * s + (9540 : ℂ) * s ^ (2 : ℕ) + (3780 : ℂ) * s ^ (3 : ℕ) + (540 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qT2_lam s r hs hs3 hs1, vvSourceTF2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem srcPieceVV_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCoeff_qT3 s r ((s + 1) * (s + 2)) * vvSourceTF3 s r ((s + 1) * (s + 2)) = (((-7920 : ℂ) + (-36888 : ℂ) * s + (-74908 : ℂ) * s ^ (2 : ℕ) + (-87218 : ℂ) * s ^ (3 : ℕ) + (-64270 : ℂ) * s ^ (4 : ℕ) + (-31124 : ℂ) * s ^ (5 : ℕ) + (-9916 : ℂ) * s ^ (6 : ℕ) + (-2006 : ℂ) * s ^ (7 : ℕ) + (-234 : ℂ) * s ^ (8 : ℕ) + (-12 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((29040 : ℂ) + (131120 : ℂ) * s + (255484 : ℂ) * s ^ (2 : ℕ) + (281632 : ℂ) * s ^ (3 : ℕ) + (193048 : ℂ) * s ^ (4 : ℕ) + (84916 : ℂ) * s ^ (5 : ℕ) + (23764 : ℂ) * s ^ (6 : ℕ) + (4016 : ℂ) * s ^ (7 : ℕ) + (360 : ℂ) * s ^ (8 : ℕ) + (12 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-36960 : ℂ) + (-161672 : ℂ) * s + (-301128 : ℂ) * s ^ (2 : ℕ) + (-311762 : ℂ) * s ^ (3 : ℕ) + (-196002 : ℂ) * s ^ (4 : ℕ) + (-76472 : ℂ) * s ^ (5 : ℕ) + (-18024 : ℂ) * s ^ (6 : ℕ) + (-2334 : ℂ) * s ^ (7 : ℕ) + (-126 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((15840 : ℂ) + (69288 : ℂ) * s + (126660 : ℂ) * s ^ (2 : ℕ) + (125220 : ℂ) * s ^ (3 : ℕ) + (72168 : ℂ) * s ^ (4 : ℕ) + (24192 : ℂ) * s ^ (5 : ℕ) + (4356 : ℂ) * s ^ (6 : ℕ) + (324 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((2640 : ℂ) + (4992 : ℂ) * s + (252 : ℂ) * s ^ (2 : ℕ) + (-5352 : ℂ) * s ^ (3 : ℕ) + (-4584 : ℂ) * s ^ (4 : ℕ) + (-1512 : ℂ) * s ^ (5 : ℕ) + (-180 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-2640 : ℂ) + (-6840 : ℂ) * s + (-6360 : ℂ) * s ^ (2 : ℕ) + (-2520 : ℂ) * s ^ (3 : ℕ) + (-360 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  rw [srcCoeff_qT3_lam s r hs hs3 hs1, vvSourceTF3_lam s r hs hs3 hs1]
  field_simp
  ring

/-- The source-only radial current of the VV harmonic sources at the fundamental harmonic. -/
def srcCurrentVV (s r : ℂ) : ℂ := (((-3000 : ℂ) + (-29315 / 2 : ℂ) * s + (-31572 : ℂ) * s ^ (2 : ℕ) + (-315991 / 8 : ℂ) * s ^ (3 : ℕ) + (-253825 / 8 : ℂ) * s ^ (4 : ℕ) + (-34011 / 2 : ℂ) * s ^ (5 : ℕ) + (-24349 / 4 : ℂ) * s ^ (6 : ℕ) + (-11223 / 8 : ℂ) * s ^ (7 : ℕ) + (-1509 / 8 : ℂ) * s ^ (8 : ℕ) + (-45 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((13550 : ℂ) + (58284 : ℂ) * s + (109669 : ℂ) * s ^ (2 : ℕ) + (477509 / 4 : ℂ) * s ^ (3 : ℕ) + (83514 : ℂ) * s ^ (4 : ℕ) + (39295 : ℂ) * s ^ (5 : ℕ) + (12555 : ℂ) * s ^ (6 : ℕ) + (10593 / 4 : ℂ) * s ^ (7 : ℕ) + (336 : ℂ) * s ^ (8 : ℕ) + (39 / 2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-14350 : ℂ) + (-117711 / 2 : ℂ) * s + (-103700 : ℂ) * s ^ (2 : ℕ) + (-827581 / 8 : ℂ) * s ^ (3 : ℕ) + (-518015 / 8 : ℂ) * s ^ (4 : ℕ) + (-53255 / 2 : ℂ) * s ^ (5 : ℕ) + (-29277 / 4 : ℂ) * s ^ (6 : ℕ) + (-10665 / 8 : ℂ) * s ^ (7 : ℕ) + (-1207 / 8 : ℂ) * s ^ (8 : ℕ) + (-33 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((1700 : ℂ) + (9166 : ℂ) * s + (37811 / 2 : ℂ) * s ^ (2 : ℕ) + (80083 / 4 : ℂ) * s ^ (3 : ℕ) + (24133 / 2 : ℂ) * s ^ (4 : ℕ) + (8507 / 2 : ℂ) * s ^ (5 : ℕ) + (1705 / 2 : ℂ) * s ^ (6 : ℕ) + (351 / 4 : ℂ) * s ^ (7 : ℕ) + (7 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((2250 : ℂ) + (6450 : ℂ) * s + (14111 / 2 : ℂ) * s ^ (2 : ℕ) + (7379 / 2 : ℂ) * s ^ (3 : ℕ) + (1839 / 2 : ℂ) * s ^ (4 : ℕ) + (169 / 2 : ℂ) * s ^ (5 : ℕ) + (-1 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-150 : ℂ) + (-387 : ℂ) * s + (-358 : ℂ) * s ^ (2 : ℕ) + (-141 : ℂ) * s ^ (3 : ℕ) + (-20 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ))

theorem srcCurrentVV_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    srcCurrent s r ((s + 1) * (s + 2)) (vvSourceTR s r ((s + 1) * (s + 2))) (vvSourceTR1 s r ((s + 1) * (s + 2))) (vvSourceTR2 s r ((s + 1) * (s + 2))) (vvSourceT s r ((s + 1) * (s + 2))) (vvSourceT1 s r ((s + 1) * (s + 2))) (vvSourceT2 s r ((s + 1) * (s + 2))) (vvSourceTF s r ((s + 1) * (s + 2))) (vvSourceTF1 s r ((s + 1) * (s + 2))) (vvSourceTF2 s r ((s + 1) * (s + 2))) (vvSourceTF3 s r ((s + 1) * (s + 2))) = srcCurrentVV s r := by
  unfold srcCurrent
  rw [srcPieceVV_qtr0 s r hr hf hs hs3 hs1, srcPieceVV_qtr1 s r hr hf hs hs3 hs1, srcPieceVV_qtr2 s r hr hf hs hs3 hs1, srcPieceVV_qt0 s r hr hf hs hs3 hs1, srcPieceVV_qt1 s r hr hf hs hs3 hs1, srcPieceVV_qt2 s r hr hf hs hs3 hs1, srcPieceVV_qT0 s r hr hf hs hs3 hs1, srcPieceVV_qT1 s r hr hf hs hs3 hs1, srcPieceVV_qT2 s r hr hf hs hs3 hs1, srcPieceVV_qT3 s r hr hf hs hs3 hs1]
  unfold srcCurrentVV
  simp only [← add_div]
  ring

/-! ## The SS `++` Laurent response against the `−` mode -/

theorem ssLaurentA_lam (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : laurentMasterA s ((s + 1) * (s + 2)) = (((-6 : ℂ) + (-23 / 2 : ℂ) * s + (-5 / 2 : ℂ) * s ^ (2 : ℕ)) / ((s + 3))) := by
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  rw [laurentMasterA_resolvents s _ hμ hres]
  all_goals (try field_simp)
  all_goals (try ring_nf)
  all_goals (try field_simp)
  all_goals (try ring)

theorem ssLaurentB_lam (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) : laurentMasterB s ((s + 1) * (s + 2)) = (((1 / 2 : ℂ) * s + (11 / 8 : ℂ) * s ^ (2 : ℕ) + (11 / 8 : ℂ) * s ^ (3 : ℕ) + (5 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (5 : ℕ)) / ((s + 3))) := by
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  rw [laurentMasterB_resolvent s _ hμ]
  all_goals (try field_simp)
  all_goals (try ring)

/-- The radial current with the SS Laurent coefficients at their actual values. -/
theorem evenCurrentSS_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    evenCurrentSS s r ((s + 1) * (s + 2)) (laurentMasterA s ((s + 1) * (s + 2))) (laurentMasterB s ((s + 1) * (s + 2))) = (((15 / 8 : ℂ) * s ^ (2 : ℕ) + (103 / 16 : ℂ) * s ^ (3 : ℕ) + (17 / 2 : ℂ) * s ^ (4 : ℕ) + (43 / 8 : ℂ) * s ^ (5 : ℕ) + (13 / 8 : ℂ) * s ^ (6 : ℕ) + (3 / 16 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((3 : ℂ) + (25 / 2 : ℂ) * s + (75 / 8 : ℂ) * s ^ (2 : ℕ) + (-19 / 2 : ℂ) * s ^ (3 : ℕ) + (-115 / 8 : ℂ) * s ^ (4 : ℕ) + (-23 / 4 : ℂ) * s ^ (5 : ℕ) + (-3 / 4 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((5 / 2 : ℂ) * s + (3 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-3 : ℂ) * s + (-1 / 2 : ℂ) * s ^ (2 : ℕ)))))))) / (r ^ (7 : ℕ) * s * (s + 3)) := by
  unfold evenCurrentSS
  rw [srcCurrentSS_eq s r hr hf hs hs3 hs1, ssLaurentA_lam s hs hs3 hs1, ssLaurentB_lam s hs hs3, evenCurrent_lauR_lam s r hs hs3 hs1, evenCurrent_lauI1_lam s r hs hs3 hs1, evenCurrent_lauI3_lam s r hs hs3 hs1]
  unfold srcCurrentSS
  field_simp
  ring

/-- Slope of the linear boundary divergence of the SS flux `r²·(current)`. -/
def evenSlopeSS (s : ℂ) : ℂ := (((-3 : ℂ) + (-1 / 2 : ℂ) * s) / ((s + 3)))
/-- The `O(1/r)` remainder of the SS flux at the AdS boundary. -/
def evenRemSS (s r : ℂ) : ℂ := (((15 / 8 : ℂ) * s ^ (2 : ℕ) + (103 / 16 : ℂ) * s ^ (3 : ℕ) + (17 / 2 : ℂ) * s ^ (4 : ℕ) + (43 / 8 : ℂ) * s ^ (5 : ℕ) + (13 / 8 : ℂ) * s ^ (6 : ℕ) + (3 / 16 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((3 : ℂ) + (25 / 2 : ℂ) * s + (75 / 8 : ℂ) * s ^ (2 : ℕ) + (-19 / 2 : ℂ) * s ^ (3 : ℕ) + (-115 / 8 : ℂ) * s ^ (4 : ℕ) + (-23 / 4 : ℂ) * s ^ (5 : ℕ) + (-3 / 4 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((5 / 2 : ℂ) * s + (3 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ)))))) / (r ^ (5 : ℕ) * s * (s + 3))

/-- Boundary structure of the SS flux at the fundamental harmonic: a pure linear divergence
and no finite part. -/
theorem evenCurrentSS_boundary (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    r ^ (2 : ℕ) * evenCurrentSS s r ((s + 1) * (s + 2)) (laurentMasterA s ((s + 1) * (s + 2))) (laurentMasterB s ((s + 1) * (s + 2))) = evenSlopeSS s * r + evenRemSS s r := by
  rw [evenCurrentSS_eq s r hr hf hs hs3 hs1]
  unfold evenSlopeSS evenRemSS
  field_simp
  ring

/-! ## The VV `++` Laurent response against the `−` mode -/

theorem vvLaurentA_lam (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : vvLaurentMasterA s ((s + 1) * (s + 2)) = ((22 / 3 : ℂ) * s + (8 / 3 : ℂ) * s ^ (2 : ℕ)) := by
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  rw [vvLaurentMasterA_eq s _ hμ]
  all_goals (try field_simp)
  all_goals (try ring_nf)
  all_goals (try field_simp)
  all_goals (try ring)

theorem vvLaurentB_lam (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) : vvLaurentMasterB s ((s + 1) * (s + 2)) = (((-25 : ℂ) * s + (-107 / 2 : ℂ) * s ^ (2 : ℕ) + (-41 : ℂ) * s ^ (3 : ℕ) + (-29 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ)) / ((s + 3))) := by
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  unfold vvLaurentMasterB
  all_goals (try field_simp)
  all_goals (try ring)

/-- The radial current with the VV Laurent coefficients at their actual values. -/
theorem evenCurrentVV_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    evenCurrentVV s r ((s + 1) * (s + 2)) (vvLaurentMasterA s ((s + 1) * (s + 2))) (vvLaurentMasterB s ((s + 1) * (s + 2))) = (((-15 / 2 : ℂ) * s + (-103 / 4 : ℂ) * s ^ (2 : ℕ) + (-34 : ℂ) * s ^ (3 : ℕ) + (-43 / 2 : ℂ) * s ^ (4 : ℕ) + (-13 / 2 : ℂ) * s ^ (5 : ℕ) + (-3 / 4 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((88 : ℂ) + (184 : ℂ) * s + (120 : ℂ) * s ^ (2 : ℕ) + (20 : ℂ) * s ^ (3 : ℕ) + (-11 / 2 : ℂ) * s ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((66 : ℂ) + (70 : ℂ) * s + (-3 : ℂ) * s ^ (2 : ℕ) + (-7 : ℂ) * s ^ (3 : ℕ)))))) / (r ^ (7 : ℕ) * (s + 3)) := by
  unfold evenCurrentVV
  rw [srcCurrentVV_eq s r hr hf hs hs3 hs1, vvLaurentA_lam s hs hs3 hs1, vvLaurentB_lam s hs hs3, evenCurrent_lauI1_lam s r hs hs3 hs1, evenCurrent_lauI3_lam s r hs hs3 hs1]
  unfold srcCurrentVV
  field_simp
  ring

/-- Slope of the linear boundary divergence of the VV flux `r²·(current)` (none for the vector–vector block). -/
def evenSlopeVV (s : ℂ) : ℂ := (0 : ℂ)
/-- The `O(1/r)` remainder of the VV flux at the AdS boundary. -/
def evenRemVV (s r : ℂ) : ℂ := (((-15 / 2 : ℂ) * s + (-103 / 4 : ℂ) * s ^ (2 : ℕ) + (-34 : ℂ) * s ^ (3 : ℕ) + (-43 / 2 : ℂ) * s ^ (4 : ℕ) + (-13 / 2 : ℂ) * s ^ (5 : ℕ) + (-3 / 4 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((88 : ℂ) + (184 : ℂ) * s + (120 : ℂ) * s ^ (2 : ℕ) + (20 : ℂ) * s ^ (3 : ℕ) + (-11 / 2 : ℂ) * s ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((66 : ℂ) + (70 : ℂ) * s + (-3 : ℂ) * s ^ (2 : ℕ) + (-7 : ℂ) * s ^ (3 : ℕ)))))) / (r ^ (5 : ℕ) * (s + 3))

/-- Boundary structure of the VV flux at the fundamental harmonic: a pure linear divergence
and no finite part. -/
theorem evenCurrentVV_boundary (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    r ^ (2 : ℕ) * evenCurrentVV s r ((s + 1) * (s + 2)) (vvLaurentMasterA s ((s + 1) * (s + 2))) (vvLaurentMasterB s ((s + 1) * (s + 2))) = evenSlopeVV s * r + evenRemVV s r := by
  rw [evenCurrentVV_eq s r hr hf hs hs3 hs1]
  unfold evenSlopeVV evenRemVV
  field_simp
  ring

end
end RHTower.D4BMScalarStream
