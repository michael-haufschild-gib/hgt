import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewRadialCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorBoundaryFlux

/-!
# The antisymmetrized `++−−` pairing at the fundamental harmonic: density and horizon logarithm

At the fundamental harmonic `μ = (s+1)(s+2)`, with the Laurent coefficients of the `++` response
(half-rate `s`) and of the `−−` response (half-rate `−3−s`) at their actual values, the two-rate
onset current `skewRadialSS` is an explicit rational function of `r` (`skewRadialSS_eq`). Its
coordinate density `r²·(current)` is `N(s,r)/(r⁶(r²−1)·s(s+3))` with `N` even of degree eight
(`skewRadDensitySS_eq`), a Laurent polynomial in `u = 1/r` once the horizon factor and the Jacobian
are extracted (`skewRadDensitySS_substitution`). The two responses carry the envelope
`z^{s}·z^{−3−s} = z^{−3}`, an integer power, so the radial integral of the dressed density
`z^{−3}·r²·(current)` over the exterior has a logarithmic horizon divergence; its coefficient is
the finite binomial sum of the Laurent coefficients recorded in `skewRadLogCoeff_eq`, the rational
function `skewRadLogCoeff`. This coefficient is odd under the reflection `s ↦ −3−s`
(`skewRadLogCoeff_reflect`), hence purely imaginary on the critical line `s = −3/2 + it`, and its
difference at two points factors through the difference of the points
(`skewRadLogCoeff_sub`): the real part off the line is the tilt `Re ρ − 1/2` times an explicit
cofactor.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry
noncomputable section

/-! ## Horner forms at the fundamental harmonic -/

theorem ssSourceTR_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((81 / 2 : ℂ) + (243 / 2 : ℂ) * s + (1161 / 8 : ℂ) * s ^ 2 + (357 / 4 : ℂ) * s ^ 3 + (30 : ℂ) * s ^ 4 + (21 / 4 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((207 : ℂ) + (663 / 2 : ℂ) * s + (439 / 2 : ℂ) * s ^ 2 + (151 / 2 : ℂ) * s ^ 3 + (27 / 2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((81 / 2 : ℂ) + (63 / 2 : ℂ) * s + (15 / 2 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 3))))) / (r ^ 5 * (r ^ 2 - 1)) := by
  unfold ssSourceTR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTR1_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((-81 / 2 : ℂ) + (-405 / 2 : ℂ) * s + (-3105 / 8 : ℂ) * s ^ 2 + (-759 / 2 : ℂ) * s ^ 3 + (-417 / 2 : ℂ) * s ^ 4 + (-261 / 4 : ℂ) * s ^ 5 + (-87 / 8 : ℂ) * s ^ 6 + (-3 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1809 / 2 : ℂ) + (-2259 : ℂ) * s + (-18699 / 8 : ℂ) * s ^ 2 + (-5161 / 4 : ℂ) * s ^ 3 + (-803 / 2 : ℂ) * s ^ 4 + (-267 / 4 : ℂ) * s ^ 5 + (-37 / 8 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-2475 / 2 : ℂ) + (-1896 : ℂ) * s + (-1198 : ℂ) * s ^ 2 + (-395 : ℂ) * s ^ 3 + (-137 / 2 : ℂ) * s ^ 4 + (-5 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-243 / 2 : ℂ) + (-189 / 2 : ℂ) * s + (-45 / 2 : ℂ) * s ^ 2 + (-3 / 2 : ℂ) * s ^ 3))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2) := by
  unfold ssSourceTR1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTR2_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((81 : ℂ) * s + (405 : ℂ) * s ^ 2 + (3105 / 4 : ℂ) * s ^ 3 + (759 : ℂ) * s ^ 4 + (417 : ℂ) * s ^ 5 + (261 / 2 : ℂ) * s ^ 6 + (87 / 4 : ℂ) * s ^ 7 + (3 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2214 : ℂ) + (8352 : ℂ) * s + (13074 : ℂ) * s ^ 2 + (44201 / 4 : ℂ) * s ^ 3 + (10937 / 2 : ℂ) * s ^ 4 + (1589 : ℂ) * s ^ 5 + (503 / 2 : ℂ) * s ^ 6 + (67 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((12186 : ℂ) + (28131 : ℂ) * s + (27283 : ℂ) * s ^ 2 + (14298 : ℂ) * s ^ 3 + (4276 : ℂ) * s ^ 4 + (691 : ℂ) * s ^ 5 + (47 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((8154 : ℂ) + (12186 : ℂ) * s + (7512 : ℂ) * s ^ 2 + (2424 : ℂ) * s ^ 3 + (414 : ℂ) * s ^ 4 + (30 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((486 : ℂ) + (378 : ℂ) * s + (90 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 3) := by
  unfold ssSourceTR2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceT_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((-81 / 4 : ℂ) + (-81 / 2 : ℂ) * s + (-513 / 16 : ℂ) * s ^ 2 + (-201 / 16 : ℂ) * s ^ 3 + (-39 / 16 : ℂ) * s ^ 4 + (-3 / 16 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-9 / 4 : ℂ) + (-15 / 4 : ℂ) * s + (-7 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-3 / 2 : ℂ) + (-1 / 2 : ℂ) * s))))) / (r ^ 4) := by
  unfold ssSourceT
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceT1_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((81 / 2 : ℂ) + (243 / 2 : ℂ) * s + (1161 / 8 : ℂ) * s ^ 2 + (357 / 4 : ℂ) * s ^ 3 + (30 : ℂ) * s ^ 4 + (21 / 4 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((90 : ℂ) + (363 / 2 : ℂ) * s + (571 / 4 : ℂ) * s ^ 2 + (219 / 4 : ℂ) * s ^ 3 + (41 / 4 : ℂ) * s ^ 4 + (3 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((27 / 2 : ℂ) + (27 / 2 : ℂ) * s + (9 / 2 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 3))))) / (r ^ 5 * (r ^ 2 - 1)) := by
  unfold ssSourceT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceT2_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((-81 / 2 : ℂ) + (-405 / 2 : ℂ) * s + (-3105 / 8 : ℂ) * s ^ 2 + (-759 / 2 : ℂ) * s ^ 3 + (-417 / 2 : ℂ) * s ^ 4 + (-261 / 4 : ℂ) * s ^ 5 + (-87 / 8 : ℂ) * s ^ 6 + (-3 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1107 / 2 : ℂ) + (-1575 : ℂ) * s + (-14457 / 8 : ℂ) * s ^ 2 + (-2149 / 2 : ℂ) * s ^ 3 + (-1401 / 4 : ℂ) * s ^ 4 + (-119 / 2 : ℂ) * s ^ 5 + (-33 / 8 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-1035 / 2 : ℂ) + (-1002 : ℂ) * s + (-3053 / 4 : ℂ) * s ^ 2 + (-1141 / 4 : ℂ) * s ^ 3 + (-209 / 4 : ℂ) * s ^ 4 + (-15 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-81 / 2 : ℂ) + (-81 / 2 : ℂ) * s + (-27 / 2 : ℂ) * s ^ 2 + (-3 / 2 : ℂ) * s ^ 3))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2) := by
  unfold ssSourceT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTF_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((-3 : ℂ) + (-4 : ℂ) * s + (-7 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((3 : ℂ) + (1 : ℂ) * s))) / (r ^ 4 * s) := by
  unfold ssSourceTF
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTF1_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((6 : ℂ) + (14 : ℂ) * s + (23 / 2 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((6 : ℂ) * s + (5 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-6 : ℂ) + (-2 : ℂ) * s))))) / (r ^ 5 * (r ^ 2 - 1) * s) := by
  unfold ssSourceTF1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTF2_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((-6 : ℂ) + (-26 : ℂ) * s + (-79 / 2 : ℂ) * s ^ 2 + (-27 : ℂ) * s ^ 3 + (-17 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-42 : ℂ) + (-116 : ℂ) * s + (-215 / 2 : ℂ) * s ^ 2 + (-41 : ℂ) * s ^ 3 + (-11 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((30 : ℂ) + (-8 : ℂ) * s + (-21 : ℂ) * s ^ 2 + (-5 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((18 : ℂ) + (6 : ℂ) * s))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2 * s) := by
  unfold ssSourceTF2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTF3_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((12 : ℂ) * s + (52 : ℂ) * s ^ 2 + (79 : ℂ) * s ^ 3 + (54 : ℂ) * s ^ 4 + (17 : ℂ) * s ^ 5 + (2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((144 : ℂ) + (576 : ℂ) * s + (842 : ℂ) * s ^ 2 + (567 : ℂ) * s ^ 3 + (178 : ℂ) * s ^ 4 + (21 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((216 : ℂ) + (900 : ℂ) * s + (960 : ℂ) * s ^ 2 + (390 : ℂ) * s ^ 3 + (54 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-288 : ℂ) + (-24 : ℂ) * s + (114 : ℂ) * s ^ 2 + (30 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (-24 : ℂ) * s))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 3 * s) := by
  unfold ssSourceTF3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssLaurentA_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0) : laurentMasterA (-3 - s) ((s + 1) * (s + 2)) = (((-6 : ℂ) + (7 / 2 : ℂ) * s + (5 / 2 : ℂ) * s ^ 2) / (s)) := by
  have hs' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  have hs3' : (-3 : ℂ) - s + 3 ≠ 0 := by intro h; apply hs; linear_combination -h
  have hs1' : (-3 : ℂ) - s + 1 ≠ 0 := by intro h; apply hs2; linear_combination -h
  have h := ssLaurentA_lam (-3 - s) hs' hs3' hs1'
  rw [show ((-3 : ℂ) - s + 1) * (-3 - s + 2) = (s + 1) * (s + 2) by ring] at h
  rw [h]
  field_simp
  all_goals (try ring)

theorem ssLaurentB_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0) : laurentMasterB (-3 - s) ((s + 1) * (s + 2)) = (((6 : ℂ) + (25 / 2 : ℂ) * s + (11 : ℂ) * s ^ 2 + (41 / 8 : ℂ) * s ^ 3 + (5 / 4 : ℂ) * s ^ 4 + (1 / 8 : ℂ) * s ^ 5) / (s)) := by
  have hs' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  have hs3' : (-3 : ℂ) - s + 3 ≠ 0 := by intro h; apply hs; linear_combination -h
  have h := ssLaurentB_lam (-3 - s) hs' hs3'
  rw [show ((-3 : ℂ) - s + 1) * (-3 - s + 2) = (s + 1) * (s + 2) by ring] at h
  rw [h]
  field_simp
  all_goals (try ring)

theorem skewRadFF_lauR_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFF_lauR_lauR s r ((s + 1) * (s + 2)) = (((480 : ℂ) + (212 : ℂ) * s + (135 / 2 : ℂ) * s ^ 2 + (210 : ℂ) * s ^ 3 + (195 / 2 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-816 : ℂ) + (-94 : ℂ) * s + (549 / 2 : ℂ) * s ^ 2 + (-134 : ℂ) * s ^ 3 + (-195 / 2 : ℂ) * s ^ 4 + (-13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((930 : ℂ) + (656 : ℂ) * s + (36 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-90 : ℂ) + (-60 : ℂ) * s))))))) / (r * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFF_lauR_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFF_lauR_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFF_lauR_lauI1 s r ((s + 1) * (s + 2)) = (((144 : ℂ) + (96 : ℂ) * s + (-11 : ℂ) * s ^ 2 + (99 : ℂ) * s ^ 3 + (75 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-168 : ℂ) + (348 : ℂ) * s + (243 / 2 : ℂ) * s ^ 2 + (-84 : ℂ) * s ^ 3 + (-137 / 2 : ℂ) * s ^ 4 + (-13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((404 : ℂ) + (318 : ℂ) * s + (143 / 2 : ℂ) * s ^ 2 + (-27 : ℂ) * s ^ 3 + (-13 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((118 : ℂ) + (72 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((6 : ℂ)))))))))) / (r ^ 3 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFF_lauR_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFF_lauR_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFF_lauR_lauI3 s r ((s + 1) * (s + 2)) = (((16 : ℂ) + (12 : ℂ) * s + (-83 / 2 : ℂ) * s ^ 2 + (20 : ℂ) * s ^ 3 + (105 / 2 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-40 : ℂ) + (498 : ℂ) * s + (137 / 2 : ℂ) * s ^ 2 + (-98 : ℂ) * s ^ 3 + (-79 / 2 : ℂ) * s ^ 4 + (-13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((294 : ℂ) + (372 : ℂ) * s + (-45 : ℂ) * s ^ 2 + (-30 : ℂ) * s ^ 3 + (-13 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((222 : ℂ) + (72 : ℂ) * s + (12 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))))) / (r ^ 5 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFF_lauR_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFF_lauI1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFF_lauI1_lauR s r ((s + 1) * (s + 2)) = (((362 : ℂ) * s ^ 2 + (369 : ℂ) * s ^ 3 + (120 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((240 : ℂ) + (-516 : ℂ) * s + (-1377 / 2 : ℂ) * s ^ 2 + (-432 : ℂ) * s ^ 3 + (-253 / 2 : ℂ) * s ^ 4 + (-13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-296 : ℂ) + (-138 : ℂ) * s + (73 / 2 : ℂ) * s ^ 2 + (51 : ℂ) * s ^ 3 + (13 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((62 : ℂ) + (48 : ℂ) * s + (-4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-6 : ℂ)))))))))) / (r ^ 3 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFF_lauI1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFF_lauI1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFF_lauI1_lauI1 s r ((s + 1) * (s + 2)) = (((36 : ℂ) * s + (423 / 2 : ℂ) * s ^ 2 + (242 : ℂ) * s ^ 3 + (195 / 2 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((72 : ℂ) + (-474 : ℂ) * s + (-1395 / 2 : ℂ) * s ^ 2 + (-350 : ℂ) * s ^ 3 + (-195 / 2 : ℂ) * s ^ 4 + (-13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-54 : ℂ) + (-36 : ℂ) * s) + r * ((0 : ℂ) + r * ((-18 : ℂ) + (-12 : ℂ) * s))))))) / (r ^ 5 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFF_lauI1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFF_lauI1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFF_lauI1_lauI3 s r ((s + 1) * (s + 2)) = (((32 : ℂ) * s + (117 : ℂ) * s ^ 2 + (147 : ℂ) * s ^ 3 + (75 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((8 : ℂ) + (-316 : ℂ) * s + (-1261 / 2 : ℂ) * s ^ 2 + (-332 : ℂ) * s ^ 3 + (-137 / 2 : ℂ) * s ^ 4 + (-13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-20 : ℂ) + (-142 : ℂ) * s + (-329 / 2 : ℂ) * s ^ 2 + (-19 : ℂ) * s ^ 3 + (-13 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((6 : ℂ) + (60 : ℂ) * s) + r * ((0 : ℂ) + r * ((6 : ℂ)))))))))) / (r ^ 7 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFF_lauI1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFF_lauI3_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFF_lauI3_lauR s r ((s + 1) * (s + 2)) = (((-160 : ℂ) + (396 : ℂ) * s + (1793 / 2 : ℂ) * s ^ 2 + (560 : ℂ) * s ^ 3 + (285 / 2 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-1688 : ℂ) + (-3558 : ℂ) * s + (-4655 / 2 : ℂ) * s ^ 2 + (-794 : ℂ) * s ^ 3 + (-311 / 2 : ℂ) * s ^ 4 + (-13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1470 : ℂ) + (1236 : ℂ) * s + (477 : ℂ) * s ^ 2 + (126 : ℂ) * s ^ 3 + (13 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-114 : ℂ) + (-12 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))))) / (r ^ 5 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFF_lauI3_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFF_lauI3_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFF_lauI3_lauI1 s r ((s + 1) * (s + 2)) = (((96 : ℂ) + (464 : ℂ) * s + (666 : ℂ) * s ^ 2 + (417 : ℂ) * s ^ 3 + (120 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-1856 : ℂ) + (-3364 : ℂ) * s + (-4337 / 2 : ℂ) * s ^ 2 + (-680 : ℂ) * s ^ 3 + (-253 / 2 : ℂ) * s ^ 4 + (-13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1088 : ℂ) + (1034 : ℂ) * s + (689 / 2 : ℂ) * s ^ 2 + (59 : ℂ) * s ^ 3 + (13 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((174 : ℂ) + (60 : ℂ) * s) + r * ((0 : ℂ) + r * ((-6 : ℂ)))))))))) / (r ^ 7 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFF_lauI3_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFF_lauI3_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFF_lauI3_lauI3 s r ((s + 1) * (s + 2)) = (((144 : ℂ) + (420 : ℂ) * s + (999 / 2 : ℂ) * s ^ 2 + (306 : ℂ) * s ^ 3 + (195 / 2 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-1296 : ℂ) + (-2646 : ℂ) * s + (-3915 / 2 : ℂ) * s ^ 2 + (-630 : ℂ) * s ^ 3 + (-195 / 2 : ℂ) * s ^ 4 + (-13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-126 : ℂ) + (24 : ℂ) * s + (108 : ℂ) * s ^ 2 + (24 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((774 : ℂ) + (516 : ℂ) * s))))))) / (r ^ 9 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFF_lauI3_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauR_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauR_qt0 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) * s + (-32 : ℂ) * s ^ 2 + (11 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-148 : ℂ) + (348 : ℂ) * s + (-61 : ℂ) * s ^ 2 + (-199 : ℂ) * s ^ 3 + (-29 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((376 : ℂ) + (2 : ℂ) * s + (-201 : ℂ) * s ^ 2 + (32 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-228 : ℂ) + (-150 : ℂ) * s + (-6 : ℂ) * s ^ 2))))))) / (r * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauR_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauR_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauR_qtr0 s r ((s + 1) * (s + 2)) = (((-11 / 2 : ℂ) * s + (-15 / 2 : ℂ) * s ^ 2 + (7 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-86 : ℂ) + (309 / 2 : ℂ) * s + (-117 / 2 : ℂ) * s ^ 2 + (-80 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((218 : ℂ) + (59 / 2 : ℂ) * s + (-193 / 2 : ℂ) * s ^ 2 + (25 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-138 : ℂ) + (-165 / 2 : ℂ) * s + (-11 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((6 : ℂ)))))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauR_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauR_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauR_qT0 s r ((s + 1) * (s + 2)) = (((4 : ℂ) * s + (54 : ℂ) * s ^ 2 + (21 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((288 : ℂ) + (-666 : ℂ) * s + (55 : ℂ) * s ^ 2 + (352 : ℂ) * s ^ 3 + (93 : ℂ) * s ^ 4 + (14 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-864 : ℂ) + (420 : ℂ) * s + (372 : ℂ) * s ^ 2 + (-279 : ℂ) * s ^ 3 + (-98 : ℂ) * s ^ 4 + (-11 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((792 : ℂ) + (230 : ℂ) * s + (-241 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-216 : ℂ) + (-132 : ℂ) * s))))))))) / (r * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauR_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauR_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauR_qT1 s r ((s + 1) * (s + 2)) = (((-41 : ℂ) * s + (-47 / 2 : ℂ) * s ^ 2 + (19 : ℂ) * s ^ 3 + (3 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-204 : ℂ) + (290 : ℂ) * s + (-9 : ℂ) * s ^ 2 + (-158 : ℂ) * s ^ 3 + (-7 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((508 : ℂ) + (93 : ℂ) * s + (-483 / 2 : ℂ) * s ^ 2 + (43 : ℂ) * s ^ 3 + (11 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-328 : ℂ) + (-174 : ℂ) * s + (-14 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauR_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI1_qt0 s r ((s + 1) * (s + 2)) = (((12 : ℂ) * s + (27 : ℂ) * s ^ 2 + (13 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-178 : ℂ) * s + (-445 : ℂ) * s ^ 2 + (-227 : ℂ) * s ^ 3 + (-27 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-76 : ℂ) + (274 : ℂ) * s + (126 : ℂ) * s ^ 2 + (58 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((88 : ℂ) + (84 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))))) / (r ^ 3 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI1_qtr0 s r ((s + 1) * (s + 2)) = (((15 / 2 : ℂ) * s + (31 / 2 : ℂ) * s ^ 2 + (7 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-181 / 2 : ℂ) * s + (-403 / 2 : ℂ) * s ^ 2 + (-80 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-44 : ℂ) + (241 / 2 : ℂ) * s + (49 / 2 : ℂ) * s ^ 2 + (25 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((56 : ℂ) + (117 / 2 : ℂ) * s + (-13 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))))) / (r ^ 2 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI1_qT0 s r ((s + 1) * (s + 2)) = (((-24 : ℂ) * s + (-57 : ℂ) * s ^ 2 + (-45 : ℂ) * s ^ 3 + (-15 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((358 : ℂ) * s + (896 : ℂ) * s ^ 2 + (582 : ℂ) * s ^ 3 + (142 : ℂ) * s ^ 4 + (14 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((148 : ℂ) + (-704 : ℂ) * s + (-793 : ℂ) * s ^ 2 + (-541 : ℂ) * s ^ 3 + (-139 : ℂ) * s ^ 4 + (-11 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-236 : ℂ) + (142 : ℂ) * s + (202 : ℂ) * s ^ 2 + (100 : ℂ) * s ^ 3 + (12 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((100 : ℂ) + (84 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))))))) / (r ^ 3 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauI1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI1_qT1 s r ((s + 1) * (s + 2)) = (((21 : ℂ) * s + (117 / 2 : ℂ) * s ^ 2 + (27 : ℂ) * s ^ 3 + (3 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-200 : ℂ) * s + (-375 : ℂ) * s ^ 2 + (-174 : ℂ) * s ^ 3 + (-7 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-104 : ℂ) + (215 : ℂ) * s + (105 / 2 : ℂ) * s ^ 2 + (51 : ℂ) * s ^ 3 + (11 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((140 : ℂ) + (132 : ℂ) * s + (-24 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-36 : ℂ)))))))))) / (r ^ 2 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauI1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI3_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI3_qt0 s r ((s + 1) * (s + 2)) = (((80 : ℂ) + (152 : ℂ) * s + (94 : ℂ) * s ^ 2 + (15 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-668 : ℂ) + (-1256 : ℂ) * s + (-853 : ℂ) * s ^ 2 + (-255 : ℂ) * s ^ 3 + (-25 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((864 : ℂ) + (1290 : ℂ) * s + (477 : ℂ) * s ^ 2 + (84 : ℂ) * s ^ 3 + (5 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-252 : ℂ) + (6 : ℂ) * s + (-18 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))))) / (r ^ 5 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI3_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI3_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI3_qtr0 s r ((s + 1) * (s + 2)) = (((40 : ℂ) + (137 / 2 : ℂ) * s + (77 / 2 : ℂ) * s ^ 2 + (7 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-322 : ℂ) + (-1151 / 2 : ℂ) * s + (-689 / 2 : ℂ) * s ^ 2 + (-80 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((390 : ℂ) + (1095 / 2 : ℂ) * s + (291 / 2 : ℂ) * s ^ 2 + (25 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-78 : ℂ) + (111 / 2 : ℂ) * s + (-15 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-30 : ℂ)))))))))) / (r ^ 4 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI3_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI3_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI3_qT0 s r ((s + 1) * (s + 2)) = (((-160 : ℂ) + (-388 : ℂ) * s + (-360 : ℂ) * s ^ 2 + (-159 : ℂ) * s ^ 3 + (-34 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1424 : ℂ) + (2894 : ℂ) * s + (2321 : ℂ) * s ^ 2 + (956 : ℂ) * s ^ 3 + (191 : ℂ) * s ^ 4 + (14 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-2440 : ℂ) + (-4156 : ℂ) * s + (-2558 : ℂ) * s ^ 2 + (-947 : ℂ) * s ^ 3 + (-180 : ℂ) * s ^ 4 + (-11 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1440 : ℂ) + (1518 : ℂ) * s + (861 : ℂ) * s ^ 2 + (246 : ℂ) * s ^ 3 + (23 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-240 : ℂ) + (-12 : ℂ) * s + (-24 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauI3_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI3_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI3_qT1 s r ((s + 1) * (s + 2)) = (((80 : ℂ) + (203 : ℂ) * s + (297 / 2 : ℂ) * s ^ 2 + (35 : ℂ) * s ^ 3 + (3 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-612 : ℂ) + (-1242 : ℂ) * s + (-765 : ℂ) * s ^ 2 + (-190 : ℂ) * s ^ 3 + (-7 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((676 : ℂ) + (1081 : ℂ) * s + (741 / 2 : ℂ) * s ^ 2 + (59 : ℂ) * s ^ 3 + (11 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-48 : ℂ) + (126 : ℂ) * s + (-42 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-96 : ℂ)))))))))) / (r ^ 4 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauI3_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauR_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauR_qt1 s r ((s + 1) * (s + 2)) = (((9 : ℂ) * s + (-9 / 2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((24 : ℂ) + (27 : ℂ) * s + (-79 / 2 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-36 : ℂ) + (-12 : ℂ) * s + (-4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauR_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauR_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauR_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-4 : ℂ) + (5 / 2 : ℂ) * s + (-7 / 2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((22 : ℂ) + (16 : ℂ) * s + (-17 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-26 : ℂ) + (-13 / 2 : ℂ) * s + (-7 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((8 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauR_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauR_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauR_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-16 : ℂ) + (7 : ℂ) * s + (-9 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((60 : ℂ) + (29 : ℂ) * s + (-31 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-62 : ℂ) + (-12 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((18 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauR_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI1_qt1 s r ((s + 1) * (s + 2)) = (((-3 : ℂ) * s + (-17 / 2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((3 : ℂ) * s + (-63 / 2 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((12 : ℂ) + (24 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (r ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI1_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI1_qtr1 s r ((s + 1) * (s + 2)) = (((-1 / 2 : ℂ) * s + (-9 / 2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-2 : ℂ) + (-2 : ℂ) * s + (-15 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((10 : ℂ) + (29 / 2 : ℂ) * s + (-9 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))))) / (r * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI1_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI1_qT2 s r ((s + 1) * (s + 2)) = (((1 : ℂ) * s + (-11 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-8 : ℂ) + (-7 : ℂ) * s + (-27 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((26 : ℂ) + (30 : ℂ) * s + (-10 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-18 : ℂ)))))))) / (r * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauI1_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI3_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI3_qt1 s r ((s + 1) * (s + 2)) = (((-15 : ℂ) * s + (-25 / 2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-24 : ℂ) + (-21 : ℂ) * s + (-47 / 2 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((60 : ℂ) + (60 : ℂ) * s + (-12 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-36 : ℂ)))))))) / (r ^ 4 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI3_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI3_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI3_qtr1 s r ((s + 1) * (s + 2)) = (((4 : ℂ) + (-7 / 2 : ℂ) * s + (-11 / 2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-26 : ℂ) + (-20 : ℂ) * s + (-13 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((46 : ℂ) + (71 / 2 : ℂ) * s + (-11 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))) / (r ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI3_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI3_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI3_qT2 s r ((s + 1) * (s + 2)) = (((16 : ℂ) + (-5 : ℂ) * s + (-13 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-76 : ℂ) + (-43 : ℂ) * s + (-23 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((114 : ℂ) + (72 : ℂ) * s + (-12 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-54 : ℂ)))))))) / (r ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauI3_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauR_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauR_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-4 : ℂ) + (1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((10 : ℂ) + (-2 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-8 : ℂ) + (1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((2 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauR_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauR_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauR_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-2 : ℂ) + (1 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((5 : ℂ) + (-1 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-4 : ℂ) + (1 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((1 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauR_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauR_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauR_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ) + (1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((10 : ℂ) + (-2 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-8 : ℂ) + (1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauR_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI1_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI1_qt2 s r ((s + 1) * (s + 2)) = (((1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-2 : ℂ) + (-2 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((4 : ℂ) + (1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-2 : ℂ)))))))) / (r * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI1_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI1_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI1_qtr2 s r ((s + 1) * (s + 2)) = (((1 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-1 : ℂ) + (-1 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((2 : ℂ) + (1 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-1 : ℂ)))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI1_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI1_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI1_qT3 s r ((s + 1) * (s + 2)) = (((1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-2 : ℂ) + (-2 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((4 : ℂ) + (1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-2 : ℂ)))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauI1_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI3_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI3_qt2 s r ((s + 1) * (s + 2)) = (((4 : ℂ) + (1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-14 : ℂ) + (-2 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((16 : ℂ) + (1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-6 : ℂ)))))))) / (r ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI3_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI3_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI3_qtr2 s r ((s + 1) * (s + 2)) = (((2 : ℂ) + (1 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-7 : ℂ) + (-1 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((8 : ℂ) + (1 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-3 : ℂ)))))))) / (r ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadFQ_lauI3_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadFQ_lauI3_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadFQ_lauI3_qT3 s r ((s + 1) * (s + 2)) = (((4 : ℂ) + (1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-14 : ℂ) + (-2 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((16 : ℂ) + (1 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-6 : ℂ)))))))) / (r ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadFQ_lauI3_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qt0_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qt0_lauR s r ((s + 1) * (s + 2)) = (((-480 : ℂ) + (-292 : ℂ) * s + (31 : ℂ) * s ^ 2 + (55 : ℂ) * s ^ 3 + (13 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1040 : ℂ) + (1122 : ℂ) * s + (-106 : ℂ) * s ^ 2 + (-239 : ℂ) * s ^ 3 + (-44 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-1736 : ℂ) + (-1316 : ℂ) * s + (-111 : ℂ) * s ^ 2 + (52 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((168 : ℂ) + (114 : ℂ) * s + (-6 : ℂ) * s ^ 2))))))) / (r * (r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qt0_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qt1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qt1_lauR s r ((s + 1) * (s + 2)) = (((45 : ℂ) * s + (63 / 2 : ℂ) * s ^ 2 + (7 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-480 : ℂ) + (-345 : ℂ) * s + (-151 / 2 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-36 : ℂ) + (-12 : ℂ) * s + (-4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qt1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qtr0_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qtr0_lauR s r ((s + 1) * (s + 2)) = (((-240 : ℂ) + (-457 / 2 : ℂ) * s + (-141 / 2 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((760 : ℂ) + (2445 / 2 : ℂ) * s + (891 / 2 : ℂ) * s ^ 2 + (32 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-1090 : ℂ) + (-1703 / 2 : ℂ) * s + (-211 / 2 : ℂ) * s ^ 2 + (23 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((60 : ℂ) + (99 / 2 : ℂ) * s + (-11 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((6 : ℂ)))))))))) / ((r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qtr0_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qtr1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qtr1_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-16 : ℂ) + (7 / 2 : ℂ) * s + (11 / 2 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-206 : ℂ) + (-145 : ℂ) * s + (-26 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-38 : ℂ) + (-29 / 2 : ℂ) * s + (-7 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((8 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qtr1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT0_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT0_lauR s r ((s + 1) * (s + 2)) = (((-960 : ℂ) + (-1400 : ℂ) * s + (-891 : ℂ) * s ^ 2 + (-297 : ℂ) * s ^ 3 + (-49 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((2592 : ℂ) + (4134 : ℂ) * s + (1871 : ℂ) * s ^ 2 + (496 : ℂ) * s ^ 3 + (117 : ℂ) * s ^ 4 + (14 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-3492 : ℂ) + (-3216 : ℂ) * s + (-561 : ℂ) * s ^ 2 + (-93 : ℂ) * s ^ 3 + (-67 : ℂ) * s ^ 4 + (-11 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((2040 : ℂ) + (1622 : ℂ) * s + (205 : ℂ) * s ^ 2 + (-10 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-180 : ℂ) + (-132 : ℂ) * s))))))))) / (r * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT0_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT1_lauR s r ((s + 1) * (s + 2)) = (((480 : ℂ) + (451 : ℂ) * s + (227 / 2 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3 + (-3 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-2544 : ℂ) + (-3166 : ℂ) * s + (-1035 : ℂ) * s ^ 2 + (-74 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((2660 : ℂ) + (2109 : ℂ) * s + (663 / 2 : ℂ) * s ^ 2 + (-23 : ℂ) * s ^ 3 + (-11 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-68 : ℂ) + (-90 : ℂ) * s + (14 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT2_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT2_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((64 : ℂ) + (7 : ℂ) * s + (-9 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((360 : ℂ) + (269 : ℂ) * s + (49 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((98 : ℂ) + (36 : ℂ) * s + (8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-18 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT2_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qt0_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qt0_lauI1 s r ((s + 1) * (s + 2)) = (((-144 : ℂ) + (-120 : ℂ) * s + (18 : ℂ) * s ^ 2 + (41 : ℂ) * s ^ 3 + (12 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((228 : ℂ) + (316 : ℂ) * s + (-130 : ℂ) * s ^ 2 + (-187 : ℂ) * s ^ 3 + (-42 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-844 : ℂ) + (-436 : ℂ) * s + (-72 : ℂ) * s ^ 2 + (14 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-236 : ℂ) + (-132 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))))) / (r ^ 3 * (r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qt0_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qt1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qt1_lauI1 s r ((s + 1) * (s + 2)) = (((33 : ℂ) * s + (55 / 2 : ℂ) * s ^ 2 + (7 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-360 : ℂ) + (-273 : ℂ) * s + (-135 / 2 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-132 : ℂ) + (-72 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (r ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qt1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qtr0_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qtr0_lauI1 s r ((s + 1) * (s + 2)) = (((-72 : ℂ) + (-207 / 2 : ℂ) * s + (-95 / 2 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((294 : ℂ) + (1219 / 2 : ℂ) * s + (605 / 2 : ℂ) * s ^ 2 + (32 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-536 : ℂ) + (-433 / 2 : ℂ) * s + (31 / 2 : ℂ) * s ^ 2 + (23 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-178 : ℂ) + (-195 / 2 : ℂ) * s + (-13 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))))) / (r ^ 2 * (r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qtr0_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qtr1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qtr1_lauI1 s r ((s + 1) * (s + 2)) = (((-12 : ℂ) + (1 / 2 : ℂ) * s + (9 / 2 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-158 : ℂ) + (-115 : ℂ) * s + (-24 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-74 : ℂ) + (-83 / 2 : ℂ) * s + (-9 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))))) / (r * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qtr1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT0_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT0_lauI1 s r ((s + 1) * (s + 2)) = (((-288 : ℂ) + (-492 : ℂ) * s + (-348 : ℂ) * s ^ 2 + (-135 : ℂ) * s ^ 3 + (-30 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((624 : ℂ) + (1030 : ℂ) * s + (454 : ℂ) * s ^ 2 + (138 : ℂ) * s ^ 3 + (68 : ℂ) * s ^ 4 + (14 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-1144 : ℂ) + (4 : ℂ) * s + (460 : ℂ) * s ^ 2 + (137 : ℂ) * s ^ 3 + (-26 : ℂ) * s ^ 4 + (-11 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((572 : ℂ) + (334 : ℂ) * s + (50 : ℂ) * s ^ 2 + (-44 : ℂ) * s ^ 3 + (-12 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((224 : ℂ) + (132 : ℂ) * s + (8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))))))) / (r ^ 3 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT0_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT1_lauI1 s r ((s + 1) * (s + 2)) = (((144 : ℂ) + (237 : ℂ) * s + (207 / 2 : ℂ) * s ^ 2 + (9 : ℂ) * s ^ 3 + (-3 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-1356 : ℂ) + (-1892 : ℂ) * s + (-813 : ℂ) * s ^ 2 + (-90 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((1208 : ℂ) + (683 : ℂ) * s + (219 / 2 : ℂ) * s ^ 2 + (-15 : ℂ) * s ^ 3 + (-11 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((472 : ℂ) + (276 : ℂ) * s + (24 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((36 : ℂ)))))))))) / (r ^ 2 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT2_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT2_lauI1 s r ((s + 1) * (s + 2)) = (((48 : ℂ) + (13 : ℂ) * s + (-7 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((284 : ℂ) + (209 : ℂ) * s + (45 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((154 : ℂ) + (90 : ℂ) * s + (10 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((18 : ℂ)))))))) / (r * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT2_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qt0_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qt0_lauI3 s r ((s + 1) * (s + 2)) = (((-16 : ℂ) + (-20 : ℂ) * s + (13 : ℂ) * s ^ 2 + (27 : ℂ) * s ^ 3 + (11 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((40 : ℂ) + (-82 : ℂ) * s + (-178 : ℂ) * s ^ 2 + (-135 : ℂ) * s ^ 3 + (-40 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-576 : ℂ) + (-156 : ℂ) * s + (-9 : ℂ) * s ^ 2 + (-24 : ℂ) * s ^ 3 + (5 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-432 : ℂ) + (-114 : ℂ) * s + (-18 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))))) / (r ^ 5 * (r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qt0_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qt1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qt1_lauI3 s r ((s + 1) * (s + 2)) = (((21 : ℂ) * s + (47 / 2 : ℂ) * s ^ 2 + (7 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-240 : ℂ) + (-201 : ℂ) * s + (-119 / 2 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-228 : ℂ) + (-132 : ℂ) * s + (-12 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-36 : ℂ)))))))) / (r ^ 4 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qt1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qtr0_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qtr0_lauI3 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) + (-53 / 2 : ℂ) * s + (-49 / 2 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((140 : ℂ) + (473 / 2 : ℂ) * s + (319 / 2 : ℂ) * s ^ 2 + (32 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-294 : ℂ) + (165 / 2 : ℂ) * s + (273 / 2 : ℂ) * s ^ 2 + (23 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-312 : ℂ) + (-201 / 2 : ℂ) * s + (-15 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-30 : ℂ)))))))))) / (r ^ 4 * (r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qtr0_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qtr1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qtr1_lauI3 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) + (-5 / 2 : ℂ) * s + (7 / 2 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-110 : ℂ) + (-85 : ℂ) * s + (-22 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-110 : ℂ) + (-137 / 2 : ℂ) * s + (-11 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))) / (r ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qtr1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT0_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT0_lauI3 s r ((s + 1) * (s + 2)) = (((-32 : ℂ) + (-64 : ℂ) * s + (-45 : ℂ) * s ^ 2 + (-21 : ℂ) * s ^ 3 + (-11 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((112 : ℂ) + (-178 : ℂ) * s + (-251 : ℂ) * s ^ 2 + (-76 : ℂ) * s ^ 3 + (19 : ℂ) * s ^ 4 + (14 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-668 : ℂ) + (608 : ℂ) * s + (785 : ℂ) * s ^ 2 + (223 : ℂ) * s ^ 3 + (15 : ℂ) * s ^ 4 + (-11 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((144 : ℂ) + (510 : ℂ) * s + (111 : ℂ) * s ^ 2 + (-30 : ℂ) * s ^ 3 + (-23 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((420 : ℂ) + (132 : ℂ) * s + (24 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT0_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT1_lauI3 s r ((s + 1) * (s + 2)) = (((16 : ℂ) + (95 : ℂ) * s + (171 / 2 : ℂ) * s ^ 2 + (17 : ℂ) * s ^ 3 + (-3 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-792 : ℂ) + (-1026 : ℂ) * s + (-567 : ℂ) * s ^ 2 + (-106 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((380 : ℂ) + (-143 : ℂ) * s + (-273 / 2 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3 + (-11 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((804 : ℂ) + (378 : ℂ) * s + (42 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((96 : ℂ)))))))))) / (r ^ 4 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT2_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT2_lauI3 s r ((s + 1) * (s + 2)) = (((32 : ℂ) + (19 : ℂ) * s + (-5 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((208 : ℂ) + (149 : ℂ) * s + (41 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((210 : ℂ) + (144 : ℂ) * s + (12 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((54 : ℂ)))))))) / (r ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT2_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qt2_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qt2_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-16 : ℂ) + (-7 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((34 : ℂ) + (14 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-20 : ℂ) + (-7 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((2 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qt2_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qtr2_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qtr2_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ) + (-7 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((17 : ℂ) + (7 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-10 : ℂ) + (-7 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((1 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qtr2_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT3_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT3_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((16 : ℂ) + (7 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-34 : ℂ) + (-14 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((20 : ℂ) + (7 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-2 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT3_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qt2_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qt2_lauI1 s r ((s + 1) * (s + 2)) = (((-12 : ℂ) + (-7 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((22 : ℂ) + (14 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-8 : ℂ) + (-7 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-2 : ℂ)))))))) / (r * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qt2_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qtr2_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qtr2_lauI1 s r ((s + 1) * (s + 2)) = (((-6 : ℂ) + (-7 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((11 : ℂ) + (7 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-4 : ℂ) + (-7 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-1 : ℂ)))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qtr2_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT3_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT3_lauI1 s r ((s + 1) * (s + 2)) = (((12 : ℂ) + (7 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-22 : ℂ) + (-14 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((8 : ℂ) + (7 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT3_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qt2_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qt2_lauI3 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) + (-7 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((10 : ℂ) + (14 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((4 : ℂ) + (-7 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-6 : ℂ)))))))) / (r ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qt2_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qtr2_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qtr2_lauI3 s r ((s + 1) * (s + 2)) = (((-4 : ℂ) + (-7 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((5 : ℂ) + (7 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((2 : ℂ) + (-7 / 2 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-3 : ℂ)))))))) / (r ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQF_qtr2_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQF_qT3_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQF_qT3_lauI3 s r ((s + 1) * (s + 2)) = (((8 : ℂ) + (7 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-10 : ℂ) + (-14 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-4 : ℂ) + (7 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((6 : ℂ)))))))) / (r ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQF_qT3_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr0_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr0_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-72 : ℂ) + (-48 : ℂ) * s) + r * ((0 : ℂ) + r * ((144 : ℂ) + (96 : ℂ) * s)))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qtr0_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr0_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr0_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((2 : ℂ)) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-12 : ℂ) * s) + r * ((0 : ℂ) + r * (((18 : ℂ) + (12 : ℂ) * s) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qtr0_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr0_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr0_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((1 : ℂ)) + r * ((0 : ℂ) + r * (((-3 : ℂ)) + r * ((0 : ℂ) + r * (((3 : ℂ)) + r * ((0 : ℂ) + r * ((-1 : ℂ))))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qtr0_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr0_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr0_qt0 s r ((s + 1) * (s + 2)) = (((3 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-132 : ℂ) + (-78 : ℂ) * s + (34 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((264 : ℂ) + (171 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qtr0_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr0_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr0_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-3 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-18 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((24 : ℂ) + (21 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qtr0_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr0_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr0_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((2 : ℂ)) + r * ((0 : ℂ) + r * (((-6 : ℂ)) + r * ((0 : ℂ) + r * (((6 : ℂ)) + r * ((0 : ℂ) + r * ((-2 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qtr0_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr0_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr0_qT0 s r ((s + 1) * (s + 2)) = (((-9 : ℂ) * s + (-3 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((260 : ℂ) + (141 : ℂ) * s + (-109 : ℂ) * s ^ 2 + (-60 : ℂ) * s ^ 3 + (-8 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-644 : ℂ) + (-315 : ℂ) * s + (123 : ℂ) * s ^ 2 + (60 : ℂ) * s ^ 3 + (8 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((228 : ℂ) + (135 : ℂ) * s + (-11 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))))) / ((r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qtr0_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr0_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr0_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-9 : ℂ) * s + (-3 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-160 : ℂ) + (-132 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((316 : ℂ) + (213 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qtr0_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr0_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr0_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * (((-34 : ℂ) + (-24 : ℂ) * s) + r * ((0 : ℂ) + r * (((44 : ℂ) + (24 : ℂ) * s) + r * ((0 : ℂ) + r * ((-18 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qtr0_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr0_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr0_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((2 : ℂ)) + r * ((0 : ℂ) + r * (((-6 : ℂ)) + r * ((0 : ℂ) + r * (((6 : ℂ)) + r * ((0 : ℂ) + r * ((-2 : ℂ))))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qtr0_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr1_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-2 : ℂ)) + r * ((0 : ℂ) + r * (((-24 : ℂ) + (-12 : ℂ) * s) + r * ((0 : ℂ) + r * (((18 : ℂ) + (12 : ℂ) * s) + r * ((0 : ℂ) + r * ((8 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qtr1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr1_qtr1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr1_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr1_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr1_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr1_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr1_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-4 : ℂ) + (3 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-48 : ℂ) + (-30 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((36 : ℂ) + (27 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((16 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qtr1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr1_qt1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr1_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr1_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr1_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr1_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr1_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-8 : ℂ) + (-3 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-100 : ℂ) + (-24 : ℂ) * s + (8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((20 : ℂ) + (3 : ℂ) * s + (-7 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((16 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qtr1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr1_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ) + (3 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-48 : ℂ) + (-30 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((36 : ℂ) + (27 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((16 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qtr1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr1_qT2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr1_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr1_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr1_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr1_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr2_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr2_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-1 : ℂ)) + r * ((0 : ℂ) + r * (((3 : ℂ)) + r * ((0 : ℂ) + r * (((-3 : ℂ)) + r * ((0 : ℂ) + r * ((1 : ℂ))))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qtr2_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr2_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr2_qtr1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr2_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr2_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr2_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr2_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr2_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr2_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-2 : ℂ)) + r * ((0 : ℂ) + r * (((6 : ℂ)) + r * ((0 : ℂ) + r * (((-6 : ℂ)) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qtr2_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr2_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr2_qt1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr2_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr2_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr2_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr2_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr2_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr2_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ) + (-3 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((10 : ℂ) + (6 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-8 : ℂ) + (-3 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qtr2_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr2_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr2_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-2 : ℂ)) + r * ((0 : ℂ) + r * (((6 : ℂ)) + r * ((0 : ℂ) + r * (((-6 : ℂ)) + r * ((0 : ℂ) + r * ((2 : ℂ))))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qtr2_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr2_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr2_qT2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr2_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qtr2_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qtr2_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qtr2_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt0_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt0_qtr0 s r ((s + 1) * (s + 2)) = (((-3 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-84 : ℂ) + (42 : ℂ) * s + (74 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((240 : ℂ) + (165 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qt0_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt0_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt0_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((4 : ℂ) + (-3 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-24 : ℂ) + (-18 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((36 : ℂ) + (21 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-16 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qt0_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt0_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt0_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((2 : ℂ)) + r * ((0 : ℂ) + r * (((-6 : ℂ)) + r * ((0 : ℂ) + r * (((6 : ℂ)) + r * ((0 : ℂ) + r * ((-2 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qt0_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt0_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt0_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-144 : ℂ) + (120 : ℂ) * s + (216 : ℂ) * s ^ 2 + (48 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((432 : ℂ) + (288 : ℂ) * s)))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qt0_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt0_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt0_qt1 s r ((s + 1) * (s + 2)) = (((-12 : ℂ) * s + (-4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-24 : ℂ) + (-24 : ℂ) * s + (8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((48 : ℂ) + (36 : ℂ) * s + (-4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qt0_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt0_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt0_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((4 : ℂ)) + r * ((0 : ℂ) + r * (((-12 : ℂ)) + r * ((0 : ℂ) + r * (((12 : ℂ)) + r * ((0 : ℂ) + r * ((-4 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qt0_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt0_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt0_qT0 s r ((s + 1) * (s + 2)) = (((-12 : ℂ) * s + (-22 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((280 : ℂ) + (-216 : ℂ) * s + (-442 : ℂ) * s ^ 2 + (-132 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-976 : ℂ) + (-336 : ℂ) * s + (332 : ℂ) * s ^ 2 + (120 : ℂ) * s ^ 3 + (12 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((408 : ℂ) + (252 : ℂ) * s + (-12 : ℂ) * s ^ 2))))))) / (r * (r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qt0_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt0_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt0_qT1 s r ((s + 1) * (s + 2)) = (((-42 : ℂ) * s + (-23 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-200 : ℂ) + (42 : ℂ) * s + (175 : ℂ) * s ^ 2 + (30 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((536 : ℂ) + (360 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-48 : ℂ)))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qt0_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt0_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt0_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((16 : ℂ) + (-6 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-68 : ℂ) + (-36 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((88 : ℂ) + (42 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-36 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qt0_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt0_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt0_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((4 : ℂ)) + r * ((0 : ℂ) + r * (((-12 : ℂ)) + r * ((0 : ℂ) + r * (((12 : ℂ)) + r * ((0 : ℂ) + r * ((-4 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qt0_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt1_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((3 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-60 : ℂ) + (-30 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((48 : ℂ) + (27 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((12 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qt1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt1_qtr1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt1_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt1_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt1_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt1_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt1_qt0 s r ((s + 1) * (s + 2)) = (((12 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-120 : ℂ) + (-72 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((96 : ℂ) + (60 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qt1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt1_qt1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt1_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt1_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt1_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt1_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt1_qT0 s r ((s + 1) * (s + 2)) = (((18 : ℂ) * s + (15 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-240 : ℂ) + (-90 : ℂ) * s + (-7 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((72 : ℂ) + (24 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qt1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt1_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((12 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-120 : ℂ) + (-72 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((96 : ℂ) + (60 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qt1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt1_qT2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt1_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt1_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt1_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt1_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt2_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt2_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-2 : ℂ)) + r * ((0 : ℂ) + r * (((6 : ℂ)) + r * ((0 : ℂ) + r * (((-6 : ℂ)) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qt2_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt2_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt2_qtr1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt2_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt2_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt2_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt2_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt2_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt2_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * (((12 : ℂ)) + r * ((0 : ℂ) + r * (((-12 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qt2_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt2_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt2_qt1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt2_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt2_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt2_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt2_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt2_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt2_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-8 : ℂ) + (-6 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((20 : ℂ) + (12 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-16 : ℂ) + (-6 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((4 : ℂ))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qt2_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt2_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt2_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * (((12 : ℂ)) + r * ((0 : ℂ) + r * (((-12 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ)))))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qt2_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt2_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt2_qT2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt2_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qt2_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qt2_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qt2_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT0_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT0_qtr0 s r ((s + 1) * (s + 2)) = (((-9 : ℂ) * s + (-3 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-172 : ℂ) + (-39 : ℂ) * s + (-1 : ℂ) * s ^ 2 + (-36 : ℂ) * s ^ 3 + (-8 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((436 : ℂ) + (297 : ℂ) * s + (15 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3 + (8 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-276 : ℂ) + (-201 : ℂ) * s + (-11 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT0_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT0_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT0_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-8 : ℂ) + (-3 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((44 : ℂ) + (72 : ℂ) * s + (8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-52 : ℂ) + (-45 : ℂ) * s + (-7 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((16 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT0_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT0_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT0_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ) + (-3 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((10 : ℂ) + (6 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-8 : ℂ) + (-3 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT0_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT0_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT0_qt0 s r ((s + 1) * (s + 2)) = (((-12 : ℂ) * s + (-22 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-296 : ℂ) + (48 : ℂ) * s + (206 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((752 : ℂ) + (384 : ℂ) * s + (-100 : ℂ) * s ^ 2 + (24 : ℂ) * s ^ 3 + (12 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-456 : ℂ) + (-324 : ℂ) * s + (-12 : ℂ) * s ^ 2))))))) / (r * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT0_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT0_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT0_qt1 s r ((s + 1) * (s + 2)) = (((18 : ℂ) * s + (15 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((48 : ℂ) + (102 : ℂ) * s + (-7 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-72 : ℂ) + (-72 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT0_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT0_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT0_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-8 : ℂ) + (-6 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((20 : ℂ) + (12 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-16 : ℂ) + (-6 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((4 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT0_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT0_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT0_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-576 : ℂ) + (48 : ℂ) * s + (432 : ℂ) * s ^ 2 + (96 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((1152 : ℂ) + (552 : ℂ) * s + (-216 : ℂ) * s ^ 2 + (-48 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-432 : ℂ) + (-288 : ℂ) * s)))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT0_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT0_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT0_qT1 s r ((s + 1) * (s + 2)) = (((-78 : ℂ) * s + (-89 : ℂ) * s ^ 2 + (-42 : ℂ) * s ^ 3 + (-7 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-408 : ℂ) + (-180 : ℂ) * s + (154 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((1016 : ℂ) + (774 : ℂ) * s + (-37 : ℂ) * s ^ 2 + (30 : ℂ) * s ^ 3 + (9 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-656 : ℂ) + (-468 : ℂ) * s + (-28 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((48 : ℂ)))))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT0_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT0_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT0_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-32 : ℂ) + (-18 : ℂ) * s + (-6 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((120 : ℂ) + (162 : ℂ) * s + (22 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-124 : ℂ) + (-96 : ℂ) * s + (-16 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((36 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT0_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT0_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT0_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ) + (-6 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((20 : ℂ) + (12 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-16 : ℂ) + (-6 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((4 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT0_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT1_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-9 : ℂ) * s + (-3 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((272 : ℂ) + (156 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-332 : ℂ) + (-219 : ℂ) * s + (-1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT1_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ) + (3 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((24 : ℂ) + (18 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-36 : ℂ) + (-21 : ℂ) * s + (1 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((16 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT1_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT1_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT1_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-2 : ℂ)) + r * ((0 : ℂ) + r * (((6 : ℂ)) + r * ((0 : ℂ) + r * (((-6 : ℂ)) + r * ((0 : ℂ) + r * ((2 : ℂ))))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT1_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT1_qt0 s r ((s + 1) * (s + 2)) = (((-42 : ℂ) * s + (-23 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((520 : ℂ) + (306 : ℂ) * s + (-41 : ℂ) * s ^ 2 + (-18 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-616 : ℂ) + (-408 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-48 : ℂ)))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT1_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((12 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((24 : ℂ) + (24 : ℂ) * s + (-8 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-48 : ℂ) + (-36 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT1_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT1_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT1_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * (((12 : ℂ)) + r * ((0 : ℂ) + r * (((-12 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT1_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT1_qT0 s r ((s + 1) * (s + 2)) = (((78 : ℂ) * s + (89 : ℂ) * s ^ 2 + (42 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-1032 : ℂ) + (-564 : ℂ) * s + (62 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((1720 : ℂ) + (834 : ℂ) * s + (-179 : ℂ) * s ^ 2 + (-78 : ℂ) * s ^ 3 + (-9 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-496 : ℂ) + (-300 : ℂ) * s + (28 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-48 : ℂ)))))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT1_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((576 : ℂ) + (384 : ℂ) * s) + r * ((0 : ℂ) + r * ((-720 : ℂ) + (-480 : ℂ) * s)))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT1_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-16 : ℂ) + (6 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((68 : ℂ) + (36 : ℂ) * s + (-4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-88 : ℂ) + (-42 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((36 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT1_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT1_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT1_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * (((12 : ℂ)) + r * ((0 : ℂ) + r * (((-12 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT1_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT2_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT2_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * (((38 : ℂ) + (24 : ℂ) * s) + r * ((0 : ℂ) + r * (((-28 : ℂ) + (-24 : ℂ) * s) + r * ((0 : ℂ) + r * ((-18 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT2_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT2_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT2_qtr1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT2_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT2_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT2_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT2_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT2_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT2_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((16 : ℂ) + (-6 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((76 : ℂ) + (60 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-56 : ℂ) + (-54 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-36 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT2_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT2_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT2_qt1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT2_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT2_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT2_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT2_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT2_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT2_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((32 : ℂ) + (18 : ℂ) * s + (6 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((168 : ℂ) + (30 : ℂ) * s + (-22 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-20 : ℂ) + (16 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-36 : ℂ))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT2_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT2_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT2_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((16 : ℂ) + (-6 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((76 : ℂ) + (60 : ℂ) * s + (4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-56 : ℂ) + (-54 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-36 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT2_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT2_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT2_qT2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT2_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT2_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT2_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT2_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT3_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT3_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((2 : ℂ)) + r * ((0 : ℂ) + r * (((-6 : ℂ)) + r * ((0 : ℂ) + r * (((6 : ℂ)) + r * ((0 : ℂ) + r * ((-2 : ℂ))))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT3_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT3_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT3_qtr1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT3_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT3_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT3_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT3_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT3_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT3_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((4 : ℂ)) + r * ((0 : ℂ) + r * (((-12 : ℂ)) + r * ((0 : ℂ) + r * (((12 : ℂ)) + r * ((0 : ℂ) + r * ((-4 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewRadQQ_qT3_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT3_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT3_qt1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT3_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT3_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT3_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT3_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT3_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT3_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ) + (6 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-20 : ℂ) + (-12 : ℂ) * s + (-4 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((16 : ℂ) + (6 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-4 : ℂ)))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT3_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT3_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT3_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((4 : ℂ)) + r * ((0 : ℂ) + r * (((-12 : ℂ)) + r * ((0 : ℂ) + r * (((12 : ℂ)) + r * ((0 : ℂ) + r * ((-4 : ℂ))))))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewRadQQ_qT3_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT3_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT3_qT2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT3_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewRadQQ_qT3_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewRadQQ_qT3_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewRadQQ_qT3_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

/-! ## Family against the reflected sources -/

theorem skewRadPieceFS_lauR_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauR_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((-297 / 4 : ℂ) * s ^ 2 + (-1197 / 4 : ℂ) * s ^ 3 + (-6009 / 16 : ℂ) * s ^ 4 + (-471 / 4 : ℂ) * s ^ 5 + (399 / 4 : ℂ) * s ^ 6 + (723 / 8 : ℂ) * s ^ 7 + (417 / 16 : ℂ) * s ^ 8 + (21 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1161 : ℂ) * s + (-5559 / 4 : ℂ) * s ^ 2 + (2581 / 4 : ℂ) * s ^ 3 + (8047 / 16 : ℂ) * s ^ 4 + (-19751 / 8 : ℂ) * s ^ 5 + (-13025 / 4 : ℂ) * s ^ 6 + (-13383 / 8 : ℂ) * s ^ 7 + (-6647 / 16 : ℂ) * s ^ 8 + (-93 / 2 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-2991 : ℂ) * s + (22615 / 2 : ℂ) * s ^ 2 + (13253 : ℂ) * s ^ 3 + (-46691 / 16 : ℂ) * s ^ 4 + (-18825 / 2 : ℂ) * s ^ 5 + (-19081 / 4 : ℂ) * s ^ 6 + (-7003 / 8 : ℂ) * s ^ 7 + (247 / 16 : ℂ) * s ^ 8 + (175 / 8 : ℂ) * s ^ 9 + (3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((12018 : ℂ) * s + (33197 / 2 : ℂ) * s ^ 2 + (-2455 : ℂ) * s ^ 3 + (-161867 / 16 : ℂ) * s ^ 4 + (-32331 / 8 : ℂ) * s ^ 5 + (-347 / 4 : ℂ) * s ^ 6 + (2291 / 8 : ℂ) * s ^ 7 + (1039 / 16 : ℂ) * s ^ 8 + (4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-6498 : ℂ) * s + (-63381 / 4 : ℂ) * s ^ 2 + (-57875 / 4 : ℂ) * s ^ 3 + (-22725 / 4 : ℂ) * s ^ 4 + (-4263 / 4 : ℂ) * s ^ 5 + (-203 / 2 : ℂ) * s ^ 6 + (-7 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1449 : ℂ) * s + (-5667 / 4 : ℂ) * s ^ 2 + (-1497 / 4 : ℂ) * s ^ 3 + (-45 / 4 : ℂ) * s ^ 4 + (13 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((81 : ℂ) * s + (36 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauR_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauR_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauR_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((54 : ℂ) * s + (873 / 4 : ℂ) * s ^ 2 + (1293 / 4 : ℂ) * s ^ 3 + (5193 / 16 : ℂ) * s ^ 4 + (2991 / 8 : ℂ) * s ^ 5 + (1443 / 4 : ℂ) * s ^ 6 + (1677 / 8 : ℂ) * s ^ 7 + (1083 / 16 : ℂ) * s ^ 8 + (45 / 4 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((909 : ℂ) * s + (1017 / 4 : ℂ) * s ^ 2 + (-5969 / 4 : ℂ) * s ^ 3 + (-8193 / 16 : ℂ) * s ^ 4 + (13517 / 8 : ℂ) * s ^ 5 + (7625 / 4 : ℂ) * s ^ 6 + (6727 / 8 : ℂ) * s ^ 7 + (2629 / 16 : ℂ) * s ^ 8 + (35 / 4 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-4632 : ℂ) * s + (-33013 / 2 : ℂ) * s ^ 2 + (-53001 / 4 : ℂ) * s ^ 3 + (24119 / 16 : ℂ) * s ^ 4 + (56303 / 8 : ℂ) * s ^ 5 + (15301 / 4 : ℂ) * s ^ 6 + (6931 / 8 : ℂ) * s ^ 7 + (1053 / 16 : ℂ) * s ^ 8 + (-2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1182 : ℂ) * s + (1825 / 2 : ℂ) * s ^ 2 + (13076 : ℂ) * s ^ 3 + (235053 / 16 : ℂ) * s ^ 4 + (57227 / 8 : ℂ) * s ^ 5 + (3683 / 2 : ℂ) * s ^ 6 + (1925 / 8 : ℂ) * s ^ 7 + (179 / 16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((7422 : ℂ) * s + (37097 / 4 : ℂ) * s ^ 2 + (13259 / 2 : ℂ) * s ^ 3 + (5889 / 2 : ℂ) * s ^ 4 + (883 : ℂ) * s ^ 5 + (725 / 4 : ℂ) * s ^ 6 + (35 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2247 : ℂ) * s + (-12899 / 4 : ℂ) * s ^ 2 + (-6313 / 4 : ℂ) * s ^ 3 + (-1421 / 4 : ℂ) * s ^ 4 + (-139 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-324 : ℂ) * s + (-144 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauR_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauR_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauR_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((54 : ℂ) * s ^ 2 + (477 / 2 : ℂ) * s ^ 3 + (384 : ℂ) * s ^ 4 + (2529 / 8 : ℂ) * s ^ 5 + (351 / 2 : ℂ) * s ^ 6 + (171 / 2 : ℂ) * s ^ 7 + (135 / 4 : ℂ) * s ^ 8 + (63 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1476 : ℂ) * s + (4626 : ℂ) * s ^ 2 + (11519 / 2 : ℂ) * s ^ 3 + (15751 / 4 : ℂ) * s ^ 4 + (7893 / 4 : ℂ) * s ^ 5 + (912 : ℂ) * s ^ 6 + (1291 / 4 : ℂ) * s ^ 7 + (57 : ℂ) * s ^ 8 + (1 / 2 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((5910 : ℂ) * s + (6797 : ℂ) * s ^ 2 + (2699 / 2 : ℂ) * s ^ 3 + (-781 : ℂ) * s ^ 4 + (-2221 / 8 : ℂ) * s ^ 5 + (-627 / 4 : ℂ) * s ^ 6 + (-347 / 2 : ℂ) * s ^ 7 + (-269 / 4 : ℂ) * s ^ 8 + (-67 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-6012 : ℂ) * s + (-14547 : ℂ) * s ^ 2 + (-22165 / 2 : ℂ) * s ^ 3 + (-18667 / 4 : ℂ) * s ^ 4 + (-7751 / 4 : ℂ) * s ^ 5 + (-3323 / 4 : ℂ) * s ^ 6 + (-879 / 4 : ℂ) * s ^ 7 + (-47 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-3768 : ℂ) * s + (-23 : ℂ) * s ^ 2 + (2340 : ℂ) * s ^ 3 + (835 : ℂ) * s ^ 4 + (-101 : ℂ) * s ^ 5 + (-100 : ℂ) * s ^ 6 + (-15 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((2232 : ℂ) * s + (3021 : ℂ) * s ^ 2 + (1389 : ℂ) * s ^ 3 + (291 : ℂ) * s ^ 4 + (27 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((162 : ℂ) * s + (72 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauR_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauR_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauR_qt0 s r ((s + 1) * (s + 2)) * ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((-54 : ℂ) * s ^ 2 + (-306 : ℂ) * s ^ 3 + (-1365 / 4 : ℂ) * s ^ 4 + (-507 / 4 : ℂ) * s ^ 5 + (-231 / 16 : ℂ) * s ^ 6 + (-21 / 2 : ℂ) * s ^ 7 + (-69 / 8 : ℂ) * s ^ 8 + (-9 / 4 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-999 : ℂ) * s + (732 : ℂ) * s ^ 2 + (5501 / 2 : ℂ) * s ^ 3 + (1691 / 4 : ℂ) * s ^ 4 + (-33675 / 16 : ℂ) * s ^ 5 + (-6939 / 4 : ℂ) * s ^ 6 + (-1131 / 2 : ℂ) * s ^ 7 + (-611 / 8 : ℂ) * s ^ 8 + (-21 / 16 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((3426 : ℂ) * s + (7349 / 2 : ℂ) * s ^ 2 + (-921 : ℂ) * s ^ 3 + (-12205 / 8 : ℂ) * s ^ 4 + (2163 / 2 : ℂ) * s ^ 5 + (25519 / 16 : ℂ) * s ^ 6 + (5125 / 8 : ℂ) * s ^ 7 + (835 / 8 : ℂ) * s ^ 8 + (39 / 8 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-3758 : ℂ) * s + (-14757 / 2 : ℂ) * s ^ 2 + (-9837 / 2 : ℂ) * s ^ 3 + (-735 / 2 : ℂ) * s ^ 4 + (12109 / 16 : ℂ) * s ^ 5 + (1043 / 8 : ℂ) * s ^ 6 + (-64 : ℂ) * s ^ 7 + (-155 / 8 : ℂ) * s ^ 8 + (-21 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1348 : ℂ) * s + (5373 / 2 : ℂ) * s ^ 2 + (3083 : ℂ) * s ^ 3 + (14273 / 8 : ℂ) * s ^ 4 + (3161 / 8 : ℂ) * s ^ 5 + (191 / 8 : ℂ) * s ^ 6 + (-5 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-131 : ℂ) * s + (529 / 2 : ℂ) * s ^ 2 + (309 : ℂ) * s ^ 3 + (55 / 2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((114 : ℂ) * s + (75 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauR_qt0_lam s r hs hs3 hs1, ssSourceT_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauR_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauR_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((-243 / 2 : ℂ) * s ^ 2 + (-1053 / 4 : ℂ) * s ^ 3 + (-1215 / 8 : ℂ) * s ^ 4 + (549 / 16 : ℂ) * s ^ 5 + (969 / 16 : ℂ) * s ^ 6 + (117 / 8 : ℂ) * s ^ 7 + (-3 : ℂ) * s ^ 8 + (-27 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-324 : ℂ) * s + (-1377 : ℂ) * s ^ 2 + (-1368 : ℂ) * s ^ 3 + (543 / 4 : ℂ) * s ^ 4 + (3601 / 4 : ℂ) * s ^ 5 + (4253 / 8 : ℂ) * s ^ 6 + (539 / 4 : ℂ) * s ^ 7 + (77 / 4 : ℂ) * s ^ 8 + (3 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((90 : ℂ) * s + (894 : ℂ) * s ^ 2 + (5007 / 2 : ℂ) * s ^ 3 + (17497 / 8 : ℂ) * s ^ 4 + (8305 / 16 : ℂ) * s ^ 5 + (-2711 / 16 : ℂ) * s ^ 6 + (-733 / 8 : ℂ) * s ^ 7 + (-23 / 2 : ℂ) * s ^ 8 + (-15 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1044 : ℂ) * s + (2157 : ℂ) * s ^ 2 + (609 : ℂ) * s ^ 3 + (-1423 : ℂ) * s ^ 4 + (-9905 / 8 : ℂ) * s ^ 5 + (-1541 / 4 : ℂ) * s ^ 6 + (-109 / 2 : ℂ) * s ^ 7 + (-19 / 4 : ℂ) * s ^ 8 + (-3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1008 : ℂ) * s + (-3993 / 2 : ℂ) * s ^ 2 + (-7113 / 4 : ℂ) * s ^ 3 + (-826 : ℂ) * s ^ 4 + (-445 / 2 : ℂ) * s ^ 5 + (-75 / 2 : ℂ) * s ^ 6 + (-13 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((144 : ℂ) * s + (408 : ℂ) * s ^ 2 + (291 : ℂ) * s ^ 3 + (78 : ℂ) * s ^ 4 + (7 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((54 : ℂ) * s + (36 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauR_qt1_lam s r hs hs3 hs1, ssSourceT1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauR_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauR_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((54 : ℂ) * s + (477 / 2 : ℂ) * s ^ 2 + (384 : ℂ) * s ^ 3 + (2529 / 8 : ℂ) * s ^ 4 + (351 / 2 : ℂ) * s ^ 5 + (171 / 2 : ℂ) * s ^ 6 + (135 / 4 : ℂ) * s ^ 7 + (63 / 8 : ℂ) * s ^ 8 + (3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((603 : ℂ) * s + (2133 / 2 : ℂ) * s ^ 2 + (2111 / 4 : ℂ) * s ^ 3 + (305 / 8 : ℂ) * s ^ 4 + (-9 / 4 : ℂ) * s ^ 5 + (-10 : ℂ) * s ^ 6 + (-26 : ℂ) * s ^ 7 + (-93 / 8 : ℂ) * s ^ 8 + (-3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1047 : ℂ) * s + (-2842 : ℂ) * s ^ 2 + (-10233 / 4 : ℂ) * s ^ 3 + (-9313 / 8 : ℂ) * s ^ 4 + (-480 : ℂ) * s ^ 5 + (-415 / 2 : ℂ) * s ^ 6 + (-91 / 2 : ℂ) * s ^ 7 + (-3 / 8 : ℂ) * s ^ 8 + (3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-222 : ℂ) * s + (1000 : ℂ) * s ^ 2 + (6733 / 4 : ℂ) * s ^ 3 + (6999 / 8 : ℂ) * s ^ 4 + (1035 / 4 : ℂ) * s ^ 5 + (103 : ℂ) * s ^ 6 + (34 : ℂ) * s ^ 7 + (33 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((876 : ℂ) * s + (2099 / 2 : ℂ) * s ^ 2 + (1097 / 4 : ℂ) * s ^ 3 + (19 / 2 : ℂ) * s ^ 4 + (54 : ℂ) * s ^ 5 + (29 : ℂ) * s ^ 6 + (15 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-237 : ℂ) * s + (-989 / 2 : ℂ) * s ^ 2 + (-308 : ℂ) * s ^ 3 + (-149 / 2 : ℂ) * s ^ 4 + (-6 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-27 : ℂ) * s + (-18 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauR_qt2_lam s r hs hs3 hs1, ssSourceT2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauR_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauR_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((-12 : ℂ) * s + (-178 : ℂ) * s ^ 2 + (-286 : ℂ) * s ^ 3 + (-383 / 2 : ℂ) * s ^ 4 + (-229 / 4 : ℂ) * s ^ 5 + (-1 / 4 : ℂ) * s ^ 6 + (17 / 4 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-864 : ℂ) + (858 : ℂ) * s + (2161 : ℂ) * s ^ 2 + (-131 / 2 : ℂ) * s ^ 3 + (-6335 / 4 : ℂ) * s ^ 4 + (-4195 / 4 : ℂ) * s ^ 5 + (-1239 / 4 : ℂ) * s ^ 6 + (-191 / 4 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3456 : ℂ) + (486 : ℂ) * s + (-1785 : ℂ) * s ^ 2 + (-59 : ℂ) * s ^ 3 + (1285 : ℂ) * s ^ 4 + (3821 / 4 : ℂ) * s ^ 5 + (1197 / 4 : ℂ) * s ^ 6 + (175 / 4 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-4968 : ℂ) + (-3462 : ℂ) * s + (-47 : ℂ) * s ^ 2 + (-215 / 2 : ℂ) * s ^ 3 + (-879 / 4 : ℂ) * s ^ 4 + (-313 / 4 : ℂ) * s ^ 5 + (-53 / 4 : ℂ) * s ^ 6 + (-1 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((3024 : ℂ) + (2742 : ℂ) * s + (413 : ℂ) * s ^ 2 + (50 : ℂ) * s ^ 3 + (38 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-648 : ℂ) + (-612 : ℂ) * s + (-132 : ℂ) * s ^ 2))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauR_qT0_lam s r hs hs3 hs1, ssSourceTF_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauR_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauR_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((-246 : ℂ) * s + (-715 : ℂ) * s ^ 2 + (-1373 / 2 : ℂ) * s ^ 3 + (-637 / 4 : ℂ) * s ^ 4 + (125 : ℂ) * s ^ 5 + (163 / 2 : ℂ) * s ^ 6 + (31 / 2 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1224 : ℂ) + (-1116 : ℂ) * s + (1414 : ℂ) * s ^ 2 + (1099 : ℂ) * s ^ 3 + (-1344 : ℂ) * s ^ 4 + (-3451 / 2 : ℂ) * s ^ 5 + (-1381 / 2 : ℂ) * s ^ 6 + (-211 / 2 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3048 : ℂ) + (6692 : ℂ) * s + (6638 : ℂ) * s ^ 2 + (2207 / 2 : ℂ) * s ^ 3 + (-9065 / 4 : ℂ) * s ^ 4 + (-1192 : ℂ) * s ^ 5 + (-157 / 2 : ℂ) * s ^ 6 + (73 / 2 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-744 : ℂ) + (-3920 : ℂ) * s + (-3720 : ℂ) * s ^ 2 + (-3019 : ℂ) * s ^ 3 + (-3039 / 2 : ℂ) * s ^ 4 + (-245 / 2 : ℂ) * s ^ 5 + (127 / 2 : ℂ) * s ^ 6 + (11 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2904 : ℂ) + (-3206 : ℂ) * s + (-1145 : ℂ) * s ^ 2 + (-961 : ℂ) * s ^ 3 + (-351 : ℂ) * s ^ 4 + (-25 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1968 : ℂ) + (1844 : ℂ) * s + (552 : ℂ) * s ^ 2 + (52 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-144 : ℂ) + (-48 : ℂ) * s))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauR_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauR_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauR_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((96 : ℂ) + (374 : ℂ) * s + (504 : ℂ) * s ^ 2 + (803 / 2 : ℂ) * s ^ 3 + (709 / 2 : ℂ) * s ^ 4 + (557 / 2 : ℂ) * s ^ 5 + (247 / 2 : ℂ) * s ^ 6 + (26 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((312 : ℂ) + (-172 : ℂ) * s + (-1652 : ℂ) * s ^ 2 + (-940 : ℂ) * s ^ 3 + (880 : ℂ) * s ^ 4 + (997 : ℂ) * s ^ 5 + (312 : ℂ) * s ^ 6 + (25 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-2628 : ℂ) + (-6156 : ℂ) * s + (-5693 : ℂ) * s ^ 2 + (471 / 2 : ℂ) * s ^ 3 + (5837 / 2 : ℂ) * s ^ 4 + (2727 / 2 : ℂ) * s ^ 5 + (357 / 2 : ℂ) * s ^ 6 + (-3 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((4008 : ℂ) + (7648 : ℂ) * s + (5140 : ℂ) * s ^ 2 + (3583 : ℂ) * s ^ 3 + (2018 : ℂ) * s ^ 4 + (489 : ℂ) * s ^ 5 + (34 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-1536 : ℂ) + (-1070 : ℂ) * s + (-1161 : ℂ) * s ^ 2 + (-262 : ℂ) * s ^ 3 + (141 : ℂ) * s ^ 4 + (40 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-576 : ℂ) + (-732 : ℂ) * s + (-594 : ℂ) * s ^ 2 + (-138 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((324 : ℂ) + (108 : ℂ) * s))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauR_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauR_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauR_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((48 : ℂ) * s + (196 : ℂ) * s ^ 2 + (276 : ℂ) * s ^ 3 + (189 : ℂ) * s ^ 4 + (93 : ℂ) * s ^ 5 + (45 : ℂ) * s ^ 6 + (15 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((576 : ℂ) + (2088 : ℂ) * s + (2636 : ℂ) * s ^ 2 + (1568 : ℂ) * s ^ 3 + (690 : ℂ) * s ^ 4 + (346 : ℂ) * s ^ 5 + (108 : ℂ) * s ^ 6 + (6 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((96 : ℂ) * s + (-1360 : ℂ) * s ^ 2 + (-1478 : ℂ) * s ^ 3 + (-449 : ℂ) * s ^ 4 + (-145 : ℂ) * s ^ 5 + (-99 : ℂ) * s ^ 6 + (-21 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2160 : ℂ) + (-3840 : ℂ) * s + (-3200 : ℂ) * s ^ 2 + (-1164 : ℂ) * s ^ 3 + (-454 : ℂ) * s ^ 4 + (-264 : ℂ) * s ^ 5 + (-54 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((1872 : ℂ) + (1632 : ℂ) * s + (1452 : ℂ) * s ^ 2 + (714 : ℂ) * s ^ 3 + (24 : ℂ) * s ^ 4 + (-30 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-144 : ℂ) + (24 : ℂ) * s + (276 : ℂ) * s ^ 2 + (84 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-144 : ℂ) + (-48 : ℂ) * s))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauR_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewRadFSrcLam_lauR (s r : ℂ) : ℂ := (((96 : ℂ) + (272 : ℂ) * s + (68 : ℂ) * s ^ 2 + (-871 / 4 : ℂ) * s ^ 3 + (1395 / 4 : ℂ) * s ^ 4 + (17513 / 16 : ℂ) * s ^ 5 + (8139 / 8 : ℂ) * s ^ 6 + (3873 / 8 : ℂ) * s ^ 7 + (517 / 4 : ℂ) * s ^ 8 + (297 / 16 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-1200 : ℂ) + (2162 : ℂ) * s + (8471 : ℂ) * s ^ 2 + (33937 / 4 : ℂ) * s ^ 3 + (6335 / 2 : ℂ) * s ^ 4 + (-23103 / 16 : ℂ) * s ^ 5 + (-17851 / 8 : ℂ) * s ^ 6 + (-4353 / 4 : ℂ) * s ^ 7 + (-2191 / 8 : ℂ) * s ^ 8 + (-593 / 16 : ℂ) * s ^ 9 + (-9 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((3876 : ℂ) + (1874 : ℂ) * s + (2249 / 2 : ℂ) * s ^ 2 + (357 / 2 : ℂ) * s ^ 3 + (-9649 / 8 : ℂ) * s ^ 4 + (-8799 / 16 : ℂ) * s ^ 5 + (833 / 2 : ℂ) * s ^ 6 + (1509 / 4 : ℂ) * s ^ 7 + (112 : ℂ) * s ^ 8 + (259 / 16 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-3864 : ℂ) + (-1686 : ℂ) * s + (-6169 / 2 : ℂ) * s ^ 2 + (-15181 / 4 : ℂ) * s ^ 3 + (-2367 / 2 : ℂ) * s ^ 4 + (15615 / 16 : ℂ) * s ^ 5 + (6419 / 8 : ℂ) * s ^ 6 + (228 : ℂ) * s ^ 7 + (261 / 8 : ℂ) * s ^ 8 + (37 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((456 : ℂ) + (-1530 : ℂ) * s + (-10591 / 2 : ℂ) * s ^ 2 + (-17517 / 4 : ℂ) * s ^ 3 + (-8657 / 8 : ℂ) * s ^ 4 + (-569 / 8 : ℂ) * s ^ 5 + (-39 / 8 : ℂ) * s ^ 6 + (-9 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((600 : ℂ) + (-1164 : ℂ) * s + (-2681 / 2 : ℂ) * s ^ 2 + (-547 / 2 : ℂ) * s ^ 3 + (-89 / 2 : ℂ) * s ^ 4 + (-11 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((36 : ℂ) + (72 : ℂ) * s + (57 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2)

theorem skewRadFSrc_lauR_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFSrc_lauR s r ((s + 1) * (s + 2)) (ssSourceTR (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2))) = skewRadFSrcLam_lauR s r := by
  unfold skewRadFSrc_lauR
  rw [skewRadPieceFS_lauR_qtr0 s r hr hf hs hs3 hs1, skewRadPieceFS_lauR_qtr1 s r hr hf hs hs3 hs1, skewRadPieceFS_lauR_qtr2 s r hr hf hs hs3 hs1, skewRadPieceFS_lauR_qt0 s r hr hf hs hs3 hs1, skewRadPieceFS_lauR_qt1 s r hr hf hs hs3 hs1, skewRadPieceFS_lauR_qt2 s r hr hf hs hs3 hs1, skewRadPieceFS_lauR_qT0 s r hr hf hs hs3 hs1, skewRadPieceFS_lauR_qT1 s r hr hf hs hs3 hs1, skewRadPieceFS_lauR_qT2 s r hr hf hs hs3 hs1, skewRadPieceFS_lauR_qT3 s r hr hf hs hs3 hs1]
  unfold skewRadFSrcLam_lauR
  all_goals (try simp only [← add_div])
  ring

theorem skewRadPieceFS_lauI1_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI1_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((405 / 4 : ℂ) * s ^ 2 + (1917 / 4 : ℂ) * s ^ 3 + (14805 / 16 : ℂ) * s ^ 4 + (948 : ℂ) * s ^ 5 + (2235 / 4 : ℂ) * s ^ 6 + (1521 / 8 : ℂ) * s ^ 7 + (555 / 16 : ℂ) * s ^ 8 + (21 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2817 / 4 : ℂ) * s ^ 2 + (-8505 / 2 : ℂ) * s ^ 3 + (-151307 / 16 : ℂ) * s ^ 4 + (-83883 / 8 : ℂ) * s ^ 5 + (-13001 / 2 : ℂ) * s ^ 6 + (-18653 / 8 : ℂ) * s ^ 7 + (-7505 / 16 : ℂ) * s ^ 8 + (-93 / 2 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-594 : ℂ) * s + (-12201 / 2 : ℂ) * s ^ 2 + (-73999 / 4 : ℂ) * s ^ 3 + (-353837 / 16 : ℂ) * s ^ 4 + (-13255 : ℂ) * s ^ 5 + (-4107 : ℂ) * s ^ 6 + (-3881 / 8 : ℂ) * s ^ 7 + (973 / 16 : ℂ) * s ^ 8 + (175 / 8 : ℂ) * s ^ 9 + (3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-2280 : ℂ) * s + (12097 / 2 : ℂ) * s ^ 2 + (44361 / 4 : ℂ) * s ^ 3 + (148087 / 16 : ℂ) * s ^ 4 + (41229 / 8 : ℂ) * s ^ 5 + (3823 / 2 : ℂ) * s ^ 6 + (3649 / 8 : ℂ) * s ^ 7 + (1033 / 16 : ℂ) * s ^ 8 + (4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((3108 : ℂ) * s + (39469 / 4 : ℂ) * s ^ 2 + (15459 / 2 : ℂ) * s ^ 3 + (5853 / 2 : ℂ) * s ^ 4 + (551 : ℂ) * s ^ 5 + (89 / 4 : ℂ) * s ^ 6 + (-9 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-72 : ℂ) * s + (303 / 4 : ℂ) * s ^ 2 + (-947 / 4 : ℂ) * s ^ 3 + (-543 / 4 : ℂ) * s ^ 4 + (-61 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-162 : ℂ) * s + (-72 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI1_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI1_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI1_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((27 / 4 : ℂ) * s ^ 2 + (369 / 4 : ℂ) * s ^ 3 + (5619 / 16 : ℂ) * s ^ 4 + (4767 / 8 : ℂ) * s ^ 5 + (2139 / 4 : ℂ) * s ^ 6 + (2175 / 8 : ℂ) * s ^ 7 + (1257 / 16 : ℂ) * s ^ 8 + (12 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((27 : ℂ) * s + (1215 / 4 : ℂ) * s ^ 2 + (8913 / 4 : ℂ) * s ^ 3 + (77561 / 16 : ℂ) * s ^ 4 + (40987 / 8 : ℂ) * s ^ 5 + (12097 / 4 : ℂ) * s ^ 6 + (8017 / 8 : ℂ) * s ^ 7 + (2643 / 16 : ℂ) * s ^ 8 + (29 / 4 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((468 : ℂ) * s + (2577 / 2 : ℂ) * s ^ 2 + (28471 / 4 : ℂ) * s ^ 3 + (186533 / 16 : ℂ) * s ^ 4 + (69787 / 8 : ℂ) * s ^ 5 + (13695 / 4 : ℂ) * s ^ 6 + (5441 / 8 : ℂ) * s ^ 7 + (791 / 16 : ℂ) * s ^ 8 + (-5 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2082 : ℂ) * s + (-17117 / 2 : ℂ) * s ^ 2 + (-5017 : ℂ) * s ^ 3 + (12643 / 16 : ℂ) * s ^ 4 + (15653 / 8 : ℂ) * s ^ 5 + (1857 / 2 : ℂ) * s ^ 6 + (1587 / 8 : ℂ) * s ^ 7 + (253 / 16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1632 : ℂ) * s + (-22357 / 4 : ℂ) * s ^ 2 + (-5039 / 2 : ℂ) * s ^ 3 + (931 / 2 : ℂ) * s ^ 4 + (657 : ℂ) * s ^ 5 + (815 / 4 : ℂ) * s ^ 6 + (45 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((2895 : ℂ) * s + (12755 / 4 : ℂ) * s ^ 2 + (7129 / 4 : ℂ) * s ^ 3 + (1949 / 4 : ℂ) * s ^ 4 + (187 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((324 : ℂ) * s + (144 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI1_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI1_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI1_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((-27 / 2 : ℂ) * s ^ 3 + (-99 / 2 : ℂ) * s ^ 4 + (-363 / 8 : ℂ) * s ^ 5 + (18 : ℂ) * s ^ 6 + (51 : ℂ) * s ^ 7 + (123 / 4 : ℂ) * s ^ 8 + (63 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-342 : ℂ) * s ^ 2 + (-1521 / 2 : ℂ) * s ^ 3 + (-883 / 4 : ℂ) * s ^ 4 + (2903 / 4 : ℂ) * s ^ 5 + (1649 / 2 : ℂ) * s ^ 6 + (1433 / 4 : ℂ) * s ^ 7 + (63 : ℂ) * s ^ 8 + (1 / 2 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((738 : ℂ) * s + (849 : ℂ) * s ^ 2 + (4611 / 2 : ℂ) * s ^ 3 + (7169 / 2 : ℂ) * s ^ 4 + (17615 / 8 : ℂ) * s ^ 5 + (1587 / 4 : ℂ) * s ^ 6 + (-141 : ℂ) * s ^ 7 + (-281 / 4 : ℂ) * s ^ 8 + (-67 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((3324 : ℂ) * s + (6157 : ℂ) * s ^ 2 + (9339 / 2 : ℂ) * s ^ 3 + (655 / 4 : ℂ) * s ^ 4 + (-7073 / 4 : ℂ) * s ^ 5 + (-4181 / 4 : ℂ) * s ^ 6 + (-1013 / 4 : ℂ) * s ^ 7 + (-47 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1344 : ℂ) * s + (-3589 : ℂ) * s ^ 2 + (-4704 : ℂ) * s ^ 3 + (-3121 : ℂ) * s ^ 4 + (-1081 : ℂ) * s ^ 5 + (-194 : ℂ) * s ^ 6 + (-15 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2556 : ℂ) * s + (-3003 : ℂ) * s ^ 2 + (-1491 : ℂ) * s ^ 3 + (-357 : ℂ) * s ^ 4 + (-33 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-162 : ℂ) * s + (-72 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI1_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI1_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI1_qt0 s r ((s + 1) * (s + 2)) * ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((81 : ℂ) * s ^ 2 + (1269 / 4 : ℂ) * s ^ 3 + (1899 / 4 : ℂ) * s ^ 4 + (5373 / 16 : ℂ) * s ^ 5 + (1641 / 16 : ℂ) * s ^ 6 + (-21 / 8 : ℂ) * s ^ 7 + (-81 / 8 : ℂ) * s ^ 8 + (-39 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-2547 / 2 : ℂ) * s ^ 2 + (-21165 / 4 : ℂ) * s ^ 3 + (-65667 / 8 : ℂ) * s ^ 4 + (-25901 / 4 : ℂ) * s ^ 5 + (-22741 / 8 : ℂ) * s ^ 6 + (-2737 / 4 : ℂ) * s ^ 7 + (-611 / 8 : ℂ) * s ^ 8 + (-3 / 4 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-513 : ℂ) * s + (4119 / 2 : ℂ) * s ^ 2 + (15763 / 2 : ℂ) * s ^ 3 + (42591 / 4 : ℂ) * s ^ 4 + (125537 / 16 : ℂ) * s ^ 5 + (54625 / 16 : ℂ) * s ^ 6 + (6841 / 8 : ℂ) * s ^ 7 + (871 / 8 : ℂ) * s ^ 8 + (69 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1050 : ℂ) * s + (1461 / 2 : ℂ) * s ^ 2 + (-1279 : ℂ) * s ^ 3 + (-17055 / 8 : ℂ) * s ^ 4 + (-12061 / 8 : ℂ) * s ^ 5 + (-2609 / 4 : ℂ) * s ^ 6 + (-673 / 4 : ℂ) * s ^ 7 + (-179 / 8 : ℂ) * s ^ 8 + (-9 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-590 : ℂ) * s + (-2889 / 2 : ℂ) * s ^ 2 + (-6195 / 4 : ℂ) * s ^ 3 + (-3051 / 4 : ℂ) * s ^ 4 + (-801 / 4 : ℂ) * s ^ 5 + (-87 / 4 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((88 : ℂ) * s + (-123 : ℂ) * s ^ 2 + (-347 / 4 : ℂ) * s ^ 3 + (-39 / 2 : ℂ) * s ^ 4 + (5 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-41 : ℂ) * s + (-30 : ℂ) * s ^ 2 + (7 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((6 : ℂ) * s))))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI1_qt0_lam s r hs hs3 hs1, ssSourceT_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI1_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI1_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((81 / 2 : ℂ) * s ^ 2 + (891 / 4 : ℂ) * s ^ 3 + (3429 / 8 : ℂ) * s ^ 4 + (6261 / 16 : ℂ) * s ^ 5 + (2889 / 16 : ℂ) * s ^ 6 + (285 / 8 : ℂ) * s ^ 7 + (-3 / 2 : ℂ) * s ^ 8 + (-27 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((9 : ℂ) * s ^ 2 + (501 : ℂ) * s ^ 3 + (4537 / 4 : ℂ) * s ^ 4 + (3973 / 4 : ℂ) * s ^ 5 + (3357 / 8 : ℂ) * s ^ 6 + (371 / 4 : ℂ) * s ^ 7 + (59 / 4 : ℂ) * s ^ 8 + (3 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-162 : ℂ) * s + (-882 : ℂ) * s ^ 2 + (-2151 / 2 : ℂ) * s ^ 3 + (-6875 / 8 : ℂ) * s ^ 4 + (-10431 / 16 : ℂ) * s ^ 5 + (-5111 / 16 : ℂ) * s ^ 6 + (-589 / 8 : ℂ) * s ^ 7 + (-7 : ℂ) * s ^ 8 + (-15 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-36 : ℂ) * s + (-75 : ℂ) * s ^ 2 + (-420 : ℂ) * s ^ 3 + (-1667 / 2 : ℂ) * s ^ 4 + (-4985 / 8 : ℂ) * s ^ 5 + (-917 / 4 : ℂ) * s ^ 6 + (-97 / 2 : ℂ) * s ^ 7 + (-25 / 4 : ℂ) * s ^ 8 + (-3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((504 : ℂ) * s + (2739 / 2 : ℂ) * s ^ 2 + (4395 / 4 : ℂ) * s ^ 3 + (238 : ℂ) * s ^ 4 + (-193 / 2 : ℂ) * s ^ 5 + (-103 / 2 : ℂ) * s ^ 6 + (-25 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-252 : ℂ) * s + (-426 : ℂ) * s ^ 2 + (-321 : ℂ) * s ^ 3 + (-108 : ℂ) * s ^ 4 + (-13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-54 : ℂ) * s + (-36 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI1_qt1_lam s r hs hs3 hs1, ssSourceT1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI1_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI1_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((-27 / 2 : ℂ) * s ^ 2 + (-99 / 2 : ℂ) * s ^ 3 + (-363 / 8 : ℂ) * s ^ 4 + (18 : ℂ) * s ^ 5 + (51 : ℂ) * s ^ 6 + (123 / 4 : ℂ) * s ^ 7 + (63 / 8 : ℂ) * s ^ 8 + (3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((27 : ℂ) * s + (-63 / 2 : ℂ) * s ^ 2 + (147 / 4 : ℂ) * s ^ 3 + (2297 / 8 : ℂ) * s ^ 4 + (1127 / 4 : ℂ) * s ^ 5 + (77 : ℂ) * s ^ 6 + (-17 : ℂ) * s ^ 7 + (-93 / 8 : ℂ) * s ^ 8 + (-3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((315 : ℂ) * s + (858 : ℂ) * s ^ 2 + (3467 / 4 : ℂ) * s ^ 3 + (751 / 8 : ℂ) * s ^ 4 + (-402 : ℂ) * s ^ 5 + (-523 / 2 : ℂ) * s ^ 6 + (-109 / 2 : ℂ) * s ^ 7 + (-3 / 8 : ℂ) * s ^ 8 + (3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-366 : ℂ) * s + (-1028 : ℂ) * s ^ 2 + (-5267 / 4 : ℂ) * s ^ 3 + (-6225 / 8 : ℂ) * s ^ 4 + (-417 / 4 : ℂ) * s ^ 5 + (88 : ℂ) * s ^ 6 + (37 : ℂ) * s ^ 7 + (33 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-294 : ℂ) * s + (-613 / 2 : ℂ) * s ^ 2 + (547 / 4 : ℂ) * s ^ 3 + (353 : ℂ) * s ^ 4 + (395 / 2 : ℂ) * s ^ 5 + (91 / 2 : ℂ) * s ^ 6 + (15 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((291 : ℂ) * s + (1007 / 2 : ℂ) * s ^ 2 + (323 : ℂ) * s ^ 3 + (179 / 2 : ℂ) * s ^ 4 + (9 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((27 : ℂ) * s + (18 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI1_qt2_lam s r hs hs3 hs1, ssSourceT2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI1_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI1_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((72 : ℂ) * s + (267 : ℂ) * s ^ 2 + (405 : ℂ) * s ^ 3 + (1323 / 4 : ℂ) * s ^ 4 + (162 : ℂ) * s ^ 5 + (99 / 2 : ℂ) * s ^ 6 + (9 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1146 : ℂ) * s + (-4315 : ℂ) * s ^ 2 + (-12297 / 2 : ℂ) * s ^ 3 + (-9003 / 2 : ℂ) * s ^ 4 + (-3753 / 2 : ℂ) * s ^ 5 + (-453 : ℂ) * s ^ 6 + (-60 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-444 : ℂ) + (2594 : ℂ) * s + (7982 : ℂ) * s ^ 2 + (8632 : ℂ) * s ^ 3 + (20611 / 4 : ℂ) * s ^ 4 + (1918 : ℂ) * s ^ 5 + (873 / 2 : ℂ) * s ^ 6 + (54 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1152 : ℂ) + (-1446 : ℂ) * s + (-3844 : ℂ) * s ^ 2 + (-7427 / 2 : ℂ) * s ^ 3 + (-1783 : ℂ) * s ^ 4 + (-891 / 2 : ℂ) * s ^ 5 + (-57 : ℂ) * s ^ 6 + (-3 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1008 : ℂ) + (-462 : ℂ) * s + (261 : ℂ) * s ^ 2 + (362 : ℂ) * s ^ 3 + (129 : ℂ) * s ^ 4 + (14 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((336 : ℂ) + (400 : ℂ) * s + (81 : ℂ) * s ^ 2 + (-5 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-36 : ℂ) + (-12 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI1_qT0_lam s r hs hs3 hs1, ssSourceTF_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI1_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI1_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((126 : ℂ) * s + (645 : ℂ) * s ^ 2 + (2445 / 2 : ℂ) * s ^ 3 + (4575 / 4 : ℂ) * s ^ 4 + (576 : ℂ) * s ^ 5 + (309 / 2 : ℂ) * s ^ 6 + (39 / 2 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1200 : ℂ) * s + (-4924 : ℂ) * s ^ 2 + (-8138 : ℂ) * s ^ 3 + (-7115 : ℂ) * s ^ 4 + (-6993 / 2 : ℂ) * s ^ 5 + (-1859 / 2 : ℂ) * s ^ 6 + (-227 / 2 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-624 : ℂ) + (-292 : ℂ) * s + (536 : ℂ) * s ^ 2 + (-863 / 2 : ℂ) * s ^ 3 + (-4093 / 4 : ℂ) * s ^ 4 + (-309 : ℂ) * s ^ 5 + (169 / 2 : ℂ) * s ^ 6 + (81 / 2 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((840 : ℂ) + (3328 : ℂ) * s + (6734 : ℂ) * s ^ 2 + (4822 : ℂ) * s ^ 3 + (2991 / 2 : ℂ) * s ^ 4 + (649 / 2 : ℂ) * s ^ 5 + (133 / 2 : ℂ) * s ^ 6 + (11 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((408 : ℂ) + (-746 : ℂ) * s + (333 : ℂ) * s ^ 2 + (101 : ℂ) * s ^ 3 + (-141 : ℂ) * s ^ 4 + (-35 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-840 : ℂ) + (-1288 : ℂ) * s + (-300 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((216 : ℂ) + (72 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI1_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI1_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI1_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((-6 : ℂ) * s + (40 : ℂ) * s ^ 2 + (517 / 2 : ℂ) * s ^ 3 + (919 / 2 : ℂ) * s ^ 4 + (735 / 2 : ℂ) * s ^ 5 + (293 / 2 : ℂ) * s ^ 6 + (28 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((48 : ℂ) + (208 : ℂ) * s + (1006 : ℂ) * s ^ 2 + (2435 : ℂ) * s ^ 3 + (2645 : ℂ) * s ^ 4 + (1378 : ℂ) * s ^ 5 + (325 : ℂ) * s ^ 6 + (21 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((180 : ℂ) + (396 : ℂ) * s + (721 : ℂ) * s ^ 2 + (5017 / 2 : ℂ) * s ^ 3 + (5215 / 2 : ℂ) * s ^ 4 + (2033 / 2 : ℂ) * s ^ 5 + (263 / 2 : ℂ) * s ^ 6 + (-1 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1224 : ℂ) + (-3936 : ℂ) * s + (-5922 : ℂ) * s ^ 2 + (-2284 : ℂ) * s ^ 3 + (429 : ℂ) * s ^ 4 + (356 : ℂ) * s ^ 5 + (45 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((1392 : ℂ) + (2606 : ℂ) * s + (321 : ℂ) * s ^ 2 + (-68 : ℂ) * s ^ 3 + (171 : ℂ) * s ^ 4 + (50 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-72 : ℂ) + (840 : ℂ) * s + (378 : ℂ) * s ^ 2 + (30 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-324 : ℂ) + (-108 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI1_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI1_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI1_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((-12 : ℂ) * s ^ 2 + (-40 : ℂ) * s ^ 3 + (-27 : ℂ) * s ^ 4 + (25 : ℂ) * s ^ 5 + (37 : ℂ) * s ^ 6 + (15 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-120 : ℂ) * s + (-316 : ℂ) * s ^ 2 + (-68 : ℂ) * s ^ 3 + (410 : ℂ) * s ^ 4 + (398 : ℂ) * s ^ 5 + (124 : ℂ) * s ^ 6 + (6 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((288 : ℂ) + (1056 : ℂ) * s + (1328 : ℂ) * s ^ 2 + (1182 : ℂ) * s ^ 3 + (543 : ℂ) * s ^ 4 + (-45 : ℂ) * s ^ 5 + (-107 : ℂ) * s ^ 6 + (-21 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((144 : ℂ) + (1152 : ℂ) * s + (656 : ℂ) * s ^ 2 + (-432 : ℂ) * s ^ 3 + (-734 : ℂ) * s ^ 4 + (-348 : ℂ) * s ^ 5 + (-54 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-1008 : ℂ) + (-2064 : ℂ) * s + (-1476 : ℂ) * s ^ 2 + (-606 : ℂ) * s ^ 3 + (-192 : ℂ) * s ^ 4 + (-30 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((432 : ℂ) + (-72 : ℂ) * s + (-180 : ℂ) * s ^ 2 + (-36 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((144 : ℂ) + (48 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI1_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewRadFSrcLam_lauI1 (s r : ℂ) : ℂ := (((192 : ℂ) * s + (1156 : ℂ) * s ^ 2 + (5789 / 2 : ℂ) * s ^ 3 + (3992 : ℂ) * s ^ 4 + (26993 / 8 : ℂ) * s ^ 5 + (14665 / 8 : ℂ) * s ^ 6 + (2593 / 4 : ℂ) * s ^ 7 + (583 / 4 : ℂ) * s ^ 8 + (153 / 8 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((48 : ℂ) + (-2204 : ℂ) * s + (-21175 / 2 : ℂ) * s ^ 2 + (-77831 / 4 : ℂ) * s ^ 3 + (-161427 / 8 : ℂ) * s ^ 4 + (-26867 / 2 : ℂ) * s ^ 5 + (-23725 / 4 : ℂ) * s ^ 6 + (-6905 / 4 : ℂ) * s ^ 7 + (-2601 / 8 : ℂ) * s ^ 8 + (-38 : ℂ) * s ^ 9 + (-9 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-600 : ℂ) + (4006 : ℂ) * s + (17279 / 2 : ℂ) * s ^ 2 + (41949 / 4 : ℂ) * s ^ 3 + (41161 / 4 : ℂ) * s ^ 4 + (56343 / 8 : ℂ) * s ^ 5 + (24737 / 8 : ℂ) * s ^ 6 + (1707 / 2 : ℂ) * s ^ 7 + (147 : ℂ) * s ^ 8 + (131 / 8 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((912 : ℂ) + (-1292 : ℂ) * s + (1797 / 2 : ℂ) * s ^ 2 + (12239 / 2 : ℂ) * s ^ 3 + (46987 / 8 : ℂ) * s ^ 4 + (2994 : ℂ) * s ^ 5 + (4007 / 4 : ℂ) * s ^ 6 + (224 : ℂ) * s ^ 7 + (259 / 8 : ℂ) * s ^ 8 + (5 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-216 : ℂ) + (-914 : ℂ) * s + (-507 / 2 : ℂ) * s ^ 2 + (-73 / 4 : ℂ) * s ^ 3 + (265 / 4 : ℂ) * s ^ 4 + (107 / 4 : ℂ) * s ^ 5 + (17 / 4 : ℂ) * s ^ 6 + (1 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-144 : ℂ) + (274 : ℂ) * s + (195 : ℂ) * s ^ 2 + (-117 / 4 : ℂ) * s ^ 3 + (-87 / 2 : ℂ) * s ^ 4 + (-17 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-68 : ℂ) * s + (-48 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((6 : ℂ) * s))))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2)

theorem skewRadFSrc_lauI1_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFSrc_lauI1 s r ((s + 1) * (s + 2)) (ssSourceTR (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2))) = skewRadFSrcLam_lauI1 s r := by
  unfold skewRadFSrc_lauI1
  rw [skewRadPieceFS_lauI1_qtr0 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI1_qtr1 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI1_qtr2 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI1_qt0 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI1_qt1 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI1_qt2 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI1_qT0 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI1_qT1 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI1_qT2 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI1_qT3 s r hr hf hs hs3 hs1]
  unfold skewRadFSrcLam_lauI1
  all_goals (try simp only [← add_div])
  ring

theorem skewRadPieceFS_lauI3_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI3_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((540 : ℂ) * s + (9459 / 4 : ℂ) * s ^ 2 + (17763 / 4 : ℂ) * s ^ 3 + (74835 / 16 : ℂ) * s ^ 4 + (12099 / 4 : ℂ) * s ^ 5 + (4923 / 4 : ℂ) * s ^ 6 + (2463 / 8 : ℂ) * s ^ 7 + (693 / 16 : ℂ) * s ^ 8 + (21 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1587 : ℂ) * s + (-44539 / 4 : ℂ) * s ^ 2 + (-106685 / 4 : ℂ) * s ^ 3 + (-524885 / 16 : ℂ) * s ^ 4 + (-190967 / 8 : ℂ) * s ^ 5 + (-43359 / 4 : ℂ) * s ^ 6 + (-24643 / 8 : ℂ) * s ^ 7 + (-8363 / 16 : ℂ) * s ^ 8 + (-93 / 2 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-16413 : ℂ) * s + (-90577 / 2 : ℂ) * s ^ 2 + (-102967 / 2 : ℂ) * s ^ 3 + (-506279 / 16 : ℂ) * s ^ 4 + (-22465 / 2 : ℂ) * s ^ 5 + (-8147 / 4 : ℂ) * s ^ 6 + (249 / 8 : ℂ) * s ^ 7 + (1699 / 16 : ℂ) * s ^ 8 + (175 / 8 : ℂ) * s ^ 9 + (3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((21510 : ℂ) * s + (120285 / 2 : ℂ) * s ^ 2 + (131801 / 2 : ℂ) * s ^ 3 + (633289 / 16 : ℂ) * s ^ 4 + (117453 / 8 : ℂ) * s ^ 5 + (14115 / 4 : ℂ) * s ^ 6 + (4575 / 8 : ℂ) * s ^ 7 + (1027 / 16 : ℂ) * s ^ 8 + (4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-522 : ℂ) * s + (22623 / 4 : ℂ) * s ^ 2 + (21039 / 4 : ℂ) * s ^ 3 + (7689 / 4 : ℂ) * s ^ 4 + (1311 / 4 : ℂ) * s ^ 5 + (2 : ℂ) * s ^ 6 + (-11 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-3123 : ℂ) * s + (-9375 / 4 : ℂ) * s ^ 2 + (-4509 / 4 : ℂ) * s ^ 3 + (-1329 / 4 : ℂ) * s ^ 4 + (-135 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-405 : ℂ) * s + (-180 : ℂ) * s ^ 2 + (-15 : ℂ) * s ^ 3))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI3_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI3_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI3_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((-54 : ℂ) * s + (-819 / 4 : ℂ) * s ^ 2 + (-555 / 4 : ℂ) * s ^ 3 + (6045 / 16 : ℂ) * s ^ 4 + (6543 / 8 : ℂ) * s ^ 5 + (2835 / 4 : ℂ) * s ^ 6 + (2673 / 8 : ℂ) * s ^ 7 + (1431 / 16 : ℂ) * s ^ 8 + (51 / 4 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-855 : ℂ) * s + (1413 / 4 : ℂ) * s ^ 2 + (23795 / 4 : ℂ) * s ^ 3 + (163315 / 16 : ℂ) * s ^ 4 + (68457 / 8 : ℂ) * s ^ 5 + (16569 / 4 : ℂ) * s ^ 6 + (9307 / 8 : ℂ) * s ^ 7 + (2657 / 16 : ℂ) * s ^ 8 + (23 / 4 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((5568 : ℂ) * s + (38167 / 2 : ℂ) * s ^ 2 + (109943 / 4 : ℂ) * s ^ 3 + (348947 / 16 : ℂ) * s ^ 4 + (83271 / 8 : ℂ) * s ^ 5 + (12089 / 4 : ℂ) * s ^ 6 + (3951 / 8 : ℂ) * s ^ 7 + (529 / 16 : ℂ) * s ^ 8 + (-1 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2982 : ℂ) * s + (-36059 / 2 : ℂ) * s ^ 2 + (-23110 : ℂ) * s ^ 3 + (-209767 / 16 : ℂ) * s ^ 4 + (-25921 / 8 : ℂ) * s ^ 5 + (31 / 2 : ℂ) * s ^ 6 + (1249 / 8 : ℂ) * s ^ 7 + (327 / 16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-10686 : ℂ) * s + (-81811 / 4 : ℂ) * s ^ 2 + (-23337 / 2 : ℂ) * s ^ 3 + (-4027 / 2 : ℂ) * s ^ 4 + (431 : ℂ) * s ^ 5 + (905 / 4 : ℂ) * s ^ 6 + (55 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((8037 : ℂ) * s + (38409 / 4 : ℂ) * s ^ 2 + (20571 / 4 : ℂ) * s ^ 3 + (5319 / 4 : ℂ) * s ^ 4 + (513 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((972 : ℂ) * s + (432 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI3_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI3_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI3_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((-54 : ℂ) * s ^ 2 + (-531 / 2 : ℂ) * s ^ 3 + (-483 : ℂ) * s ^ 4 + (-3255 / 8 : ℂ) * s ^ 5 + (-279 / 2 : ℂ) * s ^ 6 + (33 / 2 : ℂ) * s ^ 7 + (111 / 4 : ℂ) * s ^ 8 + (63 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-1476 : ℂ) * s + (-5310 : ℂ) * s ^ 2 + (-14561 / 2 : ℂ) * s ^ 3 + (-17517 / 4 : ℂ) * s ^ 4 + (-2087 / 4 : ℂ) * s ^ 5 + (737 : ℂ) * s ^ 6 + (1575 / 4 : ℂ) * s ^ 7 + (69 : ℂ) * s ^ 8 + (1 / 2 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-4434 : ℂ) * s + (-5099 : ℂ) * s ^ 2 + (6523 / 2 : ℂ) * s ^ 3 + (7950 : ℂ) * s ^ 4 + (37451 / 8 : ℂ) * s ^ 5 + (3801 / 4 : ℂ) * s ^ 6 + (-217 / 2 : ℂ) * s ^ 7 + (-293 / 4 : ℂ) * s ^ 8 + (-67 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((12660 : ℂ) * s + (26861 : ℂ) * s ^ 2 + (40843 / 2 : ℂ) * s ^ 3 + (19977 / 4 : ℂ) * s ^ 4 + (-6395 / 4 : ℂ) * s ^ 5 + (-5039 / 4 : ℂ) * s ^ 6 + (-1147 / 4 : ℂ) * s ^ 7 + (-47 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1080 : ℂ) * s + (-7155 : ℂ) * s ^ 2 + (-11748 : ℂ) * s ^ 3 + (-7077 : ℂ) * s ^ 4 + (-2061 : ℂ) * s ^ 5 + (-288 : ℂ) * s ^ 6 + (-15 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-7344 : ℂ) * s + (-9027 : ℂ) * s ^ 2 + (-4371 : ℂ) * s ^ 3 + (-1005 : ℂ) * s ^ 4 + (-93 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-486 : ℂ) * s + (-216 : ℂ) * s ^ 2 + (-18 : ℂ) * s ^ 3))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI3_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI3_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI3_qt0 s r ((s + 1) * (s + 2)) * ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((540 : ℂ) * s + (1926 : ℂ) * s ^ 2 + (5799 / 2 : ℂ) * s ^ 3 + (9453 / 4 : ℂ) * s ^ 4 + (8751 / 8 : ℂ) * s ^ 5 + (4113 / 16 : ℂ) * s ^ 6 + (27 / 4 : ℂ) * s ^ 7 + (-93 / 8 : ℂ) * s ^ 8 + (-21 / 8 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-4989 : ℂ) * s + (-17725 : ℂ) * s ^ 2 + (-27179 : ℂ) * s ^ 3 + (-47007 / 2 : ℂ) * s ^ 4 + (-199901 / 16 : ℂ) * s ^ 5 + (-8273 / 2 : ℂ) * s ^ 6 + (-809 : ℂ) * s ^ 7 + (-611 / 8 : ℂ) * s ^ 8 + (-3 / 16 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((9820 : ℂ) * s + (65385 / 2 : ℂ) * s ^ 2 + (45990 : ℂ) * s ^ 3 + (290337 / 8 : ℂ) * s ^ 4 + (142237 / 8 : ℂ) * s ^ 5 + (89059 / 16 : ℂ) * s ^ 6 + (8629 / 8 : ℂ) * s ^ 7 + (907 / 8 : ℂ) * s ^ 8 + (15 / 4 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-6758 : ℂ) * s + (-36969 / 2 : ℂ) * s ^ 2 + (-44151 / 2 : ℂ) * s ^ 3 + (-60201 / 4 : ℂ) * s ^ 4 + (-101537 / 16 : ℂ) * s ^ 5 + (-13543 / 8 : ℂ) * s ^ 6 + (-557 / 2 : ℂ) * s ^ 7 + (-203 / 8 : ℂ) * s ^ 8 + (-15 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1468 : ℂ) * s + (3437 / 2 : ℂ) * s ^ 2 + (733 / 2 : ℂ) * s ^ 3 + (-969 / 8 : ℂ) * s ^ 4 + (-321 / 8 : ℂ) * s ^ 5 + (49 / 8 : ℂ) * s ^ 6 + (17 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-225 : ℂ) * s + (-297 / 2 : ℂ) * s ^ 2 + (-33 / 2 : ℂ) * s ^ 3 + (39 / 2 : ℂ) * s ^ 4 + (13 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((132 : ℂ) * s + (21 : ℂ) * s ^ 2 + (15 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((12 : ℂ) * s))))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI3_qt0_lam s r hs hs3 hs1, ssSourceT_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI3_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI3_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((405 / 2 : ℂ) * s ^ 2 + (2835 / 4 : ℂ) * s ^ 3 + (8073 / 8 : ℂ) * s ^ 4 + (11973 / 16 : ℂ) * s ^ 5 + (4809 / 16 : ℂ) * s ^ 6 + (453 / 8 : ℂ) * s ^ 7 + (-27 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((324 : ℂ) * s + (1395 : ℂ) * s ^ 2 + (2370 : ℂ) * s ^ 3 + (8531 / 4 : ℂ) * s ^ 4 + (4345 / 4 : ℂ) * s ^ 5 + (2461 / 8 : ℂ) * s ^ 6 + (203 / 4 : ℂ) * s ^ 7 + (41 / 4 : ℂ) * s ^ 8 + (3 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-414 : ℂ) * s + (-2658 : ℂ) * s ^ 2 + (-9309 / 2 : ℂ) * s ^ 3 + (-31247 / 8 : ℂ) * s ^ 4 + (-29167 / 16 : ℂ) * s ^ 5 + (-7511 / 16 : ℂ) * s ^ 6 + (-445 / 8 : ℂ) * s ^ 7 + (-5 / 2 : ℂ) * s ^ 8 + (-15 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-1116 : ℂ) * s + (-2307 : ℂ) * s ^ 2 + (-1449 : ℂ) * s ^ 3 + (-244 : ℂ) * s ^ 4 + (-65 / 8 : ℂ) * s ^ 5 + (-293 / 4 : ℂ) * s ^ 6 + (-85 / 2 : ℂ) * s ^ 7 + (-31 / 4 : ℂ) * s ^ 8 + (-3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((2016 : ℂ) * s + (9471 / 2 : ℂ) * s ^ 2 + (15903 / 4 : ℂ) * s ^ 3 + (1302 : ℂ) * s ^ 4 + (59 / 2 : ℂ) * s ^ 5 + (-131 / 2 : ℂ) * s ^ 6 + (-37 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-648 : ℂ) * s + (-1260 : ℂ) * s ^ 2 + (-933 : ℂ) * s ^ 3 + (-294 : ℂ) * s ^ 4 + (-33 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-162 : ℂ) * s + (-108 : ℂ) * s ^ 2 + (-18 : ℂ) * s ^ 3))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI3_qt1_lam s r hs hs3 hs1, ssSourceT1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI3_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI3_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((-54 : ℂ) * s + (-531 / 2 : ℂ) * s ^ 2 + (-483 : ℂ) * s ^ 3 + (-3255 / 8 : ℂ) * s ^ 4 + (-279 / 2 : ℂ) * s ^ 5 + (33 / 2 : ℂ) * s ^ 6 + (111 / 4 : ℂ) * s ^ 7 + (63 / 8 : ℂ) * s ^ 8 + (3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-549 : ℂ) * s + (-2259 / 2 : ℂ) * s ^ 2 + (-1817 / 4 : ℂ) * s ^ 3 + (4289 / 8 : ℂ) * s ^ 4 + (2263 / 4 : ℂ) * s ^ 5 + (164 : ℂ) * s ^ 6 + (-8 : ℂ) * s ^ 7 + (-93 / 8 : ℂ) * s ^ 8 + (-3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1677 : ℂ) * s + (4558 : ℂ) * s ^ 2 + (17167 / 4 : ℂ) * s ^ 3 + (10815 / 8 : ℂ) * s ^ 4 + (-324 : ℂ) * s ^ 5 + (-631 / 2 : ℂ) * s ^ 6 + (-127 / 2 : ℂ) * s ^ 7 + (-3 / 8 : ℂ) * s ^ 8 + (3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-510 : ℂ) * s + (-3056 : ℂ) * s ^ 2 + (-17267 / 4 : ℂ) * s ^ 3 + (-19449 / 8 : ℂ) * s ^ 4 + (-1869 / 4 : ℂ) * s ^ 5 + (73 : ℂ) * s ^ 6 + (40 : ℂ) * s ^ 7 + (33 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1464 : ℂ) * s + (-3325 / 2 : ℂ) * s ^ 2 + (-3 / 4 : ℂ) * s ^ 3 + (1393 / 2 : ℂ) * s ^ 4 + (341 : ℂ) * s ^ 5 + (62 : ℂ) * s ^ 6 + (15 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((819 : ℂ) * s + (3003 / 2 : ℂ) * s ^ 2 + (954 : ℂ) * s ^ 3 + (507 / 2 : ℂ) * s ^ 4 + (24 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((81 : ℂ) * s + (54 : ℂ) * s ^ 2 + (9 : ℂ) * s ^ 3))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI3_qt2_lam s r hs hs3 hs1, ssSourceT2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI3_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI3_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((480 : ℂ) + (1804 : ℂ) * s + (2912 : ℂ) * s ^ 2 + (2636 : ℂ) * s ^ 3 + (1465 : ℂ) * s ^ 4 + (2053 / 4 : ℂ) * s ^ 5 + (445 / 4 : ℂ) * s ^ 6 + (55 / 4 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-4752 : ℂ) + (-15702 : ℂ) * s + (-22499 : ℂ) * s ^ 2 + (-36819 / 2 : ℂ) * s ^ 3 + (-37773 / 4 : ℂ) * s ^ 4 + (-12409 / 4 : ℂ) * s ^ 5 + (-2529 / 4 : ℂ) * s ^ 6 + (-289 / 4 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((11592 : ℂ) + (32334 : ℂ) * s + (38425 : ℂ) * s ^ 2 + (26145 : ℂ) * s ^ 3 + (22745 / 2 : ℂ) * s ^ 4 + (13131 / 4 : ℂ) * s ^ 5 + (2439 / 4 : ℂ) * s ^ 6 + (257 / 4 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-11640 : ℂ) + (-25222 : ℂ) * s + (-23005 : ℂ) * s ^ 2 + (-25195 / 2 : ℂ) * s ^ 3 + (-17705 / 4 : ℂ) * s ^ 4 + (-3803 / 4 : ℂ) * s ^ 5 + (-451 / 4 : ℂ) * s ^ 6 + (-23 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((5040 : ℂ) + (6990 : ℂ) * s + (4641 : ℂ) * s ^ 2 + (1776 : ℂ) * s ^ 3 + (360 : ℂ) * s ^ 4 + (29 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-648 : ℂ) + (-180 : ℂ) * s + (-42 : ℂ) * s ^ 2 + (-18 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (-24 : ℂ) * s))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI3_qT0_lam s r hs hs3 hs1, ssSourceTF_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI3_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI3_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((480 : ℂ) + (2338 : ℂ) * s + (4653 : ℂ) * s ^ 2 + (9887 / 2 : ℂ) * s ^ 3 + (12235 / 4 : ℂ) * s ^ 4 + (1119 : ℂ) * s ^ 5 + (463 / 2 : ℂ) * s ^ 6 + (47 / 2 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-3672 : ℂ) + (-15540 : ℂ) * s + (-27398 : ℂ) * s ^ 2 + (-26595 : ℂ) * s ^ 3 + (-15618 : ℂ) * s ^ 4 + (-11263 / 2 : ℂ) * s ^ 5 + (-2361 / 2 : ℂ) * s ^ 6 + (-243 / 2 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3576 : ℂ) + (10900 : ℂ) * s + (13322 : ℂ) * s ^ 2 + (17515 / 2 : ℂ) * s ^ 3 + (13983 / 4 : ℂ) * s ^ 4 + (1018 : ℂ) * s ^ 5 + (519 / 2 : ℂ) * s ^ 6 + (89 / 2 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3384 : ℂ) + (12816 : ℂ) * s + (17900 : ℂ) * s ^ 2 + (11643 : ℂ) * s ^ 3 + (7413 / 2 : ℂ) * s ^ 4 + (1215 / 2 : ℂ) * s ^ 5 + (131 / 2 : ℂ) * s ^ 6 + (11 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-4632 : ℂ) + (-9470 : ℂ) * s + (-4973 : ℂ) * s ^ 2 + (-1149 : ℂ) * s ^ 3 + (-283 : ℂ) * s ^ 4 + (-53 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((288 : ℂ) + (-1236 : ℂ) * s + (-480 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((576 : ℂ) + (192 : ℂ) * s))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI3_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI3_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI3_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((-96 : ℂ) + (-386 : ℂ) * s + (-424 : ℂ) * s ^ 2 + (231 / 2 : ℂ) * s ^ 3 + (1129 / 2 : ℂ) * s ^ 4 + (913 / 2 : ℂ) * s ^ 5 + (339 / 2 : ℂ) * s ^ 6 + (30 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-216 : ℂ) + (588 : ℂ) * s + (3664 : ℂ) * s ^ 2 + (5810 : ℂ) * s ^ 3 + (4410 : ℂ) * s ^ 4 + (1759 : ℂ) * s ^ 5 + (338 : ℂ) * s ^ 6 + (17 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2988 : ℂ) + (6948 : ℂ) * s + (7135 : ℂ) * s ^ 2 + (9563 / 2 : ℂ) * s ^ 3 + (4593 / 2 : ℂ) * s ^ 4 + (1339 / 2 : ℂ) * s ^ 5 + (169 / 2 : ℂ) * s ^ 6 + (1 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-6456 : ℂ) + (-15520 : ℂ) * s + (-16984 : ℂ) * s ^ 2 + (-8151 : ℂ) * s ^ 3 + (-1160 : ℂ) * s ^ 4 + (223 : ℂ) * s ^ 5 + (56 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((4320 : ℂ) + (6282 : ℂ) * s + (1803 : ℂ) * s ^ 2 + (126 : ℂ) * s ^ 3 + (201 : ℂ) * s ^ 4 + (60 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((432 : ℂ) + (2412 : ℂ) * s + (1350 : ℂ) * s ^ 2 + (198 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-972 : ℂ) + (-324 : ℂ) * s))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI3_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceFS_lauI3_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFQ_lauI3_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((-48 : ℂ) * s + (-220 : ℂ) * s ^ 2 + (-356 : ℂ) * s ^ 3 + (-243 : ℂ) * s ^ 4 + (-43 : ℂ) * s ^ 5 + (29 : ℂ) * s ^ 6 + (15 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-576 : ℂ) + (-2328 : ℂ) * s + (-3268 : ℂ) * s ^ 2 + (-1704 : ℂ) * s ^ 3 + (130 : ℂ) * s ^ 4 + (450 : ℂ) * s ^ 5 + (140 : ℂ) * s ^ 6 + (6 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((576 : ℂ) + (2016 : ℂ) * s + (4016 : ℂ) * s ^ 2 + (3842 : ℂ) * s ^ 3 + (1535 : ℂ) * s ^ 4 + (55 : ℂ) * s ^ 5 + (-115 : ℂ) * s ^ 6 + (-21 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((2448 : ℂ) + (6144 : ℂ) * s + (4512 : ℂ) * s ^ 2 + (300 : ℂ) * s ^ 3 + (-1014 : ℂ) * s ^ 4 + (-432 : ℂ) * s ^ 5 + (-54 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-3888 : ℂ) + (-5760 : ℂ) * s + (-4404 : ℂ) * s ^ 2 + (-1926 : ℂ) * s ^ 3 + (-408 : ℂ) * s ^ 4 + (-30 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1008 : ℂ) + (-168 : ℂ) * s + (-636 : ℂ) * s ^ 2 + (-156 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((432 : ℂ) + (144 : ℂ) * s))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewRadFQ_lauI3_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewRadFSrcLam_lauI3 (s r : ℂ) : ℂ := (((864 : ℂ) + (4680 : ℂ) * s + (10890 : ℂ) * s ^ 2 + (58003 / 4 : ℂ) * s ^ 3 + (49531 / 4 : ℂ) * s ^ 4 + (114947 / 16 : ℂ) * s ^ 5 + (23323 / 8 : ℂ) * s ^ 6 + (6655 / 8 : ℂ) * s ^ 7 + (649 / 4 : ℂ) * s ^ 8 + (315 / 16 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-9216 : ℂ) + (-42114 : ℂ) * s + (-83052 : ℂ) * s ^ 2 + (-376659 / 4 : ℂ) * s ^ 3 + (-273333 / 4 : ℂ) * s ^ 4 + (-531233 / 16 : ℂ) * s ^ 5 + (-87681 / 8 : ℂ) * s ^ 6 + (-9841 / 4 : ℂ) * s ^ 7 + (-3011 / 8 : ℂ) * s ^ 8 + (-623 / 16 : ℂ) * s ^ 9 + (-9 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((18732 : ℂ) + (48002 : ℂ) * s + (132373 / 2 : ℂ) * s ^ 2 + (68417 : ℂ) * s ^ 3 + (404437 / 8 : ℂ) * s ^ 4 + (392251 / 16 : ℂ) * s ^ 5 + (30223 / 4 : ℂ) * s ^ 6 + (5859 / 4 : ℂ) * s ^ 7 + (182 : ℂ) * s ^ 8 + (265 / 16 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-12264 : ℂ) + (1022 : ℂ) * s + (55099 / 2 : ℂ) * s ^ 2 + (106261 / 4 : ℂ) * s ^ 3 + (43381 / 4 : ℂ) * s ^ 4 + (39505 / 16 : ℂ) * s ^ 5 + (4369 / 8 : ℂ) * s ^ 6 + (160 : ℂ) * s ^ 7 + (257 / 8 : ℂ) * s ^ 8 + (43 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((840 : ℂ) + (-10066 : ℂ) * s + (-40187 / 2 : ℂ) * s ^ 2 + (-59953 / 4 : ℂ) * s ^ 3 + (-43367 / 8 : ℂ) * s ^ 4 + (-7727 / 8 : ℂ) * s ^ 5 + (-457 / 8 : ℂ) * s ^ 6 + (29 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((1080 : ℂ) + (-1656 : ℂ) * s + (-2967 / 2 : ℂ) * s ^ 2 + (-339 : ℂ) * s ^ 3 + (-57 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-36 : ℂ) + (120 : ℂ) * s + (3 : ℂ) * s ^ 2 + (9 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((12 : ℂ) * s))))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2)

theorem skewRadFSrc_lauI3_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadFSrc_lauI3 s r ((s + 1) * (s + 2)) (ssSourceTR (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2))) = skewRadFSrcLam_lauI3 s r := by
  unfold skewRadFSrc_lauI3
  rw [skewRadPieceFS_lauI3_qtr0 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI3_qtr1 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI3_qtr2 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI3_qt0 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI3_qt1 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI3_qt2 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI3_qT0 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI3_qT1 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI3_qT2 s r hr hf hs hs3 hs1, skewRadPieceFS_lauI3_qT3 s r hr hf hs hs3 hs1]
  unfold skewRadFSrcLam_lauI3
  all_goals (try simp only [← add_div])
  ring

/-! ## Sources against the reflected family -/

theorem skewRadPieceSF_qtr0_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qtr0_lauR s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-540 : ℂ) * s ^ 2 + (-16353 / 8 : ℂ) * s ^ 3 + (-50325 / 16 : ℂ) * s ^ 4 + (-20415 / 8 : ℂ) * s ^ 5 + (-9471 / 8 : ℂ) * s ^ 6 + (-2523 / 8 : ℂ) * s ^ 7 + (-717 / 16 : ℂ) * s ^ 8 + (-21 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((720 : ℂ) * s + (10311 / 2 : ℂ) * s ^ 2 + (98839 / 8 : ℂ) * s ^ 3 + (278089 / 16 : ℂ) * s ^ 4 + (58453 / 4 : ℂ) * s ^ 5 + (57047 / 8 : ℂ) * s ^ 6 + (15267 / 8 : ℂ) * s ^ 7 + (3721 / 16 : ℂ) * s ^ 8 + (3 / 2 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-4440 : ℂ) * s + (-34553 / 2 : ℂ) * s ^ 2 + (-249577 / 8 : ℂ) * s ^ 3 + (-497411 / 16 : ℂ) * s ^ 4 + (-152535 / 8 : ℂ) * s ^ 5 + (-52757 / 8 : ℂ) * s ^ 6 + (-7853 / 8 : ℂ) * s ^ 7 + (517 / 16 : ℂ) * s ^ 8 + (185 / 8 : ℂ) * s ^ 9 + (3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((10110 : ℂ) * s + (27367 : ℂ) * s ^ 2 + (198287 / 8 : ℂ) * s ^ 3 + (222271 / 16 : ℂ) * s ^ 4 + (11433 / 2 : ℂ) * s ^ 5 + (9533 / 8 : ℂ) * s ^ 6 + (-191 / 8 : ℂ) * s ^ 7 + (-689 / 16 : ℂ) * s ^ 8 + (-4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-9990 : ℂ) * s + (-20247 / 2 : ℂ) * s ^ 2 + (-10705 / 4 : ℂ) * s ^ 3 + (-90 : ℂ) * s ^ 4 + (-399 / 4 : ℂ) * s ^ 5 + (-28 : ℂ) * s ^ 6 + (7 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((522 : ℂ) * s + (933 / 2 : ℂ) * s ^ 2 + (-213 / 4 : ℂ) * s ^ 3 + (-60 : ℂ) * s ^ 4 + (-13 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((54 : ℂ) * s + (9 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qtr0_lauR_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qtr1_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qtr1_lauR s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((-180 : ℂ) * s ^ 2 + (-4341 / 8 : ℂ) * s ^ 3 + (-8397 / 16 : ℂ) * s ^ 4 + (-93 / 2 : ℂ) * s ^ 5 + (2067 / 8 : ℂ) * s ^ 6 + (1599 / 8 : ℂ) * s ^ 7 + (1083 / 16 : ℂ) * s ^ 8 + (45 / 4 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((144 : ℂ) * s + (-1449 : ℂ) * s ^ 2 + (-63239 / 8 : ℂ) * s ^ 3 + (-227403 / 16 : ℂ) * s ^ 4 + (-26183 / 2 : ℂ) * s ^ 5 + (-55583 / 8 : ℂ) * s ^ 6 + (-17299 / 8 : ℂ) * s ^ 7 + (-6011 / 16 : ℂ) * s ^ 8 + (-125 / 4 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1470 : ℂ) * s + (11317 : ℂ) * s ^ 2 + (203529 / 8 : ℂ) * s ^ 3 + (448265 / 16 : ℂ) * s ^ 4 + (71969 / 4 : ℂ) * s ^ 5 + (54017 / 8 : ℂ) * s ^ 6 + (10889 / 8 : ℂ) * s ^ 7 + (1917 / 16 : ℂ) * s ^ 8 + (2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-4170 : ℂ) * s + (-34013 / 2 : ℂ) * s ^ 2 + (-128899 / 8 : ℂ) * s ^ 3 + (-127437 / 16 : ℂ) * s ^ 4 + (-2569 : ℂ) * s ^ 5 + (-3139 / 8 : ℂ) * s ^ 6 + (223 / 8 : ℂ) * s ^ 7 + (179 / 16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((4578 : ℂ) * s + (1118 : ℂ) * s ^ 2 + (-2503 : ℂ) * s ^ 3 + (-9477 / 4 : ℂ) * s ^ 4 + (-928 : ℂ) * s ^ 5 + (-745 / 4 : ℂ) * s ^ 6 + (-35 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((1218 : ℂ) * s + (2357 / 2 : ℂ) * s ^ 2 + (1771 / 4 : ℂ) * s ^ 3 + (166 : ℂ) * s ^ 4 + (139 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-216 : ℂ) * s + (-36 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qtr1_lauR_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qtr2_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qtr2_lauR s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((540 : ℂ) * s ^ 2 + (8649 / 4 : ℂ) * s ^ 3 + (28803 / 8 : ℂ) * s ^ 4 + (26145 / 8 : ℂ) * s ^ 5 + (1782 : ℂ) * s ^ 6 + (603 : ℂ) * s ^ 7 + (999 / 8 : ℂ) * s ^ 8 + (117 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-288 : ℂ) * s + (-7155 / 2 : ℂ) * s ^ 2 + (-41629 / 4 : ℂ) * s ^ 3 + (-57905 / 4 : ℂ) * s ^ 4 + (-11403 : ℂ) * s ^ 5 + (-21573 / 4 : ℂ) * s ^ 6 + (-6187 / 4 : ℂ) * s ^ 7 + (-1041 / 4 : ℂ) * s ^ 8 + (-23 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1284 : ℂ) * s + (9029 : ℂ) * s ^ 2 + (76823 / 4 : ℂ) * s ^ 3 + (170383 / 8 : ℂ) * s ^ 4 + (112327 / 8 : ℂ) * s ^ 5 + (22137 / 4 : ℂ) * s ^ 6 + (1273 : ℂ) * s ^ 7 + (1271 / 8 : ℂ) * s ^ 8 + (67 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2268 : ℂ) * s + (-22551 / 2 : ℂ) * s ^ 2 + (-63691 / 4 : ℂ) * s ^ 3 + (-13333 : ℂ) * s ^ 4 + (-7015 : ℂ) * s ^ 5 + (-2138 : ℂ) * s ^ 6 + (-1377 / 4 : ℂ) * s ^ 7 + (-47 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2280 : ℂ) * s + (6322 : ℂ) * s ^ 2 + (5295 : ℂ) * s ^ 3 + (3025 : ℂ) * s ^ 4 + (1136 : ℂ) * s ^ 5 + (215 : ℂ) * s ^ 6 + (15 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1116 : ℂ) * s + (-1056 : ℂ) * s ^ 2 + (-327 : ℂ) * s ^ 3 + (-114 : ℂ) * s ^ 4 + (-27 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((108 : ℂ) * s + (18 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qtr2_lauR_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qt0_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qt0_lauR s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((270 : ℂ) * s ^ 2 + (3177 / 4 : ℂ) * s ^ 3 + (13053 / 16 : ℂ) * s ^ 4 + (2337 / 8 : ℂ) * s ^ 5 + (-861 / 16 : ℂ) * s ^ 6 + (-75 : ℂ) * s ^ 7 + (-381 / 16 : ℂ) * s ^ 8 + (-27 / 8 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((720 : ℂ) * s + (183 : ℂ) * s ^ 2 + (-18815 / 8 : ℂ) * s ^ 3 + (-52033 / 16 : ℂ) * s ^ 4 + (-21783 / 16 : ℂ) * s ^ 5 + (999 / 4 : ℂ) * s ^ 6 + (1491 / 4 : ℂ) * s ^ 7 + (1775 / 16 : ℂ) * s ^ 8 + (201 / 16 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((720 : ℂ) + (-1602 : ℂ) * s + (-2360 : ℂ) * s ^ 2 + (23799 / 8 : ℂ) * s ^ 3 + (96271 / 16 : ℂ) * s ^ 4 + (12513 / 4 : ℂ) * s ^ 5 + (3175 / 16 : ℂ) * s ^ 6 + (-2581 / 8 : ℂ) * s ^ 7 + (-1651 / 16 : ℂ) * s ^ 8 + (-21 / 2 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-2280 : ℂ) + (1283 : ℂ) * s + (11109 / 2 : ℂ) * s ^ 2 + (7641 / 8 : ℂ) * s ^ 3 + (-52947 / 16 : ℂ) * s ^ 4 + (-35419 / 16 : ℂ) * s ^ 5 + (-3451 / 8 : ℂ) * s ^ 6 + (97 / 4 : ℂ) * s ^ 7 + (257 / 16 : ℂ) * s ^ 8 + (21 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((4164 : ℂ) + (2189 : ℂ) * s + (-3204 : ℂ) * s ^ 2 + (-20563 / 8 : ℂ) * s ^ 3 + (-329 : ℂ) * s ^ 4 + (611 / 4 : ℂ) * s ^ 5 + (37 : ℂ) * s ^ 6 + (5 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2856 : ℂ) + (-2845 : ℂ) * s + (-983 / 2 : ℂ) * s ^ 2 + (201 : ℂ) * s ^ 3 + (115 / 2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((252 : ℂ) + (255 : ℂ) * s + (48 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qt0_lauR_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qt1_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qt1_lauR s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-405 / 4 : ℂ) * s ^ 3 + (-1431 / 4 : ℂ) * s ^ 4 + (-8055 / 16 : ℂ) * s ^ 5 + (-5835 / 16 : ℂ) * s ^ 6 + (-1179 / 8 : ℂ) * s ^ 7 + (-267 / 8 : ℂ) * s ^ 8 + (-63 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((945 : ℂ) * s ^ 2 + (14787 / 4 : ℂ) * s ^ 3 + (46119 / 8 : ℂ) * s ^ 4 + (18611 / 4 : ℂ) * s ^ 5 + (17021 / 8 : ℂ) * s ^ 6 + (2281 / 4 : ℂ) * s ^ 7 + (721 / 8 : ℂ) * s ^ 8 + (33 / 4 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1440 : ℂ) * s + (1731 : ℂ) * s ^ 2 + (-12015 / 4 : ℂ) * s ^ 3 + (-28369 / 4 : ℂ) * s ^ 4 + (-88855 / 16 : ℂ) * s ^ 5 + (-35303 / 16 : ℂ) * s ^ 6 + (-3905 / 8 : ℂ) * s ^ 7 + (-497 / 8 : ℂ) * s ^ 8 + (-75 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-1332 : ℂ) * s + (-3270 : ℂ) * s ^ 2 + (-5823 / 4 : ℂ) * s ^ 3 + (9535 / 8 : ℂ) * s ^ 4 + (9995 / 8 : ℂ) * s ^ 5 + (1651 / 4 : ℂ) * s ^ 6 + (62 : ℂ) * s ^ 7 + (43 / 8 : ℂ) * s ^ 8 + (3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-144 : ℂ) * s + (501 : ℂ) * s ^ 2 + (855 : ℂ) * s ^ 3 + (2081 / 4 : ℂ) * s ^ 4 + (647 / 4 : ℂ) * s ^ 5 + (123 / 4 : ℂ) * s ^ 6 + (13 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((36 : ℂ) * s + (111 : ℂ) * s ^ 2 + (15 : ℂ) * s ^ 3 + (-27 : ℂ) * s ^ 4 + (-7 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-18 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qt1_lauR_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qt2_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qt2_lauR s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((-180 : ℂ) * s ^ 2 + (-2643 / 4 : ℂ) * s ^ 3 + (-7839 / 8 : ℂ) * s ^ 4 + (-3051 / 4 : ℂ) * s ^ 5 + (-1359 / 4 : ℂ) * s ^ 6 + (-351 / 4 : ℂ) * s ^ 7 + (-99 / 8 : ℂ) * s ^ 8 + (-3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-144 : ℂ) * s + (639 / 2 : ℂ) * s ^ 2 + (8413 / 4 : ℂ) * s ^ 3 + (26441 / 8 : ℂ) * s ^ 4 + (9873 / 4 : ℂ) * s ^ 5 + (2017 / 2 : ℂ) * s ^ 6 + (233 : ℂ) * s ^ 7 + (231 / 8 : ℂ) * s ^ 8 + (3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((546 : ℂ) * s + (290 : ℂ) * s ^ 2 + (-9195 / 4 : ℂ) * s ^ 3 + (-32551 / 8 : ℂ) * s ^ 4 + (-2877 : ℂ) * s ^ 5 + (-2095 / 2 : ℂ) * s ^ 6 + (-413 / 2 : ℂ) * s ^ 7 + (-165 / 8 : ℂ) * s ^ 8 + (-3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-690 : ℂ) * s + (-926 : ℂ) * s ^ 2 + (3563 / 4 : ℂ) * s ^ 3 + (17259 / 8 : ℂ) * s ^ 4 + (5625 / 4 : ℂ) * s ^ 5 + (857 / 2 : ℂ) * s ^ 6 + (65 : ℂ) * s ^ 7 + (33 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((318 : ℂ) * s + (613 : ℂ) * s ^ 2 + (17 / 2 : ℂ) * s ^ 3 + (-1717 / 4 : ℂ) * s ^ 4 + (-963 / 4 : ℂ) * s ^ 5 + (-199 / 4 : ℂ) * s ^ 6 + (-15 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-30 : ℂ) * s + (-251 / 2 : ℂ) * s ^ 2 + (-46 : ℂ) * s ^ 3 + (31 / 2 : ℂ) * s ^ 4 + (6 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((9 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qt2_lauR_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT0_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT0_lauR s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((240 : ℂ) * s + (830 : ℂ) * s ^ 2 + (4651 / 4 : ℂ) * s ^ 3 + (3479 / 4 : ℂ) * s ^ 4 + (767 / 2 : ℂ) * s ^ 5 + (199 / 2 : ℂ) * s ^ 6 + (55 / 4 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1608 : ℂ) * s + (-7459 / 2 : ℂ) * s ^ 2 + (-16295 / 4 : ℂ) * s ^ 3 + (-2390 : ℂ) * s ^ 4 + (-794 : ℂ) * s ^ 5 + (-189 : ℂ) * s ^ 6 + (-145 / 4 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3465 : ℂ) * s + (6684 : ℂ) * s ^ 2 + (17969 / 4 : ℂ) * s ^ 3 + (6415 / 4 : ℂ) * s ^ 4 + (641 / 2 : ℂ) * s ^ 5 + (147 / 2 : ℂ) * s ^ 6 + (89 / 4 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-4002 : ℂ) * s + (-9283 / 2 : ℂ) * s ^ 2 + (-7733 / 4 : ℂ) * s ^ 3 + (-1197 / 2 : ℂ) * s ^ 4 + (-113 : ℂ) * s ^ 5 + (-8 : ℂ) * s ^ 6 + (1 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((2085 : ℂ) * s + (1745 : ℂ) * s ^ 2 + (316 : ℂ) * s ^ 3 + (23 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-180 : ℂ) * s + (-132 : ℂ) * s ^ 2))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT0_lauR_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT1_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT1_lauR s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-480 : ℂ) * s + (-1651 : ℂ) * s ^ 2 + (-2201 : ℂ) * s ^ 3 + (-5707 / 4 : ℂ) * s ^ 4 + (-907 / 2 : ℂ) * s ^ 5 + (-55 : ℂ) * s ^ 6 + (5 / 2 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3984 : ℂ) * s + (12799 : ℂ) * s ^ 2 + (33325 / 2 : ℂ) * s ^ 3 + (22347 / 2 : ℂ) * s ^ 4 + (3944 : ℂ) * s ^ 5 + (643 : ℂ) * s ^ 6 + (43 / 2 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-11252 : ℂ) * s + (-29335 : ℂ) * s ^ 2 + (-29464 : ℂ) * s ^ 3 + (-55535 / 4 : ℂ) * s ^ 4 + (-5923 / 2 : ℂ) * s ^ 5 + (-152 : ℂ) * s ^ 6 + (59 / 2 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((13136 : ℂ) * s + (23559 : ℂ) * s ^ 2 + (29015 / 2 : ℂ) * s ^ 3 + (3693 : ℂ) * s ^ 4 + (226 : ℂ) * s ^ 5 + (-52 : ℂ) * s ^ 6 + (-11 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-5500 : ℂ) * s + (-4700 : ℂ) * s ^ 2 + (-1001 : ℂ) * s ^ 3 + (24 : ℂ) * s ^ 4 + (25 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((64 : ℂ) * s + (84 : ℂ) * s ^ 2 + (-52 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((48 : ℂ) * s))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT1_lauR_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT2_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT2_lauR s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((-320 : ℂ) * s + (-963 : ℂ) * s ^ 2 + (-2033 / 2 : ℂ) * s ^ 3 + (-761 / 2 : ℂ) * s ^ 4 + (109 / 2 : ℂ) * s ^ 5 + (163 / 2 : ℂ) * s ^ 6 + (22 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-776 : ℂ) * s + (-4181 : ℂ) * s ^ 2 + (-7841 : ℂ) * s ^ 3 + (-6920 : ℂ) * s ^ 4 + (-3130 : ℂ) * s ^ 5 + (-717 : ℂ) * s ^ 6 + (-73 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((4182 : ℂ) * s + (13828 : ℂ) * s ^ 2 + (33933 / 2 : ℂ) * s ^ 3 + (18797 / 2 : ℂ) * s ^ 4 + (4833 / 2 : ℂ) * s ^ 5 + (483 / 2 : ℂ) * s ^ 6 + (3 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-4078 : ℂ) * s + (-8855 : ℂ) * s ^ 2 + (-5017 : ℂ) * s ^ 3 + (-727 : ℂ) * s ^ 4 + (123 : ℂ) * s ^ 5 + (34 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((206 : ℂ) * s + (-1989 : ℂ) * s ^ 2 + (-1646 : ℂ) * s ^ 3 + (-459 : ℂ) * s ^ 4 + (-40 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((894 : ℂ) * s + (648 : ℂ) * s ^ 2 + (138 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT2_lauR_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT3_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT3_lauR s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((480 : ℂ) * s + (1762 : ℂ) * s ^ 2 + (2613 : ℂ) * s ^ 3 + (2034 : ℂ) * s ^ 4 + (906 : ℂ) * s ^ 5 + (234 : ℂ) * s ^ 6 + (33 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-2364 : ℂ) * s + (-7858 : ℂ) * s ^ 2 + (-10334 : ℂ) * s ^ 3 + (-6930 : ℂ) * s ^ 4 + (-2560 : ℂ) * s ^ 5 + (-522 : ℂ) * s ^ 6 + (-54 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((4704 : ℂ) * s + (13724 : ℂ) * s ^ 2 + (15215 : ℂ) * s ^ 3 + (8206 : ℂ) * s ^ 4 + (2332 : ℂ) * s ^ 5 + (342 : ℂ) * s ^ 6 + (21 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-4776 : ℂ) * s + (-11570 : ℂ) * s ^ 2 + (-9684 : ℂ) * s ^ 3 + (-3784 : ℂ) * s ^ 4 + (-708 : ℂ) * s ^ 5 + (-54 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((2544 : ℂ) * s + (4422 : ℂ) * s ^ 2 + (2274 : ℂ) * s ^ 3 + (474 : ℂ) * s ^ 4 + (30 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-636 : ℂ) * s + (-480 : ℂ) * s ^ 2 + (-84 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((48 : ℂ) * s))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT3_lauR_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewRadSrcFLam_lauR (s r : ℂ) : ℂ := (((-80 : ℂ) * s + (-112 : ℂ) * s ^ 2 + (166 : ℂ) * s ^ 3 + (8079 / 16 : ℂ) * s ^ 4 + (9379 / 16 : ℂ) * s ^ 5 + (1833 / 4 : ℂ) * s ^ 6 + (1989 / 8 : ℂ) * s ^ 7 + (1339 / 16 : ℂ) * s ^ 8 + (243 / 16 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((388 : ℂ) * s + (-1393 : ℂ) * s ^ 2 + (-64763 / 8 : ℂ) * s ^ 3 + (-168911 / 16 : ℂ) * s ^ 4 + (-106587 / 16 : ℂ) * s ^ 5 + (-20875 / 8 : ℂ) * s ^ 6 + (-1533 / 2 : ℂ) * s ^ 7 + (-2951 / 16 : ℂ) * s ^ 8 + (-487 / 16 : ℂ) * s ^ 9 + (-9 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((720 : ℂ) + (-203 : ℂ) * s + (15263 / 2 : ℂ) * s ^ 2 + (146655 / 8 : ℂ) * s ^ 3 + (294505 / 16 : ℂ) * s ^ 4 + (156345 / 16 : ℂ) * s ^ 5 + (12565 / 4 : ℂ) * s ^ 6 + (711 : ℂ) * s ^ 7 + (2089 / 16 : ℂ) * s ^ 8 + (281 / 16 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-2280 : ℂ) + (3213 : ℂ) * s + (-1064 : ℂ) * s ^ 2 + (-71887 / 8 : ℂ) * s ^ 3 + (-140517 / 16 : ℂ) * s ^ 4 + (-62361 / 16 : ℂ) * s ^ 5 + (-8071 / 8 : ℂ) * s ^ 6 + (-777 / 4 : ℂ) * s ^ 7 + (-477 / 16 : ℂ) * s ^ 8 + (-37 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((4164 : ℂ) + (-1434 : ℂ) * s + (-10591 / 2 : ℂ) * s ^ 2 + (-13185 / 8 : ℂ) * s ^ 3 + (1559 / 4 : ℂ) * s ^ 4 + (196 : ℂ) * s ^ 5 + (75 / 4 : ℂ) * s ^ 6 + (9 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2856 : ℂ) + (-2073 : ℂ) * s + (203 : ℂ) * s ^ 2 + (469 / 2 : ℂ) * s ^ 3 + (38 : ℂ) * s ^ 4 + (11 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((252 : ℂ) + (189 : ℂ) * s + (30 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 3))))))))))))) / (r ^ 5 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3)

theorem skewRadSrcF_lauR_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadSrcF_lauR s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = skewRadSrcFLam_lauR s r := by
  unfold skewRadSrcF_lauR
  rw [skewRadPieceSF_qtr0_lauR s r hr hf hs hs3 hs1, skewRadPieceSF_qtr1_lauR s r hr hf hs hs3 hs1, skewRadPieceSF_qtr2_lauR s r hr hf hs hs3 hs1, skewRadPieceSF_qt0_lauR s r hr hf hs hs3 hs1, skewRadPieceSF_qt1_lauR s r hr hf hs hs3 hs1, skewRadPieceSF_qt2_lauR s r hr hf hs hs3 hs1, skewRadPieceSF_qT0_lauR s r hr hf hs hs3 hs1, skewRadPieceSF_qT1_lauR s r hr hf hs hs3 hs1, skewRadPieceSF_qT2_lauR s r hr hf hs hs3 hs1, skewRadPieceSF_qT3_lauR s r hr hf hs hs3 hs1]
  unfold skewRadSrcFLam_lauR
  all_goals (try simp only [← add_div])
  ring

theorem skewRadPieceSF_qtr0_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qtr0_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-162 : ℂ) * s ^ 2 + (-5535 / 8 : ℂ) * s ^ 3 + (-19611 / 16 : ℂ) * s ^ 4 + (-9339 / 8 : ℂ) * s ^ 5 + (-5169 / 8 : ℂ) * s ^ 6 + (-1665 / 8 : ℂ) * s ^ 7 + (-579 / 16 : ℂ) * s ^ 8 + (-21 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((216 : ℂ) * s + (1800 : ℂ) * s ^ 2 + (41235 / 8 : ℂ) * s ^ 3 + (130555 / 16 : ℂ) * s ^ 4 + (7656 : ℂ) * s ^ 5 + (33655 / 8 : ℂ) * s ^ 6 + (10241 / 8 : ℂ) * s ^ 7 + (2863 / 16 : ℂ) * s ^ 8 + (3 / 2 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-1530 : ℂ) * s + (-7455 : ℂ) * s ^ 2 + (-117757 / 8 : ℂ) * s ^ 3 + (-233897 / 16 : ℂ) * s ^ 4 + (-67489 / 8 : ℂ) * s ^ 5 + (-21537 / 8 : ℂ) * s ^ 6 + (-2263 / 8 : ℂ) * s ^ 7 + (1243 / 16 : ℂ) * s ^ 8 + (185 / 8 : ℂ) * s ^ 9 + (3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((4254 : ℂ) * s + (24679 / 2 : ℂ) * s ^ 2 + (70935 / 8 : ℂ) * s ^ 3 + (41005 / 16 : ℂ) * s ^ 4 + (-639 / 4 : ℂ) * s ^ 5 + (-3755 / 8 : ℂ) * s ^ 6 + (-1621 / 8 : ℂ) * s ^ 7 + (-695 / 16 : ℂ) * s ^ 8 + (-4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-4290 : ℂ) * s + (-440 : ℂ) * s ^ 2 + (2571 : ℂ) * s ^ 3 + (7671 / 4 : ℂ) * s ^ 4 + (700 : ℂ) * s ^ 5 + (467 / 4 : ℂ) * s ^ 6 + (9 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1566 : ℂ) * s + (-2013 / 2 : ℂ) * s ^ 2 + (-79 / 4 : ℂ) * s ^ 3 + (93 : ℂ) * s ^ 4 + (61 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s + (-18 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qtr0_lauI1_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qtr1_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qtr1_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((-135 : ℂ) * s ^ 2 + (-3447 / 8 : ℂ) * s ^ 3 + (-7467 / 16 : ℂ) * s ^ 4 + (-453 / 4 : ℂ) * s ^ 5 + (1317 / 8 : ℂ) * s ^ 6 + (1245 / 8 : ℂ) * s ^ 7 + (933 / 16 : ℂ) * s ^ 8 + (21 / 2 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((108 : ℂ) * s + (-1107 : ℂ) * s ^ 2 + (-48081 / 8 : ℂ) * s ^ 3 + (-174757 / 16 : ℂ) * s ^ 4 + (-20491 / 2 : ℂ) * s ^ 5 + (-44749 / 8 : ℂ) * s ^ 6 + (-14533 / 8 : ℂ) * s ^ 7 + (-5349 / 16 : ℂ) * s ^ 8 + (-119 / 4 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1134 : ℂ) * s + (8178 : ℂ) * s ^ 2 + (141115 / 8 : ℂ) * s ^ 3 + (302063 / 16 : ℂ) * s ^ 4 + (23735 / 2 : ℂ) * s ^ 5 + (35475 / 8 : ℂ) * s ^ 6 + (7291 / 8 : ℂ) * s ^ 7 + (1331 / 16 : ℂ) * s ^ 8 + (5 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2802 : ℂ) * s + (-20879 / 2 : ℂ) * s ^ 2 + (-59389 / 8 : ℂ) * s ^ 3 + (-16307 / 16 : ℂ) * s ^ 4 + (1172 : ℂ) * s ^ 5 + (5979 / 8 : ℂ) * s ^ 6 + (1449 / 8 : ℂ) * s ^ 7 + (253 / 16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2562 : ℂ) * s + (-2428 : ℂ) * s ^ 2 + (-4787 : ℂ) * s ^ 3 + (-12583 / 4 : ℂ) * s ^ 4 + (-1242 : ℂ) * s ^ 5 + (-1075 / 4 : ℂ) * s ^ 6 + (-45 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((1806 : ℂ) * s + (1675 / 2 : ℂ) * s ^ 2 + (-571 / 4 : ℂ) * s ^ 3 + (-214 : ℂ) * s ^ 4 + (-187 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((216 : ℂ) * s + (36 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qtr1_lauI1_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qtr2_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qtr2_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((405 : ℂ) * s ^ 2 + (6723 / 4 : ℂ) * s ^ 3 + (23355 / 8 : ℂ) * s ^ 4 + (22233 / 8 : ℂ) * s ^ 5 + (1593 : ℂ) * s ^ 6 + (1131 / 2 : ℂ) * s ^ 7 + (975 / 8 : ℂ) * s ^ 8 + (117 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-216 : ℂ) * s + (-5193 / 2 : ℂ) * s ^ 2 + (-31035 / 4 : ℂ) * s ^ 3 + (-45049 / 4 : ℂ) * s ^ 4 + (-9368 : ℂ) * s ^ 5 + (-18857 / 4 : ℂ) * s ^ 6 + (-5753 / 4 : ℂ) * s ^ 7 + (-1017 / 4 : ℂ) * s ^ 8 + (-23 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((900 : ℂ) * s + (6168 : ℂ) * s ^ 2 + (53637 / 4 : ℂ) * s ^ 3 + (123767 / 8 : ℂ) * s ^ 4 + (86767 / 8 : ℂ) * s ^ 5 + (18597 / 4 : ℂ) * s ^ 6 + (2337 / 2 : ℂ) * s ^ 7 + (1247 / 8 : ℂ) * s ^ 8 + (67 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1428 : ℂ) * s + (-13849 / 2 : ℂ) * s ^ 2 + (-39285 / 4 : ℂ) * s ^ 3 + (-8345 : ℂ) * s ^ 4 + (-4714 : ℂ) * s ^ 5 + (-1649 : ℂ) * s ^ 6 + (-1243 / 4 : ℂ) * s ^ 7 + (-47 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1248 : ℂ) * s + (2918 : ℂ) * s ^ 2 + (2307 : ℂ) * s ^ 3 + (1079 : ℂ) * s ^ 4 + (424 : ℂ) * s ^ 5 + (121 : ℂ) * s ^ 6 + (15 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-396 : ℂ) * s + (48 : ℂ) * s ^ 2 + (177 : ℂ) * s ^ 3 + (138 : ℂ) * s ^ 4 + (33 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s + (-18 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qtr2_lauI1_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qt0_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qt0_lauI1 s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((81 : ℂ) * s ^ 2 + (513 / 2 : ℂ) * s ^ 3 + (2259 / 8 : ℂ) * s ^ 4 + (1485 / 16 : ℂ) * s ^ 5 + (-879 / 16 : ℂ) * s ^ 6 + (-465 / 8 : ℂ) * s ^ 7 + (-81 / 4 : ℂ) * s ^ 8 + (-51 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((216 : ℂ) * s + (603 / 4 : ℂ) * s ^ 2 + (-1149 / 2 : ℂ) * s ^ 3 + (-3567 / 4 : ℂ) * s ^ 4 + (-919 / 4 : ℂ) * s ^ 5 + (2879 / 8 : ℂ) * s ^ 6 + (1237 / 4 : ℂ) * s ^ 7 + (383 / 4 : ℂ) * s ^ 8 + (12 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((216 : ℂ) + (-306 : ℂ) * s + (-483 : ℂ) * s ^ 2 + (2687 / 2 : ℂ) * s ^ 3 + (18711 / 8 : ℂ) * s ^ 4 + (17797 / 16 : ℂ) * s ^ 5 + (-1235 / 16 : ℂ) * s ^ 6 + (-1975 / 8 : ℂ) * s ^ 7 + (-167 / 2 : ℂ) * s ^ 8 + (-159 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-558 : ℂ) + (768 : ℂ) * s + (2130 : ℂ) * s ^ 2 + (568 : ℂ) * s ^ 3 + (-996 : ℂ) * s ^ 4 + (-6263 / 8 : ℂ) * s ^ 5 + (-206 : ℂ) * s ^ 6 + (-17 / 4 : ℂ) * s ^ 7 + (8 : ℂ) * s ^ 8 + (9 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1608 : ℂ) + (752 : ℂ) * s + (-1053 : ℂ) * s ^ 2 + (-5307 / 4 : ℂ) * s ^ 3 + (-2781 / 4 : ℂ) * s ^ 4 + (-765 / 4 : ℂ) * s ^ 5 + (-87 / 4 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-912 : ℂ) + (-1096 : ℂ) * s + (-2931 / 4 : ℂ) * s ^ 2 + (-1039 / 4 : ℂ) * s ^ 3 + (-153 / 4 : ℂ) * s ^ 4 + (-5 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-336 : ℂ) + (-328 : ℂ) * s + (-93 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-18 : ℂ) + (-6 : ℂ) * s))))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qt0_lauI1_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qt1_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qt1_lauI1 s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-297 / 4 : ℂ) * s ^ 3 + (-1089 / 4 : ℂ) * s ^ 4 + (-6423 / 16 : ℂ) * s ^ 5 + (-4923 / 16 : ℂ) * s ^ 6 + (-1059 / 8 : ℂ) * s ^ 7 + (-255 / 8 : ℂ) * s ^ 8 + (-63 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((711 : ℂ) * s ^ 2 + (11175 / 4 : ℂ) * s ^ 3 + (35387 / 8 : ℂ) * s ^ 4 + (14711 / 4 : ℂ) * s ^ 5 + (14109 / 8 : ℂ) * s ^ 6 + (2017 / 4 : ℂ) * s ^ 7 + (685 / 8 : ℂ) * s ^ 8 + (33 / 4 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1080 : ℂ) * s + (1575 : ℂ) * s ^ 2 + (-5547 / 4 : ℂ) * s ^ 3 + (-17275 / 4 : ℂ) * s ^ 4 + (-58887 / 16 : ℂ) * s ^ 5 + (-25607 / 16 : ℂ) * s ^ 6 + (-3185 / 8 : ℂ) * s ^ 7 + (-461 / 8 : ℂ) * s ^ 8 + (-75 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-684 : ℂ) * s + (-2154 : ℂ) * s ^ 2 + (-7539 / 4 : ℂ) * s ^ 3 + (-4469 / 8 : ℂ) * s ^ 4 + (323 / 8 : ℂ) * s ^ 5 + (259 / 4 : ℂ) * s ^ 6 + (20 : ℂ) * s ^ 7 + (31 / 8 : ℂ) * s ^ 8 + (3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-360 : ℂ) * s + (-291 : ℂ) * s ^ 2 + (351 : ℂ) * s ^ 3 + (2557 / 4 : ℂ) * s ^ 4 + (1403 / 4 : ℂ) * s ^ 5 + (319 / 4 : ℂ) * s ^ 6 + (25 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-36 : ℂ) * s + (141 : ℂ) * s ^ 2 + (195 : ℂ) * s ^ 3 + (87 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((18 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qt1_lauI1_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qt2_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qt2_lauI1 s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((-135 : ℂ) * s ^ 2 + (-2061 / 4 : ℂ) * s ^ 3 + (-6411 / 8 : ℂ) * s ^ 4 + (-2637 / 4 : ℂ) * s ^ 5 + (-1245 / 4 : ℂ) * s ^ 6 + (-339 / 4 : ℂ) * s ^ 7 + (-99 / 8 : ℂ) * s ^ 8 + (-3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-108 : ℂ) * s + (369 / 2 : ℂ) * s ^ 2 + (5949 / 4 : ℂ) * s ^ 3 + (20273 / 8 : ℂ) * s ^ 4 + (8197 / 4 : ℂ) * s ^ 5 + (1813 / 2 : ℂ) * s ^ 6 + (224 : ℂ) * s ^ 7 + (231 / 8 : ℂ) * s ^ 8 + (3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((378 : ℂ) * s + (354 : ℂ) * s ^ 2 + (-5171 / 4 : ℂ) * s ^ 3 + (-22127 / 8 : ℂ) * s ^ 4 + (-2226 : ℂ) * s ^ 5 + (-1825 / 2 : ℂ) * s ^ 6 + (-395 / 2 : ℂ) * s ^ 7 + (-165 / 8 : ℂ) * s ^ 8 + (-3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-402 : ℂ) * s + (-740 : ℂ) * s ^ 2 + (479 / 4 : ℂ) * s ^ 3 + (8715 / 8 : ℂ) * s ^ 4 + (3729 / 4 : ℂ) * s ^ 5 + (701 / 2 : ℂ) * s ^ 6 + (62 : ℂ) * s ^ 7 + (33 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((102 : ℂ) * s + (346 : ℂ) * s ^ 2 + (263 : ℂ) * s ^ 3 + (-43 / 4 : ℂ) * s ^ 4 + (-349 / 4 : ℂ) * s ^ 5 + (-133 / 4 : ℂ) * s ^ 6 + (-15 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((30 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2 + (-59 : ℂ) * s ^ 3 + (-91 / 2 : ℂ) * s ^ 4 + (-9 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-9 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 3))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qt2_lauI1_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT0_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT0_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((72 : ℂ) * s + (267 : ℂ) * s ^ 2 + (405 : ℂ) * s ^ 3 + (1323 / 4 : ℂ) * s ^ 4 + (162 : ℂ) * s ^ 5 + (99 / 2 : ℂ) * s ^ 6 + (9 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-444 : ℂ) * s + (-2123 / 2 : ℂ) * s ^ 2 + (-2265 / 2 : ℂ) * s ^ 3 + (-654 : ℂ) * s ^ 4 + (-459 / 2 : ℂ) * s ^ 5 + (-75 : ℂ) * s ^ 6 + (-24 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((910 : ℂ) * s + (1601 : ℂ) * s ^ 2 + (623 : ℂ) * s ^ 3 + (-509 / 4 : ℂ) * s ^ 4 + (-109 : ℂ) * s ^ 5 + (-9 / 2 : ℂ) * s ^ 6 + (12 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1287 : ℂ) * s + (-731 / 2 : ℂ) * s ^ 2 + (275 / 2 : ℂ) * s ^ 3 + (79 / 2 : ℂ) * s ^ 4 + (-27 / 2 : ℂ) * s ^ 5 + (6 : ℂ) * s ^ 6 + (3 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((516 : ℂ) * s + (189 : ℂ) * s ^ 2 + (-74 : ℂ) * s ^ 3 + (-81 : ℂ) * s ^ 4 + (-14 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((221 : ℂ) * s + (126 : ℂ) * s ^ 2 + (5 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((12 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT0_lauI1_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT1_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT1_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-144 : ℂ) * s + (-597 : ℂ) * s ^ 2 + (-984 : ℂ) * s ^ 3 + (-3255 / 4 : ℂ) * s ^ 4 + (-693 / 2 : ℂ) * s ^ 5 + (-66 : ℂ) * s ^ 6 + (-3 / 2 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1788 : ℂ) * s + (6569 : ℂ) * s ^ 2 + (19315 / 2 : ℂ) * s ^ 3 + (14525 / 2 : ℂ) * s ^ 4 + (2925 : ℂ) * s ^ 5 + (572 : ℂ) * s ^ 6 + (59 / 2 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-5564 : ℂ) * s + (-15277 : ℂ) * s ^ 2 + (-15803 : ℂ) * s ^ 3 + (-30643 / 4 : ℂ) * s ^ 4 + (-3333 / 2 : ℂ) * s ^ 5 + (-73 : ℂ) * s ^ 6 + (51 / 2 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((5864 : ℂ) * s + (9209 : ℂ) * s ^ 2 + (8473 / 2 : ℂ) * s ^ 3 + (408 : ℂ) * s ^ 4 + (-167 : ℂ) * s ^ 5 + (-49 : ℂ) * s ^ 6 + (-11 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1036 : ℂ) * s + (1260 : ℂ) * s ^ 2 + (1357 : ℂ) * s ^ 3 + (384 : ℂ) * s ^ 4 + (35 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-836 : ℂ) * s + (-408 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-72 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT1_lauI1_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT2_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT2_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((-240 : ℂ) * s + (-761 : ℂ) * s ^ 2 + (-1747 / 2 : ℂ) * s ^ 3 + (-791 / 2 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5 + (125 / 2 : ℂ) * s ^ 6 + (20 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-652 : ℂ) * s + (-3251 : ℂ) * s ^ 2 + (-5966 : ℂ) * s ^ 3 + (-5335 : ℂ) * s ^ 4 + (-2521 : ℂ) * s ^ 5 + (-620 : ℂ) * s ^ 6 + (-69 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2958 : ℂ) * s + (9370 : ℂ) * s ^ 2 + (22283 / 2 : ℂ) * s ^ 3 + (12115 / 2 : ℂ) * s ^ 4 + (3079 / 2 : ℂ) * s ^ 5 + (305 / 2 : ℂ) * s ^ 6 + (1 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2166 : ℂ) * s + (-3645 : ℂ) * s ^ 2 + (-308 : ℂ) * s ^ 3 + (1164 : ℂ) * s ^ 4 + (454 : ℂ) * s ^ 5 + (45 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-626 : ℂ) * s + (-3333 : ℂ) * s ^ 2 + (-2380 : ℂ) * s ^ 3 + (-579 : ℂ) * s ^ 4 + (-50 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((618 : ℂ) * s + (108 : ℂ) * s ^ 2 + (-30 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((108 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT2_lauI1_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT3_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT3_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((360 : ℂ) * s + (1374 : ℂ) * s ^ 2 + (2137 : ℂ) * s ^ 3 + (1758 : ℂ) * s ^ 4 + (830 : ℂ) * s ^ 5 + (226 : ℂ) * s ^ 6 + (33 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1668 : ℂ) * s + (-5806 : ℂ) * s ^ 2 + (-8098 : ℂ) * s ^ 3 + (-5830 : ℂ) * s ^ 4 + (-2324 : ℂ) * s ^ 5 + (-506 : ℂ) * s ^ 6 + (-54 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3024 : ℂ) * s + (9320 : ℂ) * s ^ 2 + (11139 : ℂ) * s ^ 3 + (6618 : ℂ) * s ^ 4 + (2088 : ℂ) * s ^ 5 + (334 : ℂ) * s ^ 6 + (21 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2616 : ℂ) * s + (-6742 : ℂ) * s ^ 2 + (-6216 : ℂ) * s ^ 3 + (-2804 : ℂ) * s ^ 4 + (-624 : ℂ) * s ^ 5 + (-54 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((984 : ℂ) * s + (1710 : ℂ) * s ^ 2 + (1002 : ℂ) * s ^ 3 + (258 : ℂ) * s ^ 4 + (30 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-36 : ℂ) * s + (144 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-48 : ℂ) * s))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT3_lauI1_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewRadSrcFLam_lauI1 (s r : ℂ) : ℂ := (((48 : ℂ) * s + (337 : ℂ) * s ^ 2 + (1819 / 2 : ℂ) * s ^ 3 + (5261 / 4 : ℂ) * s ^ 4 + (9421 / 8 : ℂ) * s ^ 5 + (5677 / 8 : ℂ) * s ^ 6 + (1193 / 4 : ℂ) * s ^ 7 + (85 : ℂ) * s ^ 8 + (117 / 8 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-760 : ℂ) * s + (-17627 / 4 : ℂ) * s ^ 2 + (-10447 : ℂ) * s ^ 3 + (-100125 / 8 : ℂ) * s ^ 4 + (-34439 / 4 : ℂ) * s ^ 5 + (-3700 : ℂ) * s ^ 6 + (-4219 / 4 : ℂ) * s ^ 7 + (-1683 / 8 : ℂ) * s ^ 8 + (-59 / 2 : ℂ) * s ^ 9 + (-9 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((216 : ℂ) + (2984 : ℂ) * s + (13351 : ℂ) * s ^ 2 + (44187 / 2 : ℂ) * s ^ 3 + (19873 : ℂ) * s ^ 4 + (90681 / 8 : ℂ) * s ^ 5 + (33683 / 8 : ℂ) * s ^ 6 + (1014 : ℂ) * s ^ 7 + (321 / 2 : ℂ) * s ^ 8 + (139 / 8 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-558 : ℂ) + (-499 : ℂ) * s + (-7332 : ℂ) * s ^ 2 + (-11725 : ℂ) * s ^ 3 + (-67673 / 8 : ℂ) * s ^ 4 + (-7725 / 2 : ℂ) * s ^ 5 + (-4855 / 4 : ℂ) * s ^ 6 + (-257 : ℂ) * s ^ 7 + (-281 / 8 : ℂ) * s ^ 8 + (-5 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1608 : ℂ) + (-148 : ℂ) * s + (-1122 : ℂ) * s ^ 2 + (-2867 / 4 : ℂ) * s ^ 3 + (-935 / 4 : ℂ) * s ^ 4 + (-179 / 4 : ℂ) * s ^ 5 + (-25 / 4 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-912 : ℂ) + (-1291 : ℂ) * s + (-2973 / 4 : ℂ) * s ^ 2 + (-441 / 4 : ℂ) * s ^ 3 + (81 / 4 : ℂ) * s ^ 4 + (17 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-336 : ℂ) + (-328 : ℂ) * s + (-84 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-18 : ℂ) + (-6 : ℂ) * s))))))))))))))) / (r ^ 7 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3)

theorem skewRadSrcF_lauI1_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadSrcF_lauI1 s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = skewRadSrcFLam_lauI1 s r := by
  unfold skewRadSrcF_lauI1
  rw [skewRadPieceSF_qtr0_lauI1 s r hr hf hs hs3 hs1, skewRadPieceSF_qtr1_lauI1 s r hr hf hs hs3 hs1, skewRadPieceSF_qtr2_lauI1 s r hr hf hs hs3 hs1, skewRadPieceSF_qt0_lauI1 s r hr hf hs hs3 hs1, skewRadPieceSF_qt1_lauI1 s r hr hf hs hs3 hs1, skewRadPieceSF_qt2_lauI1 s r hr hf hs hs3 hs1, skewRadPieceSF_qT0_lauI1 s r hr hf hs hs3 hs1, skewRadPieceSF_qT1_lauI1 s r hr hf hs hs3 hs1, skewRadPieceSF_qT2_lauI1 s r hr hf hs hs3 hs1, skewRadPieceSF_qT3_lauI1 s r hr hf hs hs3 hs1]
  unfold skewRadSrcFLam_lauI1
  all_goals (try simp only [← add_div])
  ring

theorem skewRadPieceSF_qtr0_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qtr0_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-18 : ℂ) * s ^ 2 + (-885 / 8 : ℂ) * s ^ 3 + (-4401 / 16 : ℂ) * s ^ 4 + (-2895 / 8 : ℂ) * s ^ 5 + (-2187 / 8 : ℂ) * s ^ 6 + (-951 / 8 : ℂ) * s ^ 7 + (-441 / 16 : ℂ) * s ^ 8 + (-21 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((24 : ℂ) * s + (973 / 2 : ℂ) * s ^ 2 + (14935 / 8 : ℂ) * s ^ 3 + (52957 / 16 : ℂ) * s ^ 4 + (13471 / 4 : ℂ) * s ^ 5 + (16623 / 8 : ℂ) * s ^ 6 + (5935 / 8 : ℂ) * s ^ 7 + (2005 / 16 : ℂ) * s ^ 8 + (3 / 2 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-492 : ℂ) * s + (-6463 / 2 : ℂ) * s ^ 2 + (-50105 / 8 : ℂ) * s ^ 3 + (-89279 / 16 : ℂ) * s ^ 4 + (-17267 / 8 : ℂ) * s ^ 5 + (-229 / 8 : ℂ) * s ^ 6 + (2319 / 8 : ℂ) * s ^ 7 + (1969 / 16 : ℂ) * s ^ 8 + (185 / 8 : ℂ) * s ^ 9 + (3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((2142 : ℂ) * s + (4770 : ℂ) * s ^ 2 + (3991 / 8 : ℂ) * s ^ 3 + (-51413 / 16 : ℂ) * s ^ 4 + (-3021 : ℂ) * s ^ 5 + (-11019 / 8 : ℂ) * s ^ 6 + (-2619 / 8 : ℂ) * s ^ 7 + (-701 / 16 : ℂ) * s ^ 8 + (-4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1710 : ℂ) * s + (8247 / 2 : ℂ) * s ^ 2 + (19929 / 4 : ℂ) * s ^ 3 + (4947 / 2 : ℂ) * s ^ 4 + (2991 / 4 : ℂ) * s ^ 5 + (235 / 2 : ℂ) * s ^ 6 + (11 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2718 : ℂ) * s + (-2055 / 2 : ℂ) * s ^ 2 + (711 / 4 : ℂ) * s ^ 3 + (174 : ℂ) * s ^ 4 + (135 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-270 : ℂ) * s + (-45 : ℂ) * s ^ 2 + (15 : ℂ) * s ^ 3))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qtr0_lauI3_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qtr1_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qtr1_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((-90 : ℂ) * s ^ 2 + (-2553 / 8 : ℂ) * s ^ 3 + (-6537 / 16 : ℂ) * s ^ 4 + (-180 : ℂ) * s ^ 5 + (567 / 8 : ℂ) * s ^ 6 + (891 / 8 : ℂ) * s ^ 7 + (783 / 16 : ℂ) * s ^ 8 + (39 / 4 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((72 : ℂ) * s + (-765 : ℂ) * s ^ 2 + (-32923 / 8 : ℂ) * s ^ 3 + (-122111 / 16 : ℂ) * s ^ 4 + (-14799 / 2 : ℂ) * s ^ 5 + (-33915 / 8 : ℂ) * s ^ 6 + (-11767 / 8 : ℂ) * s ^ 7 + (-4687 / 16 : ℂ) * s ^ 8 + (-113 / 4 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((798 : ℂ) * s + (5039 : ℂ) * s ^ 2 + (78701 / 8 : ℂ) * s ^ 3 + (155861 / 16 : ℂ) * s ^ 4 + (22971 / 4 : ℂ) * s ^ 5 + (16933 / 8 : ℂ) * s ^ 6 + (3693 / 8 : ℂ) * s ^ 7 + (745 / 16 : ℂ) * s ^ 8 + (1 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1434 : ℂ) * s + (-7745 / 2 : ℂ) * s ^ 2 + (10121 / 8 : ℂ) * s ^ 3 + (94823 / 16 : ℂ) * s ^ 4 + (4913 : ℂ) * s ^ 5 + (15097 / 8 : ℂ) * s ^ 6 + (2675 / 8 : ℂ) * s ^ 7 + (327 / 16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((546 : ℂ) * s + (-5974 : ℂ) * s ^ 2 + (-7071 : ℂ) * s ^ 3 + (-15689 / 4 : ℂ) * s ^ 4 + (-1556 : ℂ) * s ^ 5 + (-1405 / 4 : ℂ) * s ^ 6 + (-55 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((2394 : ℂ) * s + (993 / 2 : ℂ) * s ^ 2 + (-2913 / 4 : ℂ) * s ^ 3 + (-594 : ℂ) * s ^ 4 + (-513 / 4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((648 : ℂ) * s + (108 : ℂ) * s ^ 2 + (-36 : ℂ) * s ^ 3))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qtr1_lauI3_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qtr2_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qtr2_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((270 : ℂ) * s ^ 2 + (4797 / 4 : ℂ) * s ^ 3 + (17907 / 8 : ℂ) * s ^ 4 + (18321 / 8 : ℂ) * s ^ 5 + (1404 : ℂ) * s ^ 6 + (528 : ℂ) * s ^ 7 + (951 / 8 : ℂ) * s ^ 8 + (117 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-144 : ℂ) * s + (-3231 / 2 : ℂ) * s ^ 2 + (-20441 / 4 : ℂ) * s ^ 3 + (-32193 / 4 : ℂ) * s ^ 4 + (-7333 : ℂ) * s ^ 5 + (-16141 / 4 : ℂ) * s ^ 6 + (-5319 / 4 : ℂ) * s ^ 7 + (-993 / 4 : ℂ) * s ^ 8 + (-23 : ℂ) * s ^ 9 + (-3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((516 : ℂ) * s + (3307 : ℂ) * s ^ 2 + (30451 / 4 : ℂ) * s ^ 3 + (77151 / 8 : ℂ) * s ^ 4 + (61207 / 8 : ℂ) * s ^ 5 + (15057 / 4 : ℂ) * s ^ 6 + (1064 : ℂ) * s ^ 7 + (1223 / 8 : ℂ) * s ^ 8 + (67 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-588 : ℂ) * s + (-5147 / 2 : ℂ) * s ^ 2 + (-14879 / 4 : ℂ) * s ^ 3 + (-3357 : ℂ) * s ^ 4 + (-2413 : ℂ) * s ^ 5 + (-1160 : ℂ) * s ^ 6 + (-1109 / 4 : ℂ) * s ^ 7 + (-47 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((216 : ℂ) * s + (-486 : ℂ) * s ^ 2 + (-681 : ℂ) * s ^ 3 + (-867 : ℂ) * s ^ 4 + (-288 : ℂ) * s ^ 5 + (27 : ℂ) * s ^ 6 + (15 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((324 : ℂ) * s + (1152 : ℂ) * s ^ 2 + (681 : ℂ) * s ^ 3 + (390 : ℂ) * s ^ 4 + (93 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-324 : ℂ) * s + (-54 : ℂ) * s ^ 2 + (18 : ℂ) * s ^ 3))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qtr2_lauI3_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qt0_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qt0_lauI3 s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((9 : ℂ) * s ^ 2 + (129 / 4 : ℂ) * s ^ 3 + (543 / 16 : ℂ) * s ^ 4 + (-21 / 2 : ℂ) * s ^ 5 + (-801 / 16 : ℂ) * s ^ 6 + (-171 / 4 : ℂ) * s ^ 7 + (-267 / 16 : ℂ) * s ^ 8 + (-3 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((24 : ℂ) * s + (37 / 2 : ℂ) * s ^ 2 + (-233 / 8 : ℂ) * s ^ 3 + (1353 / 16 : ℂ) * s ^ 4 + (5375 / 16 : ℂ) * s ^ 5 + (410 : ℂ) * s ^ 6 + (1007 / 4 : ℂ) * s ^ 7 + (1289 / 16 : ℂ) * s ^ 8 + (183 / 16 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((24 : ℂ) + (-46 : ℂ) * s + (360 : ℂ) * s ^ 2 + (9225 / 8 : ℂ) * s ^ 3 + (16749 / 16 : ℂ) * s ^ 4 + (1763 / 8 : ℂ) * s ^ 5 + (-3341 / 16 : ℂ) * s ^ 6 + (-1441 / 8 : ℂ) * s ^ 7 + (-1021 / 16 : ℂ) * s ^ 8 + (-75 / 8 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-84 : ℂ) + (989 : ℂ) * s + (2235 / 2 : ℂ) * s ^ 2 + (951 / 8 : ℂ) * s ^ 3 + (-6189 / 16 : ℂ) * s ^ 4 + (-4609 / 16 : ℂ) * s ^ 5 + (-901 / 8 : ℂ) * s ^ 6 + (-107 / 4 : ℂ) * s ^ 7 + (-1 / 16 : ℂ) * s ^ 8 + (15 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((924 : ℂ) + (203 : ℂ) * s + (-689 : ℂ) * s ^ 2 + (-7405 / 8 : ℂ) * s ^ 3 + (-1401 / 2 : ℂ) * s ^ 4 + (-1005 / 4 : ℂ) * s ^ 5 + (-77 / 2 : ℂ) * s ^ 6 + (-17 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-216 : ℂ) + (-747 : ℂ) * s + (-702 : ℂ) * s ^ 2 + (-669 / 2 : ℂ) * s ^ 3 + (-78 : ℂ) * s ^ 4 + (-13 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-612 : ℂ) + (-411 : ℂ) * s + (-114 : ℂ) * s ^ 2 + (-15 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-36 : ℂ) + (-12 : ℂ) * s))))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qt0_lauI3_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qt1_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qt1_lauI3 s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-189 / 4 : ℂ) * s ^ 3 + (-747 / 4 : ℂ) * s ^ 4 + (-4791 / 16 : ℂ) * s ^ 5 + (-4011 / 16 : ℂ) * s ^ 6 + (-939 / 8 : ℂ) * s ^ 7 + (-243 / 8 : ℂ) * s ^ 8 + (-63 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((477 : ℂ) * s ^ 2 + (7563 / 4 : ℂ) * s ^ 3 + (24655 / 8 : ℂ) * s ^ 4 + (10811 / 4 : ℂ) * s ^ 5 + (11197 / 8 : ℂ) * s ^ 6 + (1753 / 4 : ℂ) * s ^ 7 + (649 / 8 : ℂ) * s ^ 8 + (33 / 4 : ℂ) * s ^ 9 + (3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((720 : ℂ) * s + (1419 : ℂ) * s ^ 2 + (921 / 4 : ℂ) * s ^ 3 + (-6181 / 4 : ℂ) * s ^ 4 + (-28919 / 16 : ℂ) * s ^ 5 + (-15911 / 16 : ℂ) * s ^ 6 + (-2465 / 8 : ℂ) * s ^ 7 + (-425 / 8 : ℂ) * s ^ 8 + (-75 / 16 : ℂ) * s ^ 9 + (-3 / 16 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-36 : ℂ) * s + (-1038 : ℂ) * s ^ 2 + (-9255 / 4 : ℂ) * s ^ 3 + (-18473 / 8 : ℂ) * s ^ 4 + (-9349 / 8 : ℂ) * s ^ 5 + (-1133 / 4 : ℂ) * s ^ 6 + (-22 : ℂ) * s ^ 7 + (19 / 8 : ℂ) * s ^ 8 + (3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-576 : ℂ) * s + (-1083 : ℂ) * s ^ 2 + (-153 : ℂ) * s ^ 3 + (3033 / 4 : ℂ) * s ^ 4 + (2159 / 4 : ℂ) * s ^ 5 + (515 / 4 : ℂ) * s ^ 6 + (37 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-108 : ℂ) * s + (171 : ℂ) * s ^ 2 + (375 : ℂ) * s ^ 3 + (201 : ℂ) * s ^ 4 + (33 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((54 : ℂ) * s ^ 2 + (18 : ℂ) * s ^ 3))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qt1_lauI3_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qt2_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qt2_lauI3 s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((-90 : ℂ) * s ^ 2 + (-1479 / 4 : ℂ) * s ^ 3 + (-4983 / 8 : ℂ) * s ^ 4 + (-2223 / 4 : ℂ) * s ^ 5 + (-1131 / 4 : ℂ) * s ^ 6 + (-327 / 4 : ℂ) * s ^ 7 + (-99 / 8 : ℂ) * s ^ 8 + (-3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-72 : ℂ) * s + (99 / 2 : ℂ) * s ^ 2 + (3485 / 4 : ℂ) * s ^ 3 + (14105 / 8 : ℂ) * s ^ 4 + (6521 / 4 : ℂ) * s ^ 5 + (1609 / 2 : ℂ) * s ^ 6 + (215 : ℂ) * s ^ 7 + (231 / 8 : ℂ) * s ^ 8 + (3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((210 : ℂ) * s + (418 : ℂ) * s ^ 2 + (-1147 / 4 : ℂ) * s ^ 3 + (-11703 / 8 : ℂ) * s ^ 4 + (-1575 : ℂ) * s ^ 5 + (-1555 / 2 : ℂ) * s ^ 6 + (-377 / 2 : ℂ) * s ^ 7 + (-165 / 8 : ℂ) * s ^ 8 + (-3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-114 : ℂ) * s + (-554 : ℂ) * s ^ 2 + (-2605 / 4 : ℂ) * s ^ 3 + (171 / 8 : ℂ) * s ^ 4 + (1833 / 4 : ℂ) * s ^ 5 + (545 / 2 : ℂ) * s ^ 6 + (59 : ℂ) * s ^ 7 + (33 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-114 : ℂ) * s + (79 : ℂ) * s ^ 2 + (1035 / 2 : ℂ) * s ^ 3 + (1631 / 4 : ℂ) * s ^ 4 + (265 / 4 : ℂ) * s ^ 5 + (-67 / 4 : ℂ) * s ^ 6 + (-15 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((90 : ℂ) * s + (249 / 2 : ℂ) * s ^ 2 + (-72 : ℂ) * s ^ 3 + (-213 / 2 : ℂ) * s ^ 4 + (-24 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-27 : ℂ) * s ^ 2 + (-9 : ℂ) * s ^ 3))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qt2_lauI3_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT0_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT0_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((8 : ℂ) * s + (32 : ℂ) * s ^ 2 + (205 / 4 : ℂ) * s ^ 3 + (175 / 4 : ℂ) * s ^ 4 + (49 / 2 : ℂ) * s ^ 5 + (23 / 2 : ℂ) * s ^ 6 + (17 / 4 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-60 : ℂ) * s + (-151 / 2 : ℂ) * s ^ 2 + (315 / 4 : ℂ) * s ^ 3 + (168 : ℂ) * s ^ 4 + (85 : ℂ) * s ^ 5 + (3 : ℂ) * s ^ 6 + (-47 / 4 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((279 : ℂ) * s + (4 : ℂ) * s ^ 2 + (-2337 / 4 : ℂ) * s ^ 3 + (-2705 / 4 : ℂ) * s ^ 4 + (-585 / 2 : ℂ) * s ^ 5 + (-93 / 2 : ℂ) * s ^ 6 + (7 / 4 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-704 : ℂ) * s + (817 / 2 : ℂ) * s ^ 2 + (1865 / 4 : ℂ) * s ^ 3 + (95 / 2 : ℂ) * s ^ 4 + (8 : ℂ) * s ^ 5 + (8 : ℂ) * s ^ 6 + (23 / 4 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((39 : ℂ) * s + (267 : ℂ) * s ^ 2 + (-66 : ℂ) * s ^ 3 + (-75 : ℂ) * s ^ 4 + (-29 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((414 : ℂ) * s + (120 : ℂ) * s ^ 2 + (18 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((24 : ℂ) * s))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT0_lauI3_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT1_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT1_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-16 : ℂ) * s + (-135 : ℂ) * s ^ 2 + (-355 : ℂ) * s ^ 3 + (-1715 / 4 : ℂ) * s ^ 4 + (-519 / 2 : ℂ) * s ^ 5 + (-73 : ℂ) * s ^ 6 + (-11 / 2 : ℂ) * s ^ 7 + (3 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((840 : ℂ) * s + (3355 : ℂ) * s ^ 2 + (10737 / 2 : ℂ) * s ^ 3 + (8919 / 2 : ℂ) * s ^ 4 + (2054 : ℂ) * s ^ 5 + (489 : ℂ) * s ^ 6 + (75 / 2 : ℂ) * s ^ 7 + (-7 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-2788 : ℂ) * s + (-7243 : ℂ) * s ^ 2 + (-7034 : ℂ) * s ^ 3 + (-12807 / 4 : ℂ) * s ^ 4 + (-1199 / 2 : ℂ) * s ^ 5 + (18 : ℂ) * s ^ 6 + (43 / 2 : ℂ) * s ^ 7 + (11 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1920 : ℂ) * s + (755 : ℂ) * s ^ 2 + (-4125 / 2 : ℂ) * s ^ 3 + (-1761 : ℂ) * s ^ 4 + (-468 : ℂ) * s ^ 5 + (-50 : ℂ) * s ^ 6 + (-11 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((1556 : ℂ) * s + (4396 : ℂ) * s ^ 2 + (2523 : ℂ) * s ^ 3 + (512 : ℂ) * s ^ 4 + (53 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-1320 : ℂ) * s + (-372 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-192 : ℂ) * s))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT1_lauI3_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT2_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT2_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((-160 : ℂ) * s + (-559 : ℂ) * s ^ 2 + (-1461 / 2 : ℂ) * s ^ 3 + (-821 / 2 : ℂ) * s ^ 4 + (-103 / 2 : ℂ) * s ^ 5 + (87 / 2 : ℂ) * s ^ 6 + (18 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-528 : ℂ) * s + (-2321 : ℂ) * s ^ 2 + (-4091 : ℂ) * s ^ 3 + (-3750 : ℂ) * s ^ 4 + (-1912 : ℂ) * s ^ 5 + (-523 : ℂ) * s ^ 6 + (-65 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1734 : ℂ) * s + (4912 : ℂ) * s ^ 2 + (10633 / 2 : ℂ) * s ^ 3 + (5433 / 2 : ℂ) * s ^ 4 + (1325 / 2 : ℂ) * s ^ 5 + (127 / 2 : ℂ) * s ^ 6 + (-1 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-254 : ℂ) * s + (1565 : ℂ) * s ^ 2 + (4401 : ℂ) * s ^ 3 + (3055 : ℂ) * s ^ 4 + (785 : ℂ) * s ^ 5 + (56 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-1458 : ℂ) * s + (-4677 : ℂ) * s ^ 2 + (-3114 : ℂ) * s ^ 3 + (-699 : ℂ) * s ^ 4 + (-60 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((342 : ℂ) * s + (-432 : ℂ) * s ^ 2 + (-198 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((324 : ℂ) * s))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT2_lauI3_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewRadPieceSF_qT3_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadQF_qT3_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((240 : ℂ) * s + (986 : ℂ) * s ^ 2 + (1661 : ℂ) * s ^ 3 + (1482 : ℂ) * s ^ 4 + (754 : ℂ) * s ^ 5 + (218 : ℂ) * s ^ 6 + (33 : ℂ) * s ^ 7 + (2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-972 : ℂ) * s + (-3754 : ℂ) * s ^ 2 + (-5862 : ℂ) * s ^ 3 + (-4730 : ℂ) * s ^ 4 + (-2088 : ℂ) * s ^ 5 + (-490 : ℂ) * s ^ 6 + (-54 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1344 : ℂ) * s + (4916 : ℂ) * s ^ 2 + (7063 : ℂ) * s ^ 3 + (5030 : ℂ) * s ^ 4 + (1844 : ℂ) * s ^ 5 + (326 : ℂ) * s ^ 6 + (21 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-456 : ℂ) * s + (-1914 : ℂ) * s ^ 2 + (-2748 : ℂ) * s ^ 3 + (-1824 : ℂ) * s ^ 4 + (-540 : ℂ) * s ^ 5 + (-54 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-576 : ℂ) * s + (-1002 : ℂ) * s ^ 2 + (-270 : ℂ) * s ^ 3 + (42 : ℂ) * s ^ 4 + (30 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((564 : ℂ) * s + (768 : ℂ) * s ^ 2 + (156 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-144 : ℂ) * s))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewRadQF_qT3_lauI3_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewRadSrcFLam_lauI3 (s r : ℂ) : ℂ := (((72 : ℂ) * s + (405 : ℂ) * s ^ 2 + (2023 / 2 : ℂ) * s ^ 3 + (23449 / 16 : ℂ) * s ^ 4 + (21601 / 16 : ℂ) * s ^ 5 + (818 : ℂ) * s ^ 6 + (2627 / 8 : ℂ) * s ^ 7 + (1381 / 16 : ℂ) * s ^ 8 + (225 / 16 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-816 : ℂ) * s + (-8289 / 2 : ℂ) * s ^ 2 + (-73053 / 8 : ℂ) * s ^ 3 + (-180693 / 16 : ℂ) * s ^ 4 + (-136909 / 16 : ℂ) * s ^ 5 + (-32829 / 8 : ℂ) * s ^ 6 + (-1247 : ℂ) * s ^ 7 + (-3781 / 16 : ℂ) * s ^ 8 + (-457 / 16 : ℂ) * s ^ 9 + (-9 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((24 : ℂ) + (2275 : ℂ) * s + (19801 / 2 : ℂ) * s ^ 2 + (136361 / 8 : ℂ) * s ^ 3 + (251399 / 16 : ℂ) * s ^ 4 + (155003 / 16 : ℂ) * s ^ 5 + (8465 / 2 : ℂ) * s ^ 6 + (1182 : ℂ) * s ^ 7 + (3047 / 16 : ℂ) * s ^ 8 + (275 / 16 : ℂ) * s ^ 9 + (9 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-84 : ℂ) + (1465 : ℂ) * s + (-1336 : ℂ) * s ^ 2 + (-37961 / 8 : ℂ) * s ^ 3 + (-60815 / 16 : ℂ) * s ^ 4 + (-27751 / 16 : ℂ) * s ^ 5 + (-6509 / 8 : ℂ) * s ^ 6 + (-1039 / 4 : ℂ) * s ^ 7 + (-647 / 16 : ℂ) * s ^ 8 + (-43 / 16 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((924 : ℂ) + (-1874 : ℂ) * s + (-10091 / 2 : ℂ) * s ^ 2 + (-34063 / 8 : ℂ) * s ^ 3 + (-8281 / 4 : ℂ) * s ^ 4 + (-1495 / 2 : ℂ) * s ^ 5 + (-533 / 4 : ℂ) * s ^ 6 + (-29 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-216 : ℂ) + (-765 : ℂ) * s + (597 / 2 : ℂ) * s ^ 2 + (87 : ℂ) * s ^ 3 + (-27 / 2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-612 : ℂ) + (-345 : ℂ) * s + (-78 : ℂ) * s ^ 2 + (-9 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-36 : ℂ) + (-12 : ℂ) * s))))))))))))))) / (r ^ 9 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3)

theorem skewRadSrcF_lauI3_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewRadSrcF_lauI3 s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = skewRadSrcFLam_lauI3 s r := by
  unfold skewRadSrcF_lauI3
  rw [skewRadPieceSF_qtr0_lauI3 s r hr hf hs hs3 hs1, skewRadPieceSF_qtr1_lauI3 s r hr hf hs hs3 hs1, skewRadPieceSF_qtr2_lauI3 s r hr hf hs hs3 hs1, skewRadPieceSF_qt0_lauI3 s r hr hf hs hs3 hs1, skewRadPieceSF_qt1_lauI3 s r hr hf hs hs3 hs1, skewRadPieceSF_qt2_lauI3 s r hr hf hs hs3 hs1, skewRadPieceSF_qT0_lauI3 s r hr hf hs hs3 hs1, skewRadPieceSF_qT1_lauI3 s r hr hf hs hs3 hs1, skewRadPieceSF_qT2_lauI3 s r hr hf hs hs3 hs1, skewRadPieceSF_qT3_lauI3 s r hr hf hs hs3 hs1]
  unfold skewRadSrcFLam_lauI3
  all_goals (try simp only [← add_div])
  ring

end
end RHTower.D4BMScalarStream
