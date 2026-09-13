import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorBoundaryFlux

/-!
# The two-rate onset current at the fundamental harmonic: family and family/source pieces

At the fundamental harmonic `μ = (s+1)(s+2)`, with the Laurent coefficients of the `++` response
(half-rate `s`) and of the `−−` response (half-rate `−3−s`) at their actual values, the two-rate
onset current `skewOnsetSS` is an explicit rational function of `r` (`skewOnsetSS_eq`). Its
coordinate density `r²·(current)` is `N(s,r)/(r⁶(r²−1)·s(s+3))` with `N` even of degree eight
(`skewDensitySS_eq`), a Laurent polynomial in `u = 1/r` once the horizon factor and the Jacobian
are extracted (`skewDensitySS_substitution`). The two responses carry the envelope
`z^{s}·z^{−3−s} = z^{−3}`, an integer power, so the radial integral of the dressed density
`z^{−3}·r²·(current)` over the exterior has a logarithmic horizon divergence; its coefficient is
the finite binomial sum of the Laurent coefficients recorded in `skewLogCoeff_eq`, the rational
function `skewLogCoeff`. This coefficient is odd under the reflection `s ↦ −3−s`
(`skewLogCoeff_reflect`), hence purely imaginary on the critical line `s = −3/2 + it`, and its
difference at two points factors through the difference of the points
(`skewLogCoeff_sub`): the real part off the line is the tilt `Re ρ − 1/2` times an explicit
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

theorem skewFF_lauR_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauR_lauR s r ((s + 1) * (s + 2)) = (((-576 : ℂ) * s + (-1179 / 2 : ℂ) * s ^ 2 + (-146 : ℂ) * s ^ 3 + (-15 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-1056 : ℂ) + (-632 : ℂ) * s + (171 / 2 : ℂ) * s ^ 2 + (34 : ℂ) * s ^ 3 + (15 / 2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((444 : ℂ) + (296 : ℂ) * s) + r * ((0 : ℂ) + r * ((-60 : ℂ) + (-40 : ℂ) * s))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewFF_lauR_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauR_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauR_lauI1 s r ((s + 1) * (s + 2)) = (((-220 : ℂ) * s + (15 / 2 : ℂ) * s ^ 2 + (-9 / 2 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-216 : ℂ) + (-82 : ℂ) * s + (17 / 2 : ℂ) * s ^ 2 + (9 / 2 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-20 : ℂ) + (6 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))) / (r ^ 2 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3)) := by
  unfold skewFF_lauR_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauR_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauR_lauI3 s r ((s + 1) * (s + 2)) = (((-464 : ℂ) * s + (-235 / 2 : ℂ) * s ^ 2 + (70 : ℂ) * s ^ 3 + (-15 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-336 : ℂ) + (-740 : ℂ) * s + (211 / 2 : ℂ) * s ^ 2 + (74 : ℂ) * s ^ 3 + (15 / 2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-372 : ℂ) + (-68 : ℂ) * s + (20 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((36 : ℂ)))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewFF_lauR_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI1_lauR s r ((s + 1) * (s + 2)) = (((768 : ℂ) + (557 / 2 : ℂ) * s + (-6 : ℂ) * s ^ 2 + (-15 / 2 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((66 : ℂ) + (239 / 2 : ℂ) * s + (22 : ℂ) * s ^ 2 + (15 / 2 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-38 : ℂ) + (-6 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))) / (r ^ 2 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 2) := by
  unfold skewFF_lauI1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI1_lauI1 s r ((s + 1) * (s + 2)) = (((132 : ℂ) + (167 / 2 : ℂ) * s + (-9 / 2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((84 : ℂ) + (121 / 2 : ℂ) * s + (9 / 2 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3))) / (r ^ 4 * (r ^ 2 - 1) ^ 2 * s * (s + 3)) := by
  unfold skewFF_lauI1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI1_lauI3 s r ((s + 1) * (s + 2)) = (((144 : ℂ) + (477 / 2 : ℂ) * s + (82 : ℂ) * s ^ 2 + (-15 / 2 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((374 : ℂ) + (1175 / 2 : ℂ) * s + (190 : ℂ) * s ^ 2 + (15 / 2 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-18 : ℂ) + (78 : ℂ) * s) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 2) := by
  unfold skewFF_lauI1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI3_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI3_lauR s r ((s + 1) * (s + 2)) = (((1920 : ℂ) + (2536 : ℂ) * s + (1765 / 2 : ℂ) * s ^ 2 + (70 : ℂ) * s ^ 3 + (-15 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-1200 : ℂ) + (220 : ℂ) * s + (851 / 2 : ℂ) * s ^ 2 + (74 : ℂ) * s ^ 3 + (15 / 2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-188 : ℂ) * s + (-20 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-36 : ℂ)))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewFF_lauI3_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI3_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI3_lauI1 s r ((s + 1) * (s + 2)) = (((288 : ℂ) + (348 : ℂ) * s + (191 / 2 : ℂ) * s ^ 2 + (-9 / 2 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((200 : ℂ) + (458 : ℂ) * s + (353 / 2 : ℂ) * s ^ 2 + (9 / 2 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-252 : ℂ) + (-78 : ℂ) * s) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3)) := by
  unfold skewFF_lauI3_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI3_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI3_lauI3 s r ((s + 1) * (s + 2)) = (((192 : ℂ) + (344 : ℂ) * s + (405 / 2 : ℂ) * s ^ 2 + (30 : ℂ) * s ^ 3 + (-15 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1344 : ℂ) + (2480 : ℂ) * s + (3195 / 2 : ℂ) * s ^ 2 + (370 : ℂ) * s ^ 3 + (15 / 2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-540 : ℂ) + (-360 : ℂ) * s) + r * ((0 : ℂ) + r * ((-324 : ℂ) + (-216 : ℂ) * s))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewFF_lauI3_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qt0 s r ((s + 1) * (s + 2)) = (((-216 : ℂ) * s + (129 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 3 + (-51 : ℂ) * s ^ 4 + (-10 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-120 : ℂ) + (222 : ℂ) * s + (175 : ℂ) * s ^ 2 + (-46 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((240 : ℂ) + (10 : ℂ) * s + (-140 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-120 : ℂ) + (-80 : ℂ) * s))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewFQ_lauR_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-107 : ℂ) * s + (73 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3 + (-16 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-72 : ℂ) + (82 : ℂ) * s + (108 : ℂ) * s ^ 2 + (-46 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((144 : ℂ) + (53 : ℂ) * s + (-93 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (-60 : ℂ) * s)))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewFQ_lauR_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qT0 s r ((s + 1) * (s + 2)) = (((360 : ℂ) * s + (-177 : ℂ) * s ^ 2 + (-36 : ℂ) * s ^ 3 + (51 : ℂ) * s ^ 4 + (10 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((240 : ℂ) + (-428 : ℂ) * s + (-284 : ℂ) * s ^ 2 + (70 : ℂ) * s ^ 3 + (-26 : ℂ) * s ^ 4 + (-12 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-552 : ℂ) + (76 : ℂ) * s + (375 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((432 : ℂ) + (168 : ℂ) * s + (-122 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-120 : ℂ) + (-80 : ℂ) * s))))))))) / ((r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewFQ_lauR_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-282 : ℂ) * s + (90 : ℂ) * s ^ 2 + (84 : ℂ) * s ^ 3 + (-28 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-192 : ℂ) + (154 : ℂ) * s + (364 : ℂ) * s ^ 2 + (-130 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((360 : ℂ) + (208 : ℂ) * s + (-262 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-168 : ℂ) + (-160 : ℂ) * s)))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewFQ_lauR_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qt0 s r ((s + 1) * (s + 2)) = (((12 : ℂ) + (-47 : ℂ) * s + (-128 : ℂ) * s ^ 2 + (-67 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-114 : ℂ) + (187 : ℂ) * s + (78 : ℂ) * s ^ 2 + (23 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((14 : ℂ) + (24 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))) / (r ^ 2 * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  unfold skewFQ_lauI1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qtr0 s r ((s + 1) * (s + 2)) = (((21 : ℂ) + (-7 : ℂ) * s + (-42 : ℂ) * s ^ 2 + (-16 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-82 : ℂ) + (92 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((5 : ℂ) + (3 : ℂ) * s) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))) / (r * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 3) := by
  unfold skewFQ_lauI1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qT0 s r ((s + 1) * (s + 2)) = (((-24 : ℂ) + (67 : ℂ) * s + (136 : ℂ) * s ^ 2 + (67 : ℂ) * s ^ 3 + (10 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((144 : ℂ) + (-408 : ℂ) * s + (-170 : ℂ) * s ^ 2 + (-58 : ℂ) * s ^ 3 + (-12 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-20 : ℂ) + (115 : ℂ) * s + (48 : ℂ) * s ^ 2 + (23 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-28 : ℂ) + (18 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))))) / (r ^ 2 * (r ^ 2 - 1) ^ 3 * s * (s + 3) ^ 2) := by
  unfold skewFQ_lauI1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qT1 s r ((s + 1) * (s + 2)) = (((102 : ℂ) + (70 : ℂ) * s + (-8 : ℂ) * s ^ 2 + (-28 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-270 : ℂ) + (116 : ℂ) * s + (-42 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((16 : ℂ) + (6 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((72 : ℂ)))))))) / (r * (r ^ 2 - 1) ^ 2 * s * (s + 3) ^ 2) := by
  unfold skewFQ_lauI1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qt0 s r ((s + 1) * (s + 2)) = (((-96 : ℂ) + (-368 : ℂ) * s + (-463 : ℂ) * s ^ 2 + (-276 : ℂ) * s ^ 3 + (-83 : ℂ) * s ^ 4 + (-10 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((120 : ℂ) + (638 : ℂ) * s + (679 : ℂ) * s ^ 2 + (234 : ℂ) * s ^ 3 + (39 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((48 : ℂ) + (-334 : ℂ) * s + (-52 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-72 : ℂ)))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewFQ_lauI3_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qtr0 s r ((s + 1) * (s + 2)) = (((-123 : ℂ) * s + (-183 : ℂ) * s ^ 2 + (-90 : ℂ) * s ^ 3 + (-16 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-72 : ℂ) + (202 : ℂ) * s + (268 : ℂ) * s ^ 2 + (50 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((144 : ℂ) + (-123 : ℂ) * s + (3 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (12 : ℂ) * s))))))) / (r ^ 3 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewFQ_lauI3_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qT0 s r ((s + 1) * (s + 2)) = (((192 : ℂ) + (664 : ℂ) * s + (695 : ℂ) * s ^ 2 + (324 : ℂ) * s ^ 3 + (83 : ℂ) * s ^ 4 + (10 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-528 : ℂ) + (-1764 : ℂ) * s + (-1492 : ℂ) * s ^ 2 + (-458 : ℂ) * s ^ 3 + (-90 : ℂ) * s ^ 4 + (-12 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((360 : ℂ) + (1500 : ℂ) * s + (623 : ℂ) * s ^ 2 + (156 : ℂ) * s ^ 3 + (39 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((48 : ℂ) + (-304 : ℂ) * s + (-34 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-72 : ℂ)))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewFQ_lauI3_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qT1 s r ((s + 1) * (s + 2)) = (((192 : ℂ) + (70 : ℂ) * s + (-142 : ℂ) * s ^ 2 + (-100 : ℂ) * s ^ 3 + (-28 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-576 : ℂ) + (-118 : ℂ) * s + (252 : ℂ) * s ^ 2 + (46 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((600 : ℂ) + (-80 : ℂ) * s + (82 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-216 : ℂ) + (48 : ℂ) * s))))))) / (r ^ 3 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewFQ_lauI3_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((34 : ℂ) * s + (34 : ℂ) * s ^ 2 + (-40 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((24 : ℂ) + (38 : ℂ) * s + (-76 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-24 : ℂ) + (-40 : ℂ) * s)))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewFQ_lauR_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((9 : ℂ) * s + (19 : ℂ) * s ^ 2 + (-16 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((12 : ℂ) + (31 : ℂ) * s + (-43 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-12 : ℂ) + (-24 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewFQ_lauR_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((2 : ℂ) * s + (54 : ℂ) * s ^ 2 + (-32 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((24 : ℂ) + (78 : ℂ) * s + (-94 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-24 : ℂ) + (-52 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewFQ_lauR_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qt1 s r ((s + 1) * (s + 2)) = (((-30 : ℂ) + (-42 : ℂ) * s + (-44 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((38 : ℂ) + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ)))))) / (r * (r ^ 2 - 1) * s * (s + 3) ^ 3) := by
  unfold skewFQ_lauI1_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qtr1 s r ((s + 1) * (s + 2)) = (((-15 : ℂ) + (-13 : ℂ) * s + (-16 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((15 : ℂ) + (-11 : ℂ) * s) + r * ((0 : ℂ) + r * ((16 : ℂ)))))) / ((r ^ 2 - 1) * s * (s + 3) ^ 3) := by
  unfold skewFQ_lauI1_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qT2 s r ((s + 1) * (s + 2)) = (((-30 : ℂ) + (-10 : ℂ) * s + (-32 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((22 : ℂ) + (-30 : ℂ) * s) + r * ((0 : ℂ) + r * ((36 : ℂ)))))) / ((r ^ 2 - 1) * s * (s + 3) ^ 2) := by
  unfold skewFQ_lauI1_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qt1 s r ((s + 1) * (s + 2)) = (((-96 : ℂ) + (-158 : ℂ) * s + (-118 : ℂ) * s ^ 2 + (-48 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((168 : ℂ) + (166 : ℂ) * s + (76 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (24 : ℂ) * s))))) / (r ^ 3 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewFQ_lauI3_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qtr1 s r ((s + 1) * (s + 2)) = (((-48 : ℂ) + (-71 : ℂ) * s + (-45 : ℂ) * s ^ 2 + (-16 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((84 : ℂ) + (63 : ℂ) * s + (21 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-36 : ℂ) + (24 : ℂ) * s))))) / (r ^ 2 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewFQ_lauI3_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qT2 s r ((s + 1) * (s + 2)) = (((-96 : ℂ) + (-126 : ℂ) * s + (-74 : ℂ) * s ^ 2 + (-32 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((168 : ℂ) + (94 : ℂ) * s + (34 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (60 : ℂ) * s))))) / (r ^ 2 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewFQ_lauI3_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-4 : ℂ)))))) / (s * (s + 3) ^ 3) := by
  unfold skewFQ_lauR_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((4 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((-2 : ℂ))))))) / (s * (s + 3) ^ 3) := by
  unfold skewFQ_lauR_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-4 : ℂ))))))) / (s * (s + 3) ^ 2) := by
  unfold skewFQ_lauR_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qt2 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((4 : ℂ)))) / (s * (s + 3) ^ 3) := by
  unfold skewFQ_lauI1_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((2 : ℂ))))) / (s * (s + 3) ^ 3) := by
  unfold skewFQ_lauI1_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((4 : ℂ))))) / (s * (s + 3) ^ 2) := by
  unfold skewFQ_lauI1_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qt2 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ)))) / (r ^ 2 * s * (s + 3) ^ 3) := by
  unfold skewFQ_lauI3_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qtr2 s r ((s + 1) * (s + 2)) = (((-4 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((6 : ℂ)))) / (r * s * (s + 3) ^ 3) := by
  unfold skewFQ_lauI3_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qT3 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ)))) / (r * s * (s + 3) ^ 2) := by
  unfold skewFQ_lauI3_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt0_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt0_lauR s r ((s + 1) * (s + 2)) = (((-576 : ℂ) * s + (39 : ℂ) * s ^ 2 + (284 : ℂ) * s ^ 3 + (99 : ℂ) * s ^ 4 + (10 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((2112 : ℂ) + (2016 : ℂ) * s + (427 : ℂ) * s ^ 2 + (-50 : ℂ) * s ^ 3 + (-23 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-888 : ℂ) + (-688 : ℂ) * s + (-86 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((120 : ℂ) + (80 : ℂ) * s))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQF_qt0_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt1_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((960 : ℂ) + (818 : ℂ) * s + (178 : ℂ) * s ^ 2 + (-8 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-720 : ℂ) + (-440 : ℂ) * s + (-58 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((96 : ℂ) + (40 : ℂ) * s)))))) / ((r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQF_qt1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr0_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr0_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-480 : ℂ) + (-1345 : ℂ) * s + (-845 : ℂ) * s ^ 2 + (-198 : ℂ) * s ^ 3 + (-16 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((1896 : ℂ) + (1808 : ℂ) * s + (522 : ℂ) * s ^ 2 + (46 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-852 : ℂ) + (-611 : ℂ) * s + (-93 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((108 : ℂ) + (60 : ℂ) * s)))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQF_qtr0_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr1_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((576 : ℂ) + (537 : ℂ) * s + (163 : ℂ) * s ^ 2 + (16 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-468 : ℂ) + (-289 : ℂ) * s + (-43 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((60 : ℂ) + (24 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQF_qtr1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT0_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT0_lauR s r ((s + 1) * (s + 2)) = (((-1008 : ℂ) * s + (-201 : ℂ) * s ^ 2 + (252 : ℂ) * s ^ 3 + (99 : ℂ) * s ^ 4 + (10 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((2112 : ℂ) + (1114 : ℂ) * s + (-922 : ℂ) * s ^ 2 + (-698 : ℂ) * s ^ 3 + (-154 : ℂ) * s ^ 4 + (-12 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-3000 : ℂ) + (-2444 : ℂ) * s + (-321 : ℂ) * s ^ 2 + (84 : ℂ) * s ^ 3 + (23 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1008 : ℂ) + (738 : ℂ) * s + (68 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-120 : ℂ) + (-80 : ℂ) * s))))))))) / ((r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQF_qT0_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT1_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((2880 : ℂ) + (4470 : ℂ) * s + (2178 : ℂ) * s ^ 2 + (420 : ℂ) * s ^ 3 + (28 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-5808 : ℂ) + (-5108 : ℂ) * s + (-1318 : ℂ) * s ^ 2 + (-82 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((2568 : ℂ) + (1726 : ℂ) * s + (244 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-312 : ℂ) + (-160 : ℂ) * s)))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQF_qT1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT2_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT2_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-1344 : ℂ) + (-1186 : ℂ) * s + (-342 : ℂ) * s ^ 2 + (-32 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((1056 : ℂ) + (642 : ℂ) * s + (94 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-132 : ℂ) + (-52 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQF_qT2_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt0_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt0_lauI1 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) * s + (65 : ℂ) * s ^ 2 + (53 : ℂ) * s ^ 3 + (10 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((432 : ℂ) + (124 : ℂ) * s + (21 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((40 : ℂ) + (12 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))) / (r ^ 2 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3)) := by
  unfold skewQF_qt0_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt1_lauI1 s r ((s + 1) * (s + 2)) = (((192 : ℂ) + (114 : ℂ) * s + (8 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-56 : ℂ) + (-12 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))) / (r * (r ^ 2 - 1) * s ^ 3 * (s + 3)) := by
  unfold skewQF_qt1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr0_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr0_lauI1 s r ((s + 1) * (s + 2)) = (((-96 : ℂ) + (-187 : ℂ) * s + (-102 : ℂ) * s ^ 2 + (-16 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((340 : ℂ) + (80 : ℂ) * s + (-2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((4 : ℂ) + (3 : ℂ) * s) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))) / (r * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3)) := by
  unfold skewQF_qtr0_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr1_lauI1 s r ((s + 1) * (s + 2)) = (((120 : ℂ) + (83 : ℂ) * s + (16 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((-48 : ℂ) + (-11 : ℂ) * s) + r * ((0 : ℂ) + r * ((-16 : ℂ)))))) / ((r ^ 2 - 1) * s ^ 3 * (s + 3)) := by
  unfold skewQF_qtr1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT0_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT0_lauI1 s r ((s + 1) * (s + 2)) = (((20 : ℂ) * s + (73 : ℂ) * s ^ 2 + (53 : ℂ) * s ^ 3 + (10 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((432 : ℂ) + (-342 : ℂ) * s + (-296 : ℂ) * s ^ 2 + (-86 : ℂ) * s ^ 3 + (-12 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-392 : ℂ) + (-232 : ℂ) * s + (-51 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-64 : ℂ) + (-6 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))))) / (r ^ 2 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3)) := by
  unfold skewQF_qT0_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT1_lauI1 s r ((s + 1) * (s + 2)) = (((576 : ℂ) + (638 : ℂ) * s + (244 : ℂ) * s ^ 2 + (28 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-888 : ℂ) + (-260 : ℂ) * s + (-6 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((16 : ℂ) + (6 : ℂ) * s + (2 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((72 : ℂ)))))))) / (r * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3)) := by
  unfold skewQF_qT1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT2_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT2_lauI1 s r ((s + 1) * (s + 2)) = (((-288 : ℂ) + (-182 : ℂ) * s + (-32 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * (((112 : ℂ) + (30 : ℂ) * s) + r * ((0 : ℂ) + r * ((36 : ℂ)))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3)) := by
  unfold skewQF_qT2_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt0_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt0_lauI3 s r ((s + 1) * (s + 2)) = (((128 : ℂ) * s + (239 : ℂ) * s ^ 2 + (180 : ℂ) * s ^ 3 + (67 : ℂ) * s ^ 4 + (10 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((672 : ℂ) + (520 : ℂ) * s + (139 : ℂ) * s ^ 2 + (54 : ℂ) * s ^ 3 + (9 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((744 : ℂ) + (184 : ℂ) * s + (2 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-72 : ℂ)))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQF_qt0_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt1_lauI3 s r ((s + 1) * (s + 2)) = (((288 : ℂ) + (314 : ℂ) * s + (98 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((192 : ℂ) + (128 : ℂ) * s + (22 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-144 : ℂ) + (-24 : ℂ) * s))))) / (r ^ 3 * (r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQF_qt1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr0_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr0_lauI3 s r ((s + 1) * (s + 2)) = (((-144 : ℂ) + (-273 : ℂ) * s + (-237 : ℂ) * s ^ 2 + (-102 : ℂ) * s ^ 3 + (-16 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((384 : ℂ) + (56 : ℂ) * s + (-182 : ℂ) * s ^ 2 + (-50 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((540 : ℂ) + (141 : ℂ) * s + (3 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-108 : ℂ) + (-12 : ℂ) * s))))))) / (r ^ 3 * (r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQF_qtr0_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr1_lauI3 s r ((s + 1) * (s + 2)) = (((192 : ℂ) + (233 : ℂ) * s + (99 : ℂ) * s ^ 2 + (16 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((84 : ℂ) + (63 : ℂ) * s + (21 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((-108 : ℂ) + (-24 : ℂ) * s))))) / (r ^ 2 * (r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQF_qtr1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT0_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT0_lauI3 s r ((s + 1) * (s + 2)) = (((328 : ℂ) * s + (439 : ℂ) * s ^ 2 + (228 : ℂ) * s ^ 3 + (67 : ℂ) * s ^ 4 + (10 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((672 : ℂ) + (-318 : ℂ) * s + (-1010 : ℂ) * s ^ 2 + (-458 : ℂ) * s ^ 3 + (-90 : ℂ) * s ^ 4 + (-12 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((72 : ℂ) + (-1428 : ℂ) * s + (-785 : ℂ) * s ^ 2 + (-132 : ℂ) * s ^ 3 + (-9 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-816 : ℂ) + (-262 : ℂ) * s + (-20 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((72 : ℂ)))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQF_qT0_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT1_lauI3 s r ((s + 1) * (s + 2)) = (((864 : ℂ) + (1246 : ℂ) * s + (754 : ℂ) * s ^ 2 + (236 : ℂ) * s ^ 3 + (28 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-480 : ℂ) + (44 : ℂ) * s + (378 : ℂ) * s ^ 2 + (94 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-1416 : ℂ) + (-410 : ℂ) * s + (-28 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((360 : ℂ) + (48 : ℂ) * s))))))) / (r ^ 3 * (r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQF_qT1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT2_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT2_lauI3 s r ((s + 1) * (s + 2)) = (((-480 : ℂ) + (-546 : ℂ) * s + (-214 : ℂ) * s ^ 2 + (-32 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-192 : ℂ) + (-110 : ℂ) * s + (-34 : ℂ) * s ^ 2) + r * ((0 : ℂ) + r * ((252 : ℂ) + (60 : ℂ) * s))))) / (r ^ 2 * (r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQF_qT2_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt2_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt2_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-32 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((4 : ℂ)))))) / (s ^ 3 * (s + 3)) := by
  unfold skewQF_qt2_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr2_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr2_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-16 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((2 : ℂ))))))) / (s ^ 3 * (s + 3)) := by
  unfold skewQF_qtr2_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT3_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT3_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((32 : ℂ) + (8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-4 : ℂ))))))) / (s ^ 2 * (s + 3)) := by
  unfold skewQF_qT3_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt2_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt2_lauI1 s r ((s + 1) * (s + 2)) = (((-24 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-4 : ℂ)))) / (s ^ 3 * (s + 3)) := by
  unfold skewQF_qt2_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr2_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr2_lauI1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-12 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((-2 : ℂ))))) / (s ^ 3 * (s + 3)) := by
  unfold skewQF_qtr2_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT3_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT3_lauI1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((24 : ℂ) + (8 : ℂ) * s) + r * ((0 : ℂ) + r * ((4 : ℂ))))) / (s ^ 2 * (s + 3)) := by
  unfold skewQF_qT3_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt2_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt2_lauI3 s r ((s + 1) * (s + 2)) = (((-16 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-12 : ℂ)))) / (r ^ 2 * s ^ 3 * (s + 3)) := by
  unfold skewQF_qt2_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr2_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr2_lauI3 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((-6 : ℂ)))) / (r * s ^ 3 * (s + 3)) := by
  unfold skewQF_qtr2_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT3_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT3_lauI3 s r ((s + 1) * (s + 2)) = (((16 : ℂ) + (8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ)))) / (r * s ^ 2 * (s + 3)) := by
  unfold skewQF_qT3_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-30 : ℂ) + (-20 : ℂ) * s) + r * ((0 : ℂ) + r * ((126 : ℂ) + (84 : ℂ) * s))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qtr0_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-6 : ℂ) + (-16 : ℂ) * s) + r * ((0 : ℂ) + r * ((18 : ℂ) + (28 : ℂ) * s)))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qtr0_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-2 : ℂ)) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qtr0_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-48 : ℂ) + (2 : ℂ) * s + (30 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((216 : ℂ) + (120 : ℂ) * s)))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qtr0_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-24 : ℂ) * s + (6 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((36 : ℂ) + (48 : ℂ) * s))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qtr0_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qtr0_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-96 : ℂ) + (-50 : ℂ) * s + (30 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((552 : ℂ) + (304 : ℂ) * s + (-36 : ℂ) * s ^ 2 + (-20 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-624 : ℂ) + (-358 : ℂ) * s + (6 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((216 : ℂ) + (120 : ℂ) * s)))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qtr0_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((84 : ℂ) + (88 : ℂ) * s + (-6 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-396 : ℂ) + (-312 : ℂ) * s + (6 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((288 : ℂ) + (216 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qtr0_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-40 : ℂ) * s) + r * ((0 : ℂ) + r * ((36 : ℂ) + (60 : ℂ) * s)))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qtr0_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ)))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qtr0_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-42 : ℂ) + (-16 : ℂ) * s) + r * ((0 : ℂ) + r * ((66 : ℂ) + (28 : ℂ) * s)))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qtr1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-6 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((6 : ℂ) + (4 : ℂ) * s))))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qtr1_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qtr1_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-72 : ℂ) + (-24 : ℂ) * s + (6 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((120 : ℂ) + (48 : ℂ) * s))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qtr1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ) + (8 : ℂ) * s)))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qtr1_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qtr1_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((144 : ℂ) + (66 : ℂ) * s + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-288 : ℂ) + (-122 : ℂ) * s + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((120 : ℂ) + (48 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qtr1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-108 : ℂ) + (-48 : ℂ) * s) + r * ((0 : ℂ) + r * ((144 : ℂ) + (64 : ℂ) * s)))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qtr1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ) + (8 : ℂ) * s))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qtr1_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qtr1_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-2 : ℂ)) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qtr2_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qtr1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qtr2_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qtr2_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qtr2_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qt1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qtr2_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qtr2_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))) / (s ^ 3 * (s + 3)) := by
  unfold skewQQ_qtr2_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ)))))))) / (s ^ 3 * (s + 3)) := by
  unfold skewQQ_qtr2_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qT2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qtr2_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qtr2_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((38 : ℂ) * s + (42 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((144 : ℂ) + (120 : ℂ) * s)))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qt0_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-6 : ℂ) * s + (12 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((24 : ℂ) + (48 : ℂ) * s))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qt0_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qt0_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qt0 s r ((s + 1) * (s + 2)) = (((108 : ℂ) * s + (108 : ℂ) * s ^ 2 + (24 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((240 : ℂ) + (160 : ℂ) * s))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qt0_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((4 : ℂ) * s + (36 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((48 : ℂ) + (80 : ℂ) * s)))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qt0_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ)) + r * ((0 : ℂ) + r * ((8 : ℂ)))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qt0_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qT0 s r ((s + 1) * (s + 2)) = (((144 : ℂ) * s + (234 : ℂ) * s ^ 2 + (116 : ℂ) * s ^ 3 + (30 : ℂ) * s ^ 4 + (4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((480 : ℂ) + (168 : ℂ) * s + (-258 : ℂ) * s ^ 2 + (-132 : ℂ) * s ^ 3 + (-30 : ℂ) * s ^ 4 + (-4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-624 : ℂ) + (-368 : ℂ) * s + (72 : ℂ) * s ^ 2 + (24 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((240 : ℂ) + (160 : ℂ) * s))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qt0_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-84 : ℂ) * s + (-144 : ℂ) * s ^ 2 + (-28 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-384 : ℂ) + (-288 : ℂ) * s + (120 : ℂ) * s ^ 2 + (24 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((336 : ℂ) + (320 : ℂ) * s)))))) / ((r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qt0_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-28 : ℂ) * s + (24 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((48 : ℂ) + (104 : ℂ) * s))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qt0_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ)) + r * ((0 : ℂ) + r * ((8 : ℂ))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qt0_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-60 : ℂ) + (-6 : ℂ) * s + (12 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((108 : ℂ) + (48 : ℂ) * s))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qt1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ) + (8 : ℂ) * s)))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qt1_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qt1_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-96 : ℂ) + (4 : ℂ) * s + (36 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((192 : ℂ) + (80 : ℂ) * s)))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qt1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-24 : ℂ) + (-16 : ℂ) * s) + r * ((0 : ℂ) + r * ((24 : ℂ) + (16 : ℂ) * s))))) / (s ^ 3 * (s + 3) ^ 3) := by
  unfold skewQQ_qt1_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qt1_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((192 : ℂ) + (28 : ℂ) * s + (-48 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-432 : ℂ) + (-160 : ℂ) * s + (24 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((192 : ℂ) + (80 : ℂ) * s)))))) / ((r ^ 2 - 1) * s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qt1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-168 : ℂ) + (-44 : ℂ) * s + (24 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((240 : ℂ) + (112 : ℂ) * s))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qt1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-24 : ℂ) + (-16 : ℂ) * s) + r * ((0 : ℂ) + r * ((24 : ℂ) + (16 : ℂ) * s)))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qt1_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qt1_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qt2_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qtr1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qt2_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qt2_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ)) + r * ((0 : ℂ) + r * ((8 : ℂ)))))) / (s ^ 3 * (s + 3) ^ 2) := by
  unfold skewQQ_qt2_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qt1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qt2_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qt2_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-16 : ℂ)) + r * ((0 : ℂ) + r * ((8 : ℂ)))))) / (s ^ 3 * (s + 3)) := by
  unfold skewQQ_qt2_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ)) + r * ((0 : ℂ) + r * ((8 : ℂ))))))) / (s ^ 3 * (s + 3)) := by
  unfold skewQQ_qt2_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qT2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qt2_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qt2_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-94 : ℂ) * s + (-78 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-144 : ℂ) + (20 : ℂ) * s + (144 : ℂ) * s ^ 2 + (20 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((288 : ℂ) + (178 : ℂ) * s + (-66 : ℂ) * s ^ 2 + (-8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-144 : ℂ) + (-120 : ℂ) * s)))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT0_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) * s + (18 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((24 : ℂ) + (68 : ℂ) * s + (-18 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-24 : ℂ) + (-48 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT0_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * ((-4 : ℂ))))))) / (s * (s + 3) ^ 3) := by
  unfold skewQQ_qT0_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qt0 s r ((s + 1) * (s + 2)) = (((-252 : ℂ) * s + (-270 : ℂ) * s ^ 2 + (-116 : ℂ) * s ^ 3 + (-30 : ℂ) * s ^ 4 + (-4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-240 : ℂ) + (228 : ℂ) * s + (390 : ℂ) * s ^ 2 + (132 : ℂ) * s ^ 3 + (30 : ℂ) * s ^ 4 + (4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((480 : ℂ) + (152 : ℂ) * s + (-144 : ℂ) * s ^ 2 + (-24 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-240 : ℂ) + (-160 : ℂ) * s))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT0_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((8 : ℂ) * s + (60 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((48 : ℂ) + (88 : ℂ) * s + (-48 : ℂ) * s ^ 2 + (-8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-48 : ℂ) + (-80 : ℂ) * s)))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT0_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((16 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))) / (s * (s + 3) ^ 3) := by
  unfold skewQQ_qT0_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qT0 s r ((s + 1) * (s + 2)) = (((-360 : ℂ) * s + (-414 : ℂ) * s ^ 2 + (-152 : ℂ) * s ^ 3 + (-30 : ℂ) * s ^ 4 + (-4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-480 : ℂ) + (4 : ℂ) * s + (378 : ℂ) * s ^ 2 + (144 : ℂ) * s ^ 3 + (30 : ℂ) * s ^ 4 + (4 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((624 : ℂ) + (308 : ℂ) * s + (-108 : ℂ) * s ^ 2 + (-24 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-240 : ℂ) + (-160 : ℂ) * s))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT0_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-204 : ℂ) * s + (-252 : ℂ) * s ^ 2 + (-40 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-384 : ℂ) + (-64 : ℂ) * s + (432 : ℂ) * s ^ 2 + (64 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((720 : ℂ) + (572 : ℂ) * s + (-180 : ℂ) * s ^ 2 + (-24 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-336 : ℂ) + (-320 : ℂ) * s)))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT0_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-56 : ℂ) * s + (36 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((48 : ℂ) + (168 : ℂ) * s + (-36 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-48 : ℂ) + (-104 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT0_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((16 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ))))))) / (s * (s + 3) ^ 2) := by
  unfold skewQQ_qT0_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-180 : ℂ) + (-70 : ℂ) * s + (12 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((540 : ℂ) + (294 : ℂ) * s + (-12 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-360 : ℂ) + (-216 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((36 : ℂ) + (48 : ℂ) * s) + r * ((0 : ℂ) + r * ((-48 : ℂ) + (-64 : ℂ) * s)))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT1_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((4 : ℂ)) + r * ((0 : ℂ) + r * ((-4 : ℂ)))))))) / (s * (s + 3) ^ 3) := by
  unfold skewQQ_qT1_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-288 : ℂ) + (-24 : ℂ) * s + (108 : ℂ) * s ^ 2 + (28 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((912 : ℂ) + (360 : ℂ) * s + (-96 : ℂ) * s ^ 2 + (-24 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-624 : ℂ) + (-320 : ℂ) * s)))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((72 : ℂ) + (80 : ℂ) * s + (-12 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-96 : ℂ) + (-112 : ℂ) * s))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT1_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ))))))) / (s * (s + 3) ^ 3) := by
  unfold skewQQ_qT1_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((576 : ℂ) + (228 : ℂ) * s + (-108 : ℂ) * s ^ 2 + (-40 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((-1968 : ℂ) + (-928 : ℂ) * s + (144 : ℂ) * s ^ 2 + (64 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((1968 : ℂ) + (1004 : ℂ) * s + (-36 : ℂ) * s ^ 2 + (-24 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-624 : ℂ) + (-320 : ℂ) * s)))))))) / ((r ^ 2 - 1) ^ 2 * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-504 : ℂ) + (-300 : ℂ) * s + (36 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((1344 : ℂ) + (860 : ℂ) * s + (-36 : ℂ) * s ^ 2 + (-8 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-816 : ℂ) + (-544 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((72 : ℂ) + (112 : ℂ) * s) + r * ((0 : ℂ) + r * ((-96 : ℂ) + (-136 : ℂ) * s)))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT1_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))))) / (s * (s + 3) ^ 2) := by
  unfold skewQQ_qT1_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((108 : ℂ) + (40 : ℂ) * s) + r * ((0 : ℂ) + r * ((-144 : ℂ) + (-60 : ℂ) * s)))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT2_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((12 : ℂ) + (8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-12 : ℂ) + (-8 : ℂ) * s))))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT2_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qT2_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((192 : ℂ) + (64 : ℂ) * s + (-12 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-264 : ℂ) + (-104 : ℂ) * s))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT2_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((24 : ℂ) + (16 : ℂ) * s) + r * ((0 : ℂ) + r * ((-24 : ℂ) + (-16 : ℂ) * s)))))) / (s ^ 2 * (s + 3) ^ 3) := by
  unfold skewQQ_qT2_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qT2_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-384 : ℂ) + (-164 : ℂ) * s + (4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * (((672 : ℂ) + (276 : ℂ) * s + (-4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-264 : ℂ) + (-104 : ℂ) * s))))))) / ((r ^ 2 - 1) * s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT2_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((264 : ℂ) + (112 : ℂ) * s) + r * ((0 : ℂ) + r * ((-312 : ℂ) + (-136 : ℂ) * s)))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT2_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((24 : ℂ) + (16 : ℂ) * s) + r * ((0 : ℂ) + r * ((-24 : ℂ) + (-16 : ℂ) * s))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT2_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qT2_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((4 : ℂ)) + r * ((0 : ℂ) + r * ((-4 : ℂ)))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT3_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qtr1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qT3_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qtr2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qT3_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ))))))) / (s ^ 2 * (s + 3) ^ 2) := by
  unfold skewQQ_qT3_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qt1 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qT3_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qt2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qT3_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((16 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ))))))) / (s ^ 2 * (s + 3)) := by
  unfold skewQQ_qT3_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))))) / (s ^ 2 * (s + 3)) := by
  unfold skewQQ_qT3_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qT2 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qT3_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qT3 s r ((s + 1) * (s + 2)) = (0 : ℂ) := by
  unfold skewQQ_qT3_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

/-! ## Family against the reflected sources -/

theorem skewPieceFS_lauR_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((-2889 / 2 : ℂ) * s ^ 2 + (-5733 / 2 : ℂ) * s ^ 3 + (-9465 / 8 : ℂ) * s ^ 4 + (1539 / 2 : ℂ) * s ^ 5 + (975 / 2 : ℂ) * s ^ 6 + (-861 / 4 : ℂ) * s ^ 7 + (-1839 / 8 : ℂ) * s ^ 8 + (-255 / 4 : ℂ) * s ^ 9 + (-6 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-972 : ℂ) * s + (-8868 : ℂ) * s ^ 2 + (-5069 / 2 : ℂ) * s ^ 3 + (28297 / 4 : ℂ) * s ^ 4 + (19721 / 4 : ℂ) * s ^ 5 + (65 : ℂ) * s ^ 6 + (-1805 / 2 : ℂ) * s ^ 7 + (-1245 / 4 : ℂ) * s ^ 8 + (-133 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-3024 : ℂ) * s + (3813 : ℂ) * s ^ 2 + (17693 : ℂ) * s ^ 3 + (85691 / 8 : ℂ) * s ^ 4 + (-1929 / 4 : ℂ) * s ^ 5 + (-4535 / 2 : ℂ) * s ^ 6 + (-2987 / 4 : ℂ) * s ^ 7 + (-647 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((7992 : ℂ) * s + (13530 : ℂ) * s ^ 2 + (3383 / 2 : ℂ) * s ^ 3 + (-7677 : ℂ) * s ^ 4 + (-4968 : ℂ) * s ^ 5 + (-1221 : ℂ) * s ^ 6 + (-231 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-3024 : ℂ) * s + (-17721 / 2 : ℂ) * s ^ 2 + (-18567 / 2 : ℂ) * s ^ 3 + (-7855 / 2 : ℂ) * s ^ 4 + (-1497 / 2 : ℂ) * s ^ 5 + (-60 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-972 : ℂ) * s + (-1242 : ℂ) * s ^ 2 + (-396 : ℂ) * s ^ 3 + (-30 : ℂ) * s ^ 4))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauR_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((-243 / 2 : ℂ) * s ^ 2 + (-1647 / 2 : ℂ) * s ^ 3 + (-15651 / 8 : ℂ) * s ^ 4 + (-3729 / 2 : ℂ) * s ^ 5 + (-675 / 2 : ℂ) * s ^ 6 + (2481 / 4 : ℂ) * s ^ 7 + (3675 / 8 : ℂ) * s ^ 8 + (495 / 4 : ℂ) * s ^ 9 + (12 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-162 : ℂ) * s + (-3888 : ℂ) * s ^ 2 + (-14274 : ℂ) * s ^ 3 + (-57453 / 4 : ℂ) * s ^ 4 + (-4123 / 4 : ℂ) * s ^ 5 + (12915 / 2 : ℂ) * s ^ 6 + (8513 / 2 : ℂ) * s ^ 7 + (4423 / 4 : ℂ) * s ^ 8 + (425 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-3456 : ℂ) * s + (-19809 : ℂ) * s ^ 2 + (-23478 : ℂ) * s ^ 3 + (52097 / 8 : ℂ) * s ^ 4 + (86411 / 4 : ℂ) * s ^ 5 + (12488 : ℂ) * s ^ 6 + (12429 / 4 : ℂ) * s ^ 7 + (2375 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1332 : ℂ) * s + (-4020 : ℂ) * s ^ 2 + (21062 : ℂ) * s ^ 3 + (30038 : ℂ) * s ^ 4 + (15088 : ℂ) * s ^ 5 + (3494 : ℂ) * s ^ 6 + (326 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((4464 : ℂ) * s + (28725 / 2 : ℂ) * s ^ 2 + (31695 / 2 : ℂ) * s ^ 3 + (13995 / 2 : ℂ) * s ^ 4 + (2817 / 2 : ℂ) * s ^ 5 + (120 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((486 : ℂ) * s + (1188 : ℂ) * s ^ 2 + (450 : ℂ) * s ^ 3 + (36 : ℂ) * s ^ 4))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauR_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((108 : ℂ) * s ^ 3 + (396 : ℂ) * s ^ 4 + (363 : ℂ) * s ^ 5 + (-144 : ℂ) * s ^ 6 + (-408 : ℂ) * s ^ 7 + (-246 : ℂ) * s ^ 8 + (-63 : ℂ) * s ^ 9 + (-6 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((2952 : ℂ) * s ^ 2 + (7146 : ℂ) * s ^ 3 + (3644 : ℂ) * s ^ 4 + (-8861 / 2 : ℂ) * s ^ 5 + (-12943 / 2 : ℂ) * s ^ 6 + (-6587 / 2 : ℂ) * s ^ 7 + (-1545 / 2 : ℂ) * s ^ 8 + (-70 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((14772 : ℂ) * s ^ 2 + (10768 : ℂ) * s ^ 3 + (-13436 : ℂ) * s ^ 4 + (-40403 / 2 : ℂ) * s ^ 5 + (-20549 / 2 : ℂ) * s ^ 6 + (-4829 / 2 : ℂ) * s ^ 7 + (-443 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2748 : ℂ) * s ^ 2 + (-14294 : ℂ) * s ^ 3 + (-19656 : ℂ) * s ^ 4 + (-9764 : ℂ) * s ^ 5 + (-2276 : ℂ) * s ^ 6 + (-214 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-4788 : ℂ) * s ^ 2 + (-6672 : ℂ) * s ^ 3 + (-3168 : ℂ) * s ^ 4 + (-672 : ℂ) * s ^ 5 + (-60 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-324 : ℂ) * s ^ 2 + (-144 : ℂ) * s ^ 3 + (-12 : ℂ) * s ^ 4))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauR_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qt0 s r ((s + 1) * (s + 2)) * ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((-1458 : ℂ) * s ^ 2 + (-6237 / 4 : ℂ) * s ^ 3 + (-81 / 4 : ℂ) * s ^ 4 + (3051 / 16 : ℂ) * s ^ 5 + (-3297 / 8 : ℂ) * s ^ 6 + (-3477 / 8 : ℂ) * s ^ 7 + (-657 / 4 : ℂ) * s ^ 8 + (-453 / 16 : ℂ) * s ^ 9 + (-15 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-810 : ℂ) * s + (2889 / 2 : ℂ) * s ^ 2 + (17145 / 4 : ℂ) * s ^ 3 + (24573 / 8 : ℂ) * s ^ 4 + (7559 / 8 : ℂ) * s ^ 5 + (995 / 2 : ℂ) * s ^ 6 + (859 / 2 : ℂ) * s ^ 7 + (1441 / 8 : ℂ) * s ^ 8 + (267 / 8 : ℂ) * s ^ 9 + (9 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((2340 : ℂ) * s + (5439 / 2 : ℂ) * s ^ 2 + (-6027 / 4 : ℂ) * s ^ 3 + (-7899 / 2 : ℂ) * s ^ 4 + (-34129 / 16 : ℂ) * s ^ 5 + (-3165 / 8 : ℂ) * s ^ 6 + (-229 / 8 : ℂ) * s ^ 7 + (-33 / 2 : ℂ) * s ^ 8 + (-81 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-2220 : ℂ) * s + (-8475 / 2 : ℂ) * s ^ 2 + (-11601 / 4 : ℂ) * s ^ 3 + (-375 / 8 : ℂ) * s ^ 4 + (1575 / 2 : ℂ) * s ^ 5 + (1179 / 4 : ℂ) * s ^ 6 + (135 / 4 : ℂ) * s ^ 7 + (5 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((720 : ℂ) * s + (2713 / 2 : ℂ) * s ^ 2 + (1500 : ℂ) * s ^ 3 + (922 : ℂ) * s ^ 4 + (210 : ℂ) * s ^ 5 + (31 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-90 : ℂ) * s + (135 : ℂ) * s ^ 2 + (180 : ℂ) * s ^ 3 + (23 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((60 : ℂ) * s + (40 : ℂ) * s ^ 2))))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauR_qt0_lam s r hs hs3 hs1, ssSourceT_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((-459 : ℂ) * s ^ 2 + (-1683 : ℂ) * s ^ 3 + (-7683 / 4 : ℂ) * s ^ 4 + (-342 : ℂ) * s ^ 5 + (1719 / 2 : ℂ) * s ^ 6 + (1395 / 2 : ℂ) * s ^ 7 + (891 / 4 : ℂ) * s ^ 8 + (63 / 2 : ℂ) * s ^ 9 + (3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-324 : ℂ) * s + (-1938 : ℂ) * s ^ 2 + (-2269 : ℂ) * s ^ 3 + (1316 : ℂ) * s ^ 4 + (12929 / 4 : ℂ) * s ^ 5 + (3043 / 2 : ℂ) * s ^ 6 + (109 / 2 : ℂ) * s ^ 7 + (-124 : ℂ) * s ^ 8 + (-111 / 4 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-72 : ℂ) * s + (1296 : ℂ) * s ^ 2 + (5633 : ℂ) * s ^ 3 + (20325 / 4 : ℂ) * s ^ 4 + (603 / 4 : ℂ) * s ^ 5 + (-1534 : ℂ) * s ^ 6 + (-662 : ℂ) * s ^ 7 + (-389 / 4 : ℂ) * s ^ 8 + (-15 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1008 : ℂ) * s + (3270 : ℂ) * s ^ 2 + (1293 : ℂ) * s ^ 3 + (-5673 / 2 : ℂ) * s ^ 4 + (-2659 : ℂ) * s ^ 5 + (-816 : ℂ) * s ^ 6 + (-90 : ℂ) * s ^ 7 + (-3 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-504 : ℂ) * s + (-1917 : ℂ) * s ^ 2 + (-2842 : ℂ) * s ^ 3 + (-1620 : ℂ) * s ^ 4 + (-382 : ℂ) * s ^ 5 + (-31 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s + (-252 : ℂ) * s ^ 2 + (-132 : ℂ) * s ^ 3 + (-20 : ℂ) * s ^ 4))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauR_qt1_lam s r hs hs3 hs1, ssSourceT1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((108 : ℂ) * s ^ 2 + (396 : ℂ) * s ^ 3 + (363 : ℂ) * s ^ 4 + (-144 : ℂ) * s ^ 5 + (-408 : ℂ) * s ^ 6 + (-246 : ℂ) * s ^ 7 + (-63 : ℂ) * s ^ 8 + (-6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1314 : ℂ) * s ^ 2 + (1584 : ℂ) * s ^ 3 + (-1843 / 2 : ℂ) * s ^ 4 + (-4259 / 2 : ℂ) * s ^ 5 + (-2087 / 2 : ℂ) * s ^ 6 + (-265 / 2 : ℂ) * s ^ 7 + (27 : ℂ) * s ^ 8 + (6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-780 : ℂ) * s ^ 2 + (-3002 : ℂ) * s ^ 3 + (-2147 : ℂ) * s ^ 4 + (468 : ℂ) * s ^ 5 + (965 : ℂ) * s ^ 6 + (332 : ℂ) * s ^ 7 + (36 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1224 : ℂ) * s ^ 2 + (-120 : ℂ) * s ^ 3 + (3993 / 2 : ℂ) * s ^ 4 + (3259 / 2 : ℂ) * s ^ 5 + (943 / 2 : ℂ) * s ^ 6 + (93 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((528 : ℂ) * s ^ 2 + (1106 : ℂ) * s ^ 3 + (703 : ℂ) * s ^ 4 + (176 : ℂ) * s ^ 5 + (15 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((54 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 4))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauR_qt2_lam s r hs hs3 hs1, ssSourceT2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((-1080 : ℂ) * s + (-909 : ℂ) * s ^ 2 + (186 : ℂ) * s ^ 3 + (843 / 4 : ℂ) * s ^ 4 + (-507 / 4 : ℂ) * s ^ 5 + (-481 / 4 : ℂ) * s ^ 6 + (-121 / 4 : ℂ) * s ^ 7 + (-5 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-720 : ℂ) + (1404 : ℂ) * s + (1973 : ℂ) * s ^ 2 + (1330 : ℂ) * s ^ 3 + (519 : ℂ) * s ^ 4 + (339 / 2 : ℂ) * s ^ 5 + (86 : ℂ) * s ^ 6 + (55 / 2 : ℂ) * s ^ 7 + (3 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2376 : ℂ) + (936 : ℂ) * s + (-1743 : ℂ) * s ^ 2 + (-1533 : ℂ) * s ^ 3 + (-2625 / 4 : ℂ) * s ^ 4 + (-675 / 4 : ℂ) * s ^ 5 + (-117 / 4 : ℂ) * s ^ 6 + (-21 / 4 : ℂ) * s ^ 7 + (-1 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-2952 : ℂ) + (-2556 : ℂ) * s + (139 : ℂ) * s ^ 2 + (443 : ℂ) * s ^ 3 + (409 / 2 : ℂ) * s ^ 4 + (54 : ℂ) * s ^ 5 + (7 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((1656 : ℂ) + (1656 : ℂ) * s + (332 : ℂ) * s ^ 2 + (30 : ℂ) * s ^ 3 + (14 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-360 : ℂ) + (-360 : ℂ) * s + (-80 : ℂ) * s ^ 2))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauR_qT0_lam s r hs hs3 hs1, ssSourceTF_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((-1692 : ℂ) * s + (-3408 : ℂ) * s ^ 2 + (-1479 : ℂ) * s ^ 3 + (915 : ℂ) * s ^ 4 + (793 : ℂ) * s ^ 5 + (59 : ℂ) * s ^ 6 + (-70 : ℂ) * s ^ 7 + (-14 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1152 : ℂ) + (-1764 : ℂ) * s + (440 : ℂ) * s ^ 2 + (4449 : ℂ) * s ^ 3 + (3534 : ℂ) * s ^ 4 + (324 : ℂ) * s ^ 5 + (-440 : ℂ) * s ^ 6 + (-109 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2160 : ℂ) + (6828 : ℂ) * s + (5468 : ℂ) * s ^ 2 + (2230 : ℂ) * s ^ 3 + (-835 : ℂ) * s ^ 4 + (-1221 : ℂ) * s ^ 5 + (-289 : ℂ) * s ^ 6 + (-5 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((144 : ℂ) + (-1692 : ℂ) * s + (-3616 : ℂ) * s ^ 2 + (-2632 : ℂ) * s ^ 3 + (-1554 : ℂ) * s ^ 4 + (-344 : ℂ) * s ^ 5 + (-2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-2160 : ℂ) + (-2976 : ℂ) * s + (-644 : ℂ) * s ^ 2 + (-432 : ℂ) * s ^ 3 + (-156 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((1008 : ℂ) + (1296 : ℂ) * s + (320 : ℂ) * s ^ 2))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauR_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((-12 : ℂ) * s + (-376 : ℂ) * s ^ 2 + (-1291 : ℂ) * s ^ 3 + (-1355 : ℂ) * s ^ 4 + (-211 : ℂ) * s ^ 5 + (403 : ℂ) * s ^ 6 + (218 : ℂ) * s ^ 7 + (32 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-144 : ℂ) + (-1176 : ℂ) * s + (-4912 : ℂ) * s ^ 2 + (-6420 : ℂ) * s ^ 3 + (-772 : ℂ) * s ^ 4 + (3066 : ℂ) * s ^ 5 + (1736 : ℂ) * s ^ 6 + (270 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-864 : ℂ) + (-5064 : ℂ) * s + (-3776 : ℂ) * s ^ 2 + (2803 : ℂ) * s ^ 3 + (7495 : ℂ) * s ^ 4 + (4293 : ℂ) * s ^ 5 + (729 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((1728 : ℂ) + (7152 : ℂ) * s + (5648 : ℂ) * s ^ 2 + (5316 : ℂ) * s ^ 3 + (3656 : ℂ) * s ^ 4 + (756 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-288 : ℂ) + (180 : ℂ) * s + (-304 : ℂ) * s ^ 2 + (648 : ℂ) * s ^ 3 + (260 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-432 : ℂ) + (-1080 : ℂ) * s + (-312 : ℂ) * s ^ 2))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauR_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((96 : ℂ) * s ^ 2 + (320 : ℂ) * s ^ 3 + (216 : ℂ) * s ^ 4 + (-200 : ℂ) * s ^ 5 + (-296 : ℂ) * s ^ 6 + (-120 : ℂ) * s ^ 7 + (-16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1152 : ℂ) * s + (3408 : ℂ) * s ^ 2 + (1920 : ℂ) * s ^ 3 + (-2516 : ℂ) * s ^ 4 + (-3328 : ℂ) * s ^ 5 + (-1324 : ℂ) * s ^ 6 + (-176 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((1152 : ℂ) * s + (3168 : ℂ) * s ^ 2 + (-2888 : ℂ) * s ^ 3 + (-6828 : ℂ) * s ^ 4 + (-3400 : ℂ) * s ^ 5 + (-516 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-3168 : ℂ) * s + (-1488 : ℂ) * s ^ 2 + (-2736 : ℂ) * s ^ 3 + (-2232 : ℂ) * s ^ 4 + (-456 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((576 : ℂ) * s + (480 : ℂ) * s ^ 2 + (-264 : ℂ) * s ^ 3 + (-120 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((288 : ℂ) * s + (96 : ℂ) * s ^ 2))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauR_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewFSrcLam_lauR (s r : ℂ) : ℂ := (((-2784 : ℂ) * s + (-7972 : ℂ) * s ^ 2 + (-34769 / 4 : ℂ) * s ^ 3 + (-17339 / 4 : ℂ) * s ^ 4 + (-12353 / 16 : ℂ) * s ^ 5 + (729 / 8 : ℂ) * s ^ 6 + (93 / 8 : ℂ) * s ^ 7 + (-43 / 2 : ℂ) * s ^ 8 + (-93 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-2016 : ℂ) + (-2652 : ℂ) * s + (-16149 / 2 : ℂ) * s ^ 2 + (-19129 / 4 : ℂ) * s ^ 3 + (4689 / 8 : ℂ) * s ^ 4 + (13985 / 8 : ℂ) * s ^ 5 + (2169 / 2 : ℂ) * s ^ 6 + (849 / 2 : ℂ) * s ^ 7 + (849 / 8 : ℂ) * s ^ 8 + (117 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((3672 : ℂ) + (-360 : ℂ) * s + (10257 / 2 : ℂ) * s ^ 2 + (26877 / 4 : ℂ) * s ^ 3 + (1948 : ℂ) * s ^ 4 + (-17473 / 16 : ℂ) * s ^ 5 + (-8991 / 8 : ℂ) * s ^ 6 + (-3383 / 8 : ℂ) * s ^ 7 + (-335 / 4 : ℂ) * s ^ 8 + (-141 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-1080 : ℂ) + (5184 : ℂ) * s + (21499 / 2 : ℂ) * s ^ 2 + (28493 / 4 : ℂ) * s ^ 3 + (15141 / 8 : ℂ) * s ^ 4 + (124 : ℂ) * s ^ 5 + (-205 / 4 : ℂ) * s ^ 6 + (-53 / 4 : ℂ) * s ^ 7 + (-7 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-792 : ℂ) + (1092 : ℂ) * s + (1091 / 2 : ℂ) * s ^ 2 + (-362 : ℂ) * s ^ 3 + (-95 : ℂ) * s ^ 4 + (-8 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((216 : ℂ) + (-540 : ℂ) * s + (-417 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((60 : ℂ) * s + (40 : ℂ) * s ^ 2))))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2)

theorem skewFSrc_lauR_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFSrc_lauR s r ((s + 1) * (s + 2)) (ssSourceTR (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2))) = skewFSrcLam_lauR s r := by
  unfold skewFSrc_lauR
  rw [skewPieceFS_lauR_qtr0 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qtr1 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qtr2 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qt0 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qt1 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qt2 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qT0 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qT1 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qT2 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qT3 s r hr hf hs hs3 hs1]
  unfold skewFSrcLam_lauR
  simp only [← add_div]
  ring

theorem skewPieceFS_lauI1_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((567 / 2 : ℂ) * s + (1323 / 2 : ℂ) * s ^ 2 + (-441 / 8 : ℂ) * s ^ 3 + (-3225 / 2 : ℂ) * s ^ 4 + (-4281 / 2 : ℂ) * s ^ 5 + (-5373 / 4 : ℂ) * s ^ 6 + (-3663 / 8 : ℂ) * s ^ 7 + (-327 / 4 : ℂ) * s ^ 8 + (-6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((342 : ℂ) * s + (-711 / 2 : ℂ) * s ^ 2 + (-8921 / 4 : ℂ) * s ^ 3 + (-11573 / 4 : ℂ) * s ^ 4 + (-3889 / 2 : ℂ) * s ^ 5 + (-768 : ℂ) * s ^ 6 + (-669 / 4 : ℂ) * s ^ 7 + (-61 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-5307 : ℂ) * s + (-575 : ℂ) * s ^ 2 + (34171 / 8 : ℂ) * s ^ 3 + (12351 / 4 : ℂ) * s ^ 4 + (1857 / 2 : ℂ) * s ^ 5 + (477 / 4 : ℂ) * s ^ 6 + (25 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-438 : ℂ) * s + (4517 / 2 : ℂ) * s ^ 2 + (3787 / 2 : ℂ) * s ^ 3 + (1331 / 2 : ℂ) * s ^ 4 + (273 / 2 : ℂ) * s ^ 5 + (12 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((3447 / 2 : ℂ) * s + (4341 / 2 : ℂ) * s ^ 2 + (2153 / 2 : ℂ) * s ^ 3 + (507 / 2 : ℂ) * s ^ 4 + (24 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((324 : ℂ) * s + (144 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI1_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((405 / 2 : ℂ) * s + (2241 / 2 : ℂ) * s ^ 2 + (21285 / 8 : ℂ) * s ^ 3 + (7545 / 2 : ℂ) * s ^ 4 + (6999 / 2 : ℂ) * s ^ 5 + (8349 / 4 : ℂ) * s ^ 6 + (6027 / 8 : ℂ) * s ^ 7 + (591 / 4 : ℂ) * s ^ 8 + (12 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((4320 : ℂ) * s + (25821 / 2 : ℂ) * s ^ 2 + (83193 / 4 : ℂ) * s ^ 3 + (84883 / 4 : ℂ) * s ^ 4 + (13340 : ℂ) * s ^ 5 + (9893 / 2 : ℂ) * s ^ 6 + (3959 / 4 : ℂ) * s ^ 7 + (329 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1449 : ℂ) * s + (5301 : ℂ) * s ^ 2 + (108521 / 8 : ℂ) * s ^ 3 + (51407 / 4 : ℂ) * s ^ 4 + (5771 : ℂ) * s ^ 5 + (5181 / 4 : ℂ) * s ^ 6 + (951 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-10404 : ℂ) * s + (-25047 / 2 : ℂ) * s ^ 2 + (-12319 / 2 : ℂ) * s ^ 3 + (-3603 / 2 : ℂ) * s ^ 4 + (-617 / 2 : ℂ) * s ^ 5 + (-19 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-14415 / 2 : ℂ) * s + (-15473 / 2 : ℂ) * s ^ 2 + (-7153 / 2 : ℂ) * s ^ 3 + (-1679 / 2 : ℂ) * s ^ 4 + (-80 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-648 : ℂ) * s + (-288 : ℂ) * s ^ 2 + (-24 : ℂ) * s ^ 3))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI1_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((-108 : ℂ) * s ^ 3 + (-504 : ℂ) * s ^ 4 + (-867 : ℂ) * s ^ 5 + (-723 : ℂ) * s ^ 6 + (-315 : ℂ) * s ^ 7 + (-69 : ℂ) * s ^ 8 + (-6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2898 : ℂ) * s ^ 2 + (-9900 : ℂ) * s ^ 3 + (-27229 / 2 : ℂ) * s ^ 4 + (-19379 / 2 : ℂ) * s ^ 5 + (-7567 / 2 : ℂ) * s ^ 6 + (-1541 / 2 : ℂ) * s ^ 7 + (-64 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1476 : ℂ) * s + (-11172 : ℂ) * s ^ 2 + (-25068 : ℂ) * s ^ 3 + (-41309 / 2 : ℂ) * s ^ 4 + (-17067 / 2 : ℂ) * s ^ 5 + (-3595 / 2 : ℂ) * s ^ 6 + (-309 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((8124 : ℂ) * s + (5174 : ℂ) * s ^ 2 + (216 : ℂ) * s ^ 3 + (-556 : ℂ) * s ^ 4 + (-196 : ℂ) * s ^ 5 + (-26 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((5436 : ℂ) * s + (5664 : ℂ) * s ^ 2 + (2616 : ℂ) * s ^ 3 + (624 : ℂ) * s ^ 4 + (60 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((324 : ℂ) * s + (144 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI1_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qt0 s r ((s + 1) * (s + 2)) * ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((81 : ℂ) * s + (-729 / 4 : ℂ) * s ^ 2 + (-2619 / 2 : ℂ) * s ^ 3 + (-35133 / 16 : ℂ) * s ^ 4 + (-14361 / 8 : ℂ) * s ^ 5 + (-6609 / 8 : ℂ) * s ^ 6 + (-219 : ℂ) * s ^ 7 + (-501 / 16 : ℂ) * s ^ 8 + (-15 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1683 / 2 : ℂ) * s + (555 / 4 : ℂ) * s ^ 2 + (24071 / 8 : ℂ) * s ^ 3 + (32977 / 8 : ℂ) * s ^ 4 + (11325 / 4 : ℂ) * s ^ 5 + (4651 / 4 : ℂ) * s ^ 6 + (2305 / 8 : ℂ) * s ^ 7 + (315 / 8 : ℂ) * s ^ 8 + (9 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1551 / 2 : ℂ) * s + (1463 / 4 : ℂ) * s ^ 2 + (-4663 / 4 : ℂ) * s ^ 3 + (-25641 / 16 : ℂ) * s ^ 4 + (-7485 / 8 : ℂ) * s ^ 5 + (-2565 / 8 : ℂ) * s ^ 6 + (-273 / 4 : ℂ) * s ^ 7 + (-129 / 16 : ℂ) * s ^ 8 + (-3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((201 / 2 : ℂ) * s + (293 / 4 : ℂ) * s ^ 2 + (-2393 / 8 : ℂ) * s ^ 3 + (-1037 / 4 : ℂ) * s ^ 4 + (-189 / 2 : ℂ) * s ^ 5 + (-16 : ℂ) * s ^ 6 + (-7 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-181 / 2 : ℂ) * s + (-719 / 2 : ℂ) * s ^ 2 + (-455 / 2 : ℂ) * s ^ 3 + (-129 / 2 : ℂ) * s ^ 4 + (-6 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-13 : ℂ) * s + (-36 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-12 : ℂ) * s))))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI1_qt0_lam s r hs hs3 hs1, ssSourceT_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((405 : ℂ) * s + (1647 : ℂ) * s ^ 2 + (12789 / 4 : ℂ) * s ^ 3 + (7389 / 2 : ℂ) * s ^ 4 + (5217 / 2 : ℂ) * s ^ 5 + (2211 / 2 : ℂ) * s ^ 6 + (1071 / 4 : ℂ) * s ^ 7 + (33 : ℂ) * s ^ 8 + (3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-18 : ℂ) * s + (-240 : ℂ) * s ^ 2 + (-243 : ℂ) * s ^ 3 + (-2251 / 4 : ℂ) * s ^ 4 + (-1849 / 2 : ℂ) * s ^ 5 + (-1297 / 2 : ℂ) * s ^ 6 + (-211 : ℂ) * s ^ 7 + (-123 / 4 : ℂ) * s ^ 8 + (-3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1716 : ℂ) * s + (-3911 : ℂ) * s ^ 2 + (-18867 / 4 : ℂ) * s ^ 3 + (-15155 / 4 : ℂ) * s ^ 4 + (-1839 : ℂ) * s ^ 5 + (-480 : ℂ) * s ^ 6 + (-233 / 4 : ℂ) * s ^ 7 + (-9 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((438 : ℂ) * s + (1178 : ℂ) * s ^ 2 + (1993 / 2 : ℂ) * s ^ 3 + (459 : ℂ) * s ^ 4 + (136 : ℂ) * s ^ 5 + (23 : ℂ) * s ^ 6 + (3 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((783 : ℂ) * s + (1254 : ℂ) * s ^ 2 + (754 : ℂ) * s ^ 3 + (198 : ℂ) * s ^ 4 + (19 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((108 : ℂ) * s + (72 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI1_qt1_lam s r hs hs3 hs1, ssSourceT1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((-108 : ℂ) * s ^ 2 + (-504 : ℂ) * s ^ 3 + (-867 : ℂ) * s ^ 4 + (-723 : ℂ) * s ^ 5 + (-315 : ℂ) * s ^ 6 + (-69 : ℂ) * s ^ 7 + (-6 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((54 : ℂ) * s + (-1116 : ℂ) * s ^ 2 + (-5541 / 2 : ℂ) * s ^ 3 + (-4709 / 2 : ℂ) * s ^ 4 + (-1581 / 2 : ℂ) * s ^ 5 + (-55 / 2 : ℂ) * s ^ 6 + (39 : ℂ) * s ^ 7 + (6 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((684 : ℂ) * s + (1698 : ℂ) * s ^ 2 + (2854 : ℂ) * s ^ 3 + (2759 : ℂ) * s ^ 4 + (1374 : ℂ) * s ^ 5 + (329 : ℂ) * s ^ 6 + (30 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-48 : ℂ) * s + (524 : ℂ) * s ^ 2 + (1995 / 2 : ℂ) * s ^ 3 + (1229 / 2 : ℂ) * s ^ 4 + (309 / 2 : ℂ) * s ^ 5 + (27 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-636 : ℂ) * s + (-962 : ℂ) * s ^ 2 + (-571 : ℂ) * s ^ 3 + (-152 : ℂ) * s ^ 4 + (-15 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-54 : ℂ) * s + (-36 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI1_qt2_lam s r hs hs3 hs1, ssSourceT2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((72 : ℂ) + (-105 : ℂ) * s + (-634 : ℂ) * s ^ 2 + (-3425 / 4 : ℂ) * s ^ 3 + (-2211 / 4 : ℂ) * s ^ 4 + (-765 / 4 : ℂ) * s ^ 5 + (-137 / 4 : ℂ) * s ^ 6 + (-5 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-504 : ℂ) + (825 : ℂ) * s + (2365 : ℂ) * s ^ 2 + (1869 : ℂ) * s ^ 3 + (1529 / 2 : ℂ) * s ^ 4 + (202 : ℂ) * s ^ 5 + (71 / 2 : ℂ) * s ^ 6 + (3 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((492 : ℂ) + (-1345 : ℂ) * s + (-1487 : ℂ) * s ^ 2 + (-3205 / 4 : ℂ) * s ^ 3 + (-1219 / 4 : ℂ) * s ^ 4 + (-289 / 4 : ℂ) * s ^ 5 + (-37 / 4 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((24 : ℂ) + (383 : ℂ) * s + (230 : ℂ) * s ^ 2 + (169 / 2 : ℂ) * s ^ 3 + (21 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-156 : ℂ) + (-70 : ℂ) * s + (-18 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((72 : ℂ) + (24 : ℂ) * s))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI1_qT0_lam s r hs hs3 hs1, ssSourceTF_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((612 : ℂ) + (1848 : ℂ) * s + (2105 : ℂ) * s ^ 2 + (933 : ℂ) * s ^ 3 + (-153 : ℂ) * s ^ 4 + (-319 : ℂ) * s ^ 5 + (-116 : ℂ) * s ^ 6 + (-14 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1620 : ℂ) + (-2472 : ℂ) * s + (-803 : ℂ) * s ^ 2 + (46 : ℂ) * s ^ 3 + (-348 : ℂ) * s ^ 4 + (-304 : ℂ) * s ^ 5 + (-65 : ℂ) * s ^ 6 + (-2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-516 : ℂ) + (-1984 : ℂ) * s + (-466 : ℂ) * s ^ 2 + (403 : ℂ) * s ^ 3 + (-7 : ℂ) * s ^ 4 + (-51 : ℂ) * s ^ 5 + (-3 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((2052 : ℂ) + (948 : ℂ) * s + (964 : ℂ) * s ^ 2 + (454 : ℂ) * s ^ 3 + (60 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-96 : ℂ) + (364 : ℂ) * s + (336 : ℂ) * s ^ 2 + (68 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-432 : ℂ) + (-144 : ℂ) * s))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI1_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((180 : ℂ) + (840 : ℂ) * s + (1637 : ℂ) * s ^ 2 + (2037 : ℂ) * s ^ 3 + (1789 : ℂ) * s ^ 4 + (979 : ℂ) * s ^ 5 + (282 : ℂ) * s ^ 6 + (32 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((1128 : ℂ) + (3508 : ℂ) * s + (5640 : ℂ) * s ^ 2 + (6608 : ℂ) * s ^ 3 + (4638 : ℂ) * s ^ 4 + (1600 : ℂ) * s ^ 5 + (206 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-2040 : ℂ) + (-2288 : ℂ) * s + (-557 : ℂ) * s ^ 2 + (1967 : ℂ) * s ^ 3 + (1525 : ℂ) * s ^ 4 + (289 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-1392 : ℂ) + (-5612 : ℂ) * s + (-4728 : ℂ) * s ^ 2 + (-1148 : ℂ) * s ^ 3 + (-48 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((1476 : ℂ) + (-696 : ℂ) * s + (-936 : ℂ) * s ^ 2 + (-180 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((648 : ℂ) + (216 : ℂ) * s))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI1_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((-96 : ℂ) * s ^ 2 + (-416 : ℂ) * s ^ 3 + (-632 : ℂ) * s ^ 4 + (-432 : ℂ) * s ^ 5 + (-136 : ℂ) * s ^ 6 + (-16 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1104 : ℂ) * s + (-4400 : ℂ) * s ^ 2 + (-6420 : ℂ) * s ^ 3 + (-4320 : ℂ) * s ^ 4 + (-1356 : ℂ) * s ^ 5 + (-160 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((576 : ℂ) + (576 : ℂ) * s + (-3832 : ℂ) * s ^ 2 + (-5412 : ℂ) * s ^ 3 + (-2408 : ℂ) * s ^ 4 + (-348 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((864 : ℂ) + (5904 : ℂ) * s + (4032 : ℂ) * s ^ 2 + (648 : ℂ) * s ^ 3 + (-24 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-1152 : ℂ) + (480 : ℂ) * s + (648 : ℂ) * s ^ 2 + (120 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-288 : ℂ) + (-96 : ℂ) * s))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI1_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewFSrcLam_lauI1 (s r : ℂ) : ℂ := (((864 : ℂ) + (3555 : ℂ) * s + (24603 / 4 : ℂ) * s ^ 2 + (5579 : ℂ) * s ^ 3 + (43823 / 16 : ℂ) * s ^ 4 + (4953 / 8 : ℂ) * s ^ 5 + (-151 / 8 : ℂ) * s ^ 6 + (-161 / 4 : ℂ) * s ^ 7 + (-117 / 16 : ℂ) * s ^ 8 + (-3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-996 : ℂ) + (9227 / 2 : ℂ) * s + (44967 / 4 : ℂ) * s ^ 2 + (86131 / 8 : ℂ) * s ^ 3 + (53219 / 8 : ℂ) * s ^ 4 + (11857 / 4 : ℂ) * s ^ 5 + (3593 / 4 : ℂ) * s ^ 6 + (1353 / 8 : ℂ) * s ^ 7 + (141 / 8 : ℂ) * s ^ 8 + (3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1488 : ℂ) + (-15359 / 2 : ℂ) * s + (-58541 / 4 : ℂ) * s ^ 2 + (-56413 / 4 : ℂ) * s ^ 3 + (-136673 / 16 : ℂ) * s ^ 4 + (-27335 / 8 : ℂ) * s ^ 5 + (-6935 / 8 : ℂ) * s ^ 6 + (-259 / 2 : ℂ) * s ^ 7 + (-165 / 16 : ℂ) * s ^ 8 + (-3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1548 : ℂ) + (-1209 / 2 : ℂ) * s + (-11271 / 4 : ℂ) * s ^ 2 + (-18533 / 8 : ℂ) * s ^ 3 + (-3475 / 4 : ℂ) * s ^ 4 + (-337 / 2 : ℂ) * s ^ 5 + (-25 / 2 : ℂ) * s ^ 6 + (5 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((72 : ℂ) + (173 / 2 : ℂ) * s + (121 / 2 : ℂ) * s ^ 2 + (151 / 2 : ℂ) * s ^ 3 + (39 / 2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((41 : ℂ) * s + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-12 : ℂ) * s))))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2)

theorem skewFSrc_lauI1_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFSrc_lauI1 s r ((s + 1) * (s + 2)) (ssSourceTR (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2))) = skewFSrcLam_lauI1 s r := by
  unfold skewFSrc_lauI1
  rw [skewPieceFS_lauI1_qtr0 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qtr1 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qtr2 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qt0 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qt1 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qt2 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qT0 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qT1 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qT2 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qT3 s r hr hf hs hs3 hs1]
  unfold skewFSrcLam_lauI1
  simp only [← add_div]
  ring

theorem skewPieceFS_lauI3_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((-3321 / 2 : ℂ) * s ^ 2 + (-13797 / 2 : ℂ) * s ^ 3 + (-98217 / 8 : ℂ) * s ^ 4 + (-24561 / 2 : ℂ) * s ^ 5 + (-15165 / 2 : ℂ) * s ^ 6 + (-11877 / 4 : ℂ) * s ^ 7 + (-5775 / 8 : ℂ) * s ^ 8 + (-399 / 4 : ℂ) * s ^ 9 + (-6 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-972 : ℂ) * s + (-8352 : ℂ) * s ^ 2 + (-30237 / 2 : ℂ) * s ^ 3 + (-44931 / 4 : ℂ) * s ^ 4 + (-14043 / 4 : ℂ) * s ^ 5 + (-56 : ℂ) * s ^ 6 + (461 / 2 : ℂ) * s ^ 7 + (195 / 4 : ℂ) * s ^ 8 + (11 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-3024 : ℂ) * s + (9501 : ℂ) * s ^ 2 + (30641 : ℂ) * s ^ 3 + (246635 / 8 : ℂ) * s ^ 4 + (63615 / 4 : ℂ) * s ^ 5 + (9349 / 2 : ℂ) * s ^ 6 + (3005 / 4 : ℂ) * s ^ 7 + (409 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((7992 : ℂ) * s + (3978 : ℂ) * s ^ 2 + (-3225 / 2 : ℂ) * s ^ 3 + (-2086 : ℂ) * s ^ 4 + (-667 : ℂ) * s ^ 5 + (-44 : ℂ) * s ^ 6 + (15 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-3024 : ℂ) * s + (-12537 / 2 : ℂ) * s ^ 2 + (-5487 / 2 : ℂ) * s ^ 3 + (-543 / 2 : ℂ) * s ^ 4 + (111 / 2 : ℂ) * s ^ 5 + (12 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-972 : ℂ) * s + (-270 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 4))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI3_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((648 : ℂ) * s + (7965 / 2 : ℂ) * s ^ 2 + (20565 / 2 : ℂ) * s ^ 3 + (120669 / 8 : ℂ) * s ^ 4 + (28383 / 2 : ℂ) * s ^ 5 + (18021 / 2 : ℂ) * s ^ 6 + (15465 / 4 : ℂ) * s ^ 7 + (8571 / 8 : ℂ) * s ^ 8 + (687 / 4 : ℂ) * s ^ 9 + (12 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((13338 : ℂ) * s + (46584 : ℂ) * s ^ 2 + (73497 : ℂ) * s ^ 3 + (279911 / 4 : ℂ) * s ^ 4 + (176873 / 4 : ℂ) * s ^ 5 + (37577 / 2 : ℂ) * s ^ 6 + (10321 / 2 : ℂ) * s ^ 7 + (3303 / 4 : ℂ) * s ^ 8 + (233 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-5040 : ℂ) * s + (-18837 : ℂ) * s ^ 2 + (-27298 : ℂ) * s ^ 3 + (-166111 / 8 : ℂ) * s ^ 4 + (-39141 / 4 : ℂ) * s ^ 5 + (-2940 : ℂ) * s ^ 6 + (-2003 / 4 : ℂ) * s ^ 7 + (-281 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-21852 : ℂ) * s + (-47532 : ℂ) * s ^ 2 + (-51783 : ℂ) * s ^ 3 + (-32823 : ℂ) * s ^ 4 + (-12285 : ℂ) * s ^ 5 + (-2517 : ℂ) * s ^ 6 + (-216 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((11448 : ℂ) * s + (7677 / 2 : ℂ) * s ^ 2 + (-11073 / 2 : ℂ) * s ^ 3 + (-8349 / 2 : ℂ) * s ^ 4 + (-2271 / 2 : ℂ) * s ^ 5 + (-120 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((1458 : ℂ) * s + (-324 : ℂ) * s ^ 2 + (-378 : ℂ) * s ^ 3 + (-36 : ℂ) * s ^ 4))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI3_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((-108 : ℂ) * s ^ 3 + (-612 : ℂ) * s ^ 4 + (-1371 : ℂ) * s ^ 5 + (-1590 : ℂ) * s ^ 6 + (-1038 : ℂ) * s ^ 7 + (-384 : ℂ) * s ^ 8 + (-75 : ℂ) * s ^ 9 + (-6 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-2952 : ℂ) * s ^ 2 + (-12942 : ℂ) * s ^ 3 + (-23444 : ℂ) * s ^ 4 + (-45597 / 2 : ℂ) * s ^ 5 + (-25815 / 2 : ℂ) * s ^ 6 + (-8547 / 2 : ℂ) * s ^ 7 + (-1537 / 2 : ℂ) * s ^ 8 + (-58 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-11820 : ℂ) * s ^ 2 + (-33112 : ℂ) * s ^ 3 + (-36700 : ℂ) * s ^ 4 + (-42215 / 2 : ℂ) * s ^ 5 + (-13585 / 2 : ℂ) * s ^ 6 + (-2361 / 2 : ℂ) * s ^ 7 + (-175 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((13500 : ℂ) * s ^ 2 + (24642 : ℂ) * s ^ 3 + (20088 : ℂ) * s ^ 4 + (8652 : ℂ) * s ^ 5 + (1884 : ℂ) * s ^ 6 + (162 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((15660 : ℂ) * s ^ 2 + (18000 : ℂ) * s ^ 3 + (8400 : ℂ) * s ^ 4 + (1920 : ℂ) * s ^ 5 + (180 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((972 : ℂ) * s ^ 2 + (432 : ℂ) * s ^ 3 + (36 : ℂ) * s ^ 4))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI3_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qt0 s r ((s + 1) * (s + 2)) * ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((-648 : ℂ) * s + (-3564 : ℂ) * s ^ 2 + (-31725 / 4 : ℂ) * s ^ 3 + (-39219 / 4 : ℂ) * s ^ 4 + (-121365 / 16 : ℂ) * s ^ 5 + (-30825 / 8 : ℂ) * s ^ 6 + (-10341 / 8 : ℂ) * s ^ 7 + (-1107 / 4 : ℂ) * s ^ 8 + (-549 / 16 : ℂ) * s ^ 9 + (-15 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1386 : ℂ) * s + (17697 / 2 : ℂ) * s ^ 2 + (79141 / 4 : ℂ) * s ^ 3 + (183297 / 8 : ℂ) * s ^ 4 + (127651 / 8 : ℂ) * s ^ 5 + (7162 : ℂ) * s ^ 6 + (2121 : ℂ) * s ^ 7 + (3241 / 8 : ℂ) * s ^ 8 + (363 / 8 : ℂ) * s ^ 9 + (9 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-372 : ℂ) * s + (-13169 / 2 : ℂ) * s ^ 2 + (-58735 / 4 : ℂ) * s ^ 3 + (-15084 : ℂ) * s ^ 4 + (-144401 / 16 : ℂ) * s ^ 5 + (-27333 / 8 : ℂ) * s ^ 6 + (-6701 / 8 : ℂ) * s ^ 7 + (-129 : ℂ) * s ^ 8 + (-177 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-756 : ℂ) * s + (1213 / 2 : ℂ) * s ^ 2 + (9235 / 4 : ℂ) * s ^ 3 + (14549 / 8 : ℂ) * s ^ 4 + (641 : ℂ) * s ^ 5 + (429 / 4 : ℂ) * s ^ 6 + (37 / 4 : ℂ) * s ^ 7 + (5 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((360 : ℂ) * s + (909 / 2 : ℂ) * s ^ 2 + (477 : ℂ) * s ^ 3 + (155 : ℂ) * s ^ 4 + (13 : ℂ) * s ^ 5 + (1 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-6 : ℂ) * s + (239 : ℂ) * s ^ 2 + (44 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((36 : ℂ) * s))))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI3_qt0_lam s r hs hs3 hs1, ssSourceT_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((1296 : ℂ) * s + (5589 : ℂ) * s ^ 2 + (10773 : ℂ) * s ^ 3 + (49341 / 4 : ℂ) * s ^ 4 + (9255 : ℂ) * s ^ 5 + (9315 / 2 : ℂ) * s ^ 6 + (3075 / 2 : ℂ) * s ^ 7 + (1251 / 4 : ℂ) * s ^ 8 + (69 / 2 : ℂ) * s ^ 9 + (3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-684 : ℂ) * s + (-4290 : ℂ) * s ^ 2 + (-9415 : ℂ) * s ^ 3 + (-11126 : ℂ) * s ^ 4 + (-33383 / 4 : ℂ) * s ^ 5 + (-8445 / 2 : ℂ) * s ^ 6 + (-2847 / 2 : ℂ) * s ^ 7 + (-298 : ℂ) * s ^ 8 + (-135 / 4 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-4248 : ℂ) * s + (-11496 : ℂ) * s ^ 2 + (-14379 : ℂ) * s ^ 3 + (-42523 / 4 : ℂ) * s ^ 4 + (-19633 / 4 : ℂ) * s ^ 5 + (-1388 : ℂ) * s ^ 6 + (-226 : ℂ) * s ^ 7 + (-77 / 4 : ℂ) * s ^ 8 + (-3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((5040 : ℂ) * s + (11862 : ℂ) * s ^ 2 + (13099 : ℂ) * s ^ 3 + (17843 / 2 : ℂ) * s ^ 4 + (3805 : ℂ) * s ^ 5 + (932 : ℂ) * s ^ 6 + (112 : ℂ) * s ^ 7 + (9 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1080 : ℂ) * s + (-1557 : ℂ) * s ^ 2 + (-114 : ℂ) * s ^ 3 + (488 : ℂ) * s ^ 4 + (194 : ℂ) * s ^ 5 + (21 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-324 : ℂ) * s + (-108 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3 + (12 : ℂ) * s ^ 4))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI3_qt1_lam s r hs hs3 hs1, ssSourceT1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((-108 : ℂ) * s ^ 2 + (-612 : ℂ) * s ^ 3 + (-1371 : ℂ) * s ^ 4 + (-1590 : ℂ) * s ^ 5 + (-1038 : ℂ) * s ^ 6 + (-384 : ℂ) * s ^ 7 + (-75 : ℂ) * s ^ 8 + (-6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1206 : ℂ) * s ^ 2 + (-3816 : ℂ) * s ^ 3 + (-9239 / 2 : ℂ) * s ^ 4 + (-5159 / 2 : ℂ) * s ^ 5 + (-1075 / 2 : ℂ) * s ^ 6 + (155 / 2 : ℂ) * s ^ 7 + (51 : ℂ) * s ^ 8 + (6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((2148 : ℂ) * s ^ 2 + (6398 : ℂ) * s ^ 3 + (7855 : ℂ) * s ^ 4 + (5050 : ℂ) * s ^ 5 + (1783 : ℂ) * s ^ 6 + (326 : ℂ) * s ^ 7 + (24 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1128 : ℂ) * s ^ 2 + (1168 : ℂ) * s ^ 3 + (-3 / 2 : ℂ) * s ^ 4 + (-801 / 2 : ℂ) * s ^ 5 + (-325 / 2 : ℂ) * s ^ 6 + (-39 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-1800 : ℂ) * s ^ 2 + (-3030 : ℂ) * s ^ 3 + (-1845 : ℂ) * s ^ 4 + (-480 : ℂ) * s ^ 5 + (-45 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-162 : ℂ) * s ^ 2 + (-108 : ℂ) * s ^ 3 + (-18 : ℂ) * s ^ 4))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI3_qt2_lam s r hs hs3 hs1, ssSourceT2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((-576 : ℂ) + (-2760 : ℂ) * s + (-5077 : ℂ) * s ^ 2 + (-4962 : ℂ) * s ^ 3 + (-11709 / 4 : ℂ) * s ^ 4 + (-4411 / 4 : ℂ) * s ^ 5 + (-1065 / 4 : ℂ) * s ^ 6 + (-153 / 4 : ℂ) * s ^ 7 + (-5 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2160 : ℂ) + (9588 : ℂ) * s + (15205 : ℂ) * s ^ 2 + (12228 : ℂ) * s ^ 3 + (5727 : ℂ) * s ^ 4 + (3367 / 2 : ℂ) * s ^ 5 + (330 : ℂ) * s ^ 6 + (87 / 2 : ℂ) * s ^ 7 + (3 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-2664 : ℂ) + (-11760 : ℂ) * s + (-14739 : ℂ) * s ^ 2 + (-8541 : ℂ) * s ^ 3 + (-11737 / 4 : ℂ) * s ^ 4 + (-2867 / 4 : ℂ) * s ^ 5 + (-509 / 4 : ℂ) * s ^ 6 + (-53 / 4 : ℂ) * s ^ 7 + (-1 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((936 : ℂ) + (5580 : ℂ) * s + (4603 : ℂ) * s ^ 2 + (1765 : ℂ) * s ^ 3 + (865 / 2 : ℂ) * s ^ 4 + (64 : ℂ) * s ^ 5 + (7 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((360 : ℂ) + (-576 : ℂ) * s + (-280 : ℂ) * s ^ 2 + (-34 : ℂ) * s ^ 3 + (-6 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-216 : ℂ) + (-72 : ℂ) * s))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI3_qT0_lam s r hs hs3 hs1, ssSourceTF_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((1152 : ℂ) + (3108 : ℂ) * s + (2336 : ℂ) * s ^ 2 + (-1015 : ℂ) * s ^ 3 + (-2825 : ℂ) * s ^ 4 + (-2075 : ℂ) * s ^ 5 + (-793 : ℂ) * s ^ 6 + (-162 : ℂ) * s ^ 7 + (-14 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-3456 : ℂ) + (-7620 : ℂ) * s + (-5384 : ℂ) * s ^ 2 + (-167 : ℂ) * s ^ 3 + (1518 : ℂ) * s ^ 4 + (612 : ℂ) * s ^ 5 + (24 : ℂ) * s ^ 6 + (-21 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2448 : ℂ) + (3660 : ℂ) * s + (3396 : ℂ) * s ^ 2 + (3894 : ℂ) * s ^ 3 + (2793 : ℂ) * s ^ 4 + (871 : ℂ) * s ^ 5 + (91 : ℂ) * s ^ 6 + (-1 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((2160 : ℂ) + (2724 : ℂ) * s + (-568 : ℂ) * s ^ 2 + (-400 : ℂ) * s ^ 3 + (382 : ℂ) * s ^ 4 + (144 : ℂ) * s ^ 5 + (6 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-3600 : ℂ) + (-2016 : ℂ) * s + (-1124 : ℂ) * s ^ 2 + (-176 : ℂ) * s ^ 3 + (36 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((1296 : ℂ) + (144 : ℂ) * s + (-96 : ℂ) * s ^ 2))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI3_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((576 : ℂ) + (3252 : ℂ) * s + (7512 : ℂ) * s ^ 2 + (9685 : ℂ) * s ^ 3 + (7973 : ℂ) * s ^ 4 + (4429 : ℂ) * s ^ 5 + (1619 : ℂ) * s ^ 6 + (346 : ℂ) * s ^ 7 + (32 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3024 : ℂ) + (11496 : ℂ) * s + (18760 : ℂ) * s ^ 2 + (18276 : ℂ) * s ^ 3 + (12052 : ℂ) * s ^ 4 + (5282 : ℂ) * s ^ 5 + (1336 : ℂ) * s ^ 6 + (142 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-9504 : ℂ) + (-24936 : ℂ) * s + (-28304 : ℂ) * s ^ 2 + (-18605 : ℂ) * s ^ 3 + (-7001 : ℂ) * s ^ 4 + (-1307 : ℂ) * s ^ 5 + (-87 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((6336 : ℂ) + (4464 : ℂ) * s + (-4568 : ℂ) * s ^ 2 + (-7604 : ℂ) * s ^ 3 + (-3440 : ℂ) * s ^ 4 + (-500 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((864 : ℂ) + (5076 : ℂ) * s + (2208 : ℂ) * s ^ 2 + (-696 : ℂ) * s ^ 3 + (-300 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-1296 : ℂ) + (648 : ℂ) * s + (360 : ℂ) * s ^ 2))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI3_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((-96 : ℂ) * s ^ 2 + (-512 : ℂ) * s ^ 3 + (-1048 : ℂ) * s ^ 4 + (-1064 : ℂ) * s ^ 5 + (-568 : ℂ) * s ^ 6 + (-152 : ℂ) * s ^ 7 + (-16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1152 : ℂ) * s + (-5616 : ℂ) * s ^ 2 + (-10720 : ℂ) * s ^ 3 + (-10324 : ℂ) * s ^ 4 + (-5312 : ℂ) * s ^ 5 + (-1388 : ℂ) * s ^ 6 + (-144 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-2016 : ℂ) * s ^ 2 + (-4776 : ℂ) * s ^ 3 + (-3996 : ℂ) * s ^ 4 + (-1416 : ℂ) * s ^ 5 + (-180 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((4896 : ℂ) * s + (13296 : ℂ) * s ^ 2 + (10800 : ℂ) * s ^ 3 + (3528 : ℂ) * s ^ 4 + (408 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-2880 : ℂ) * s + (480 : ℂ) * s ^ 2 + (1560 : ℂ) * s ^ 3 + (360 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-864 : ℂ) * s + (-288 : ℂ) * s ^ 2))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2) := by
  rw [skewFQ_lauI3_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewFSrcLam_lauI3 (s r : ℂ) : ℂ := (((1152 : ℂ) + (4896 : ℂ) * s + (8914 : ℂ) * s ^ 2 + (34807 / 4 : ℂ) * s ^ 3 + (18107 / 4 : ℂ) * s ^ 4 + (12911 / 16 : ℂ) * s ^ 5 + (-3231 / 8 : ℂ) * s ^ 6 + (-2291 / 8 : ℂ) * s ^ 7 + (-74 : ℂ) * s ^ 8 + (-141 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1728 : ℂ) + (25380 : ℂ) * s + (123195 / 2 : ℂ) * s ^ 2 + (286431 / 4 : ℂ) * s ^ 3 + (411525 / 8 : ℂ) * s ^ 4 + (201645 / 8 : ℂ) * s ^ 5 + (8529 : ℂ) * s ^ 6 + (1913 : ℂ) * s ^ 7 + (2121 / 8 : ℂ) * s ^ 8 + (165 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-9720 : ℂ) + (-45720 : ℂ) * s + (-157503 / 2 : ℂ) * s ^ 2 + (-321847 / 4 : ℂ) * s ^ 3 + (-111265 / 2 : ℂ) * s ^ 4 + (-423057 / 16 : ℂ) * s ^ 5 + (-67063 / 8 : ℂ) * s ^ 6 + (-13455 / 8 : ℂ) * s ^ 7 + (-785 / 4 : ℂ) * s ^ 8 + (-189 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((9432 : ℂ) + (8088 : ℂ) * s + (-7389 / 2 : ℂ) * s ^ 2 + (-30467 / 4 : ℂ) * s ^ 3 + (-25439 / 8 : ℂ) * s ^ 4 + (-277 / 2 : ℂ) * s ^ 5 + (837 / 4 : ℂ) * s ^ 6 + (221 / 4 : ℂ) * s ^ 7 + (41 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-2376 : ℂ) + (7308 : ℂ) * s + (23223 / 2 : ℂ) * s ^ 2 + (7707 : ℂ) * s ^ 3 + (2842 : ℂ) * s ^ 4 + (567 : ℂ) * s ^ 5 + (97 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-216 : ℂ) + (12 : ℂ) * s + (323 : ℂ) * s ^ 2 + (62 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((36 : ℂ) * s))))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 3 * (s + 3) ^ 2)

theorem skewFSrc_lauI3_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFSrc_lauI3 s r ((s + 1) * (s + 2)) (ssSourceTR (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2))) = skewFSrcLam_lauI3 s r := by
  unfold skewFSrc_lauI3
  rw [skewPieceFS_lauI3_qtr0 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qtr1 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qtr2 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qt0 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qt1 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qt2 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qT0 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qT1 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qT2 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qT3 s r hr hf hs hs3 hs1]
  unfold skewFSrcLam_lauI3
  simp only [← add_div]
  ring

/-! ## Sources against the reflected family -/

theorem skewPieceSF_qtr0_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr0_lauR s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-1080 : ℂ) * s ^ 2 + (-24345 / 4 : ℂ) * s ^ 3 + (-108285 / 8 : ℂ) * s ^ 4 + (-62667 / 4 : ℂ) * s ^ 5 + (-41583 / 4 : ℂ) * s ^ 6 + (-16347 / 4 : ℂ) * s ^ 7 + (-7509 / 8 : ℂ) * s ^ 8 + (-465 / 4 : ℂ) * s ^ 9 + (-6 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1440 : ℂ) * s + (13821 : ℂ) * s ^ 2 + (75995 / 2 : ℂ) * s ^ 3 + (48019 : ℂ) * s ^ 4 + (142207 / 4 : ℂ) * s ^ 5 + (31987 / 2 : ℂ) * s ^ 6 + (8411 / 2 : ℂ) * s ^ 7 + (1173 / 2 : ℂ) * s ^ 8 + (133 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-10008 : ℂ) * s + (-41970 : ℂ) * s ^ 2 + (-214859 / 4 : ℂ) * s ^ 3 + (-328399 / 8 : ℂ) * s ^ 4 + (-21480 : ℂ) * s ^ 5 + (-27865 / 4 : ℂ) * s ^ 6 + (-4777 / 4 : ℂ) * s ^ 7 + (-647 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((19620 : ℂ) * s + (30990 : ℂ) * s ^ 2 + (21407 : ℂ) * s ^ 3 + (22311 / 2 : ℂ) * s ^ 4 + (9639 / 2 : ℂ) * s ^ 5 + (2409 / 2 : ℂ) * s ^ 6 + (231 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-7992 : ℂ) * s + (-8199 : ℂ) * s ^ 2 + (-5763 / 2 : ℂ) * s ^ 3 + (-800 : ℂ) * s ^ 4 + (-663 / 2 : ℂ) * s ^ 5 + (-60 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((972 : ℂ) * s + (702 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3 + (-30 : ℂ) * s ^ 4))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qtr0_lauR_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr1_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr1_lauR s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((6480 : ℂ) * s ^ 2 + (107973 / 4 : ℂ) * s ^ 3 + (376569 / 8 : ℂ) * s ^ 4 + (179907 / 4 : ℂ) * s ^ 5 + (103419 / 4 : ℂ) * s ^ 6 + (36759 / 4 : ℂ) * s ^ 7 + (15825 / 8 : ℂ) * s ^ 8 + (945 / 4 : ℂ) * s ^ 9 + (12 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-5184 : ℂ) * s + (-42498 : ℂ) * s ^ 2 + (-104724 : ℂ) * s ^ 3 + (-133092 : ℂ) * s ^ 4 + (-398825 / 4 : ℂ) * s ^ 5 + (-45255 : ℂ) * s ^ 6 + (-24287 / 2 : ℂ) * s ^ 7 + (-1763 : ℂ) * s ^ 8 + (-425 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((18036 : ℂ) * s + (86841 : ℂ) * s ^ 2 + (526869 / 4 : ℂ) * s ^ 3 + (922247 / 8 : ℂ) * s ^ 4 + (64786 : ℂ) * s ^ 5 + (88193 / 4 : ℂ) * s ^ 6 + (16071 / 4 : ℂ) * s ^ 7 + (2375 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-27324 : ℂ) * s + (-63654 : ℂ) * s ^ 2 + (-55976 : ℂ) * s ^ 3 + (-32662 : ℂ) * s ^ 4 + (-13810 : ℂ) * s ^ 5 + (-3352 : ℂ) * s ^ 6 + (-326 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((14076 : ℂ) * s + (15105 : ℂ) * s ^ 2 + (12315 / 2 : ℂ) * s ^ 3 + (2070 : ℂ) * s ^ 4 + (1503 / 2 : ℂ) * s ^ 5 + (120 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-1620 : ℂ) * s + (-918 : ℂ) * s ^ 2 + (-18 : ℂ) * s ^ 3 + (36 : ℂ) * s ^ 4))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qtr1_lauR_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr2_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr2_lauR s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((-3240 : ℂ) * s ^ 2 + (-13446 : ℂ) * s ^ 3 + (-23355 : ℂ) * s ^ 4 + (-22233 : ℂ) * s ^ 5 + (-12744 : ℂ) * s ^ 6 + (-4524 : ℂ) * s ^ 7 + (-975 : ℂ) * s ^ 8 + (-117 : ℂ) * s ^ 9 + (-6 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((1728 : ℂ) * s + (18477 : ℂ) * s ^ 2 + (104259 / 2 : ℂ) * s ^ 3 + (143983 / 2 : ℂ) * s ^ 4 + (56815 : ℂ) * s ^ 5 + (26782 : ℂ) * s ^ 6 + (14867 / 2 : ℂ) * s ^ 7 + (2235 / 2 : ℂ) * s ^ 8 + (70 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-5976 : ℂ) * s + (-36861 : ℂ) * s ^ 2 + (-142319 / 2 : ℂ) * s ^ 3 + (-143347 / 2 : ℂ) * s ^ 4 + (-43307 : ℂ) * s ^ 5 + (-15388 : ℂ) * s ^ 6 + (-5803 / 2 : ℂ) * s ^ 7 + (-443 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((7632 : ℂ) * s + (32952 : ℂ) * s ^ 2 + (34832 : ℂ) * s ^ 3 + (21774 : ℂ) * s ^ 4 + (9242 : ℂ) * s ^ 5 + (2218 : ℂ) * s ^ 6 + (214 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-6048 : ℂ) * s + (-7272 : ℂ) * s ^ 2 + (-3264 : ℂ) * s ^ 3 + (-1188 : ℂ) * s ^ 4 + (-408 : ℂ) * s ^ 5 + (-60 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((648 : ℂ) * s + (324 : ℂ) * s ^ 2 + (-12 : ℂ) * s ^ 4))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qtr2_lauR_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt0_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt0_lauR s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((324 : ℂ) * s ^ 3 + (11745 / 16 : ℂ) * s ^ 4 + (5265 / 16 : ℂ) * s ^ 5 + (-357 : ℂ) * s ^ 6 + (-3273 / 8 : ℂ) * s ^ 7 + (-2547 / 16 : ℂ) * s ^ 8 + (-447 / 16 : ℂ) * s ^ 9 + (-15 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-324 : ℂ) * s ^ 2 + (-7137 / 2 : ℂ) * s ^ 3 + (-5931 : ℂ) * s ^ 4 + (-29285 / 8 : ℂ) * s ^ 5 + (-1105 / 2 : ℂ) * s ^ 6 + (370 : ℂ) * s ^ 7 + (761 / 4 : ℂ) * s ^ 8 + (273 / 8 : ℂ) * s ^ 9 + (9 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-2304 : ℂ) * s + (-4611 : ℂ) * s ^ 2 + (663 : ℂ) * s ^ 3 + (91641 / 16 : ℂ) * s ^ 4 + (66853 / 16 : ℂ) * s ^ 5 + (2301 / 2 : ℂ) * s ^ 6 + (463 / 8 : ℂ) * s ^ 7 + (-507 / 16 : ℂ) * s ^ 8 + (-99 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-3168 : ℂ) + (-444 : ℂ) * s + (5361 : ℂ) * s ^ 2 + (6903 / 2 : ℂ) * s ^ 3 + (-3345 / 8 : ℂ) * s ^ 4 + (-3663 / 4 : ℂ) * s ^ 5 + (-513 / 2 : ℂ) * s ^ 6 + (-75 / 4 : ℂ) * s ^ 7 + (5 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((4500 : ℂ) + (4044 : ℂ) * s + (-223 : ℂ) * s ^ 2 + (-966 : ℂ) * s ^ 3 + (-271 / 2 : ℂ) * s ^ 4 + (69 : ℂ) * s ^ 5 + (31 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-1512 : ℂ) + (-1476 : ℂ) * s + (-243 : ℂ) * s ^ 2 + (96 : ℂ) * s ^ 3 + (23 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((180 : ℂ) + (180 : ℂ) * s + (40 : ℂ) * s ^ 2))))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qt0_lauR_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt1_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt1_lauR s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-2160 : ℂ) * s ^ 2 + (-15921 / 2 : ℂ) * s ^ 3 + (-46941 / 4 : ℂ) * s ^ 4 + (-17703 / 2 : ℂ) * s ^ 5 + (-3582 : ℂ) * s ^ 6 + (-1395 / 2 : ℂ) * s ^ 7 + (-81 / 4 : ℂ) * s ^ 8 + (27 / 2 : ℂ) * s ^ 9 + (3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-2880 : ℂ) * s + (-1794 : ℂ) * s ^ 2 + (12508 : ℂ) * s ^ 3 + (94667 / 4 : ℂ) * s ^ 4 + (70915 / 4 : ℂ) * s ^ 5 + (6551 : ℂ) * s ^ 6 + (2201 / 2 : ℂ) * s ^ 7 + (71 / 4 : ℂ) * s ^ 8 + (-69 / 4 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((5040 : ℂ) * s + (8838 : ℂ) * s ^ 2 + (-7117 / 2 : ℂ) * s ^ 3 + (-15270 : ℂ) * s ^ 4 + (-45657 / 4 : ℂ) * s ^ 5 + (-3634 : ℂ) * s ^ 6 + (-457 : ℂ) * s ^ 7 + (4 : ℂ) * s ^ 8 + (15 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2448 : ℂ) * s + (-6396 : ℂ) * s ^ 2 + (-1923 : ℂ) * s ^ 3 + (6867 / 2 : ℂ) * s ^ 4 + (2713 : ℂ) * s ^ 5 + (696 : ℂ) * s ^ 6 + (54 : ℂ) * s ^ 7 + (-3 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((288 : ℂ) * s + (1656 : ℂ) * s ^ 2 + (1042 : ℂ) * s ^ 3 + (-75 : ℂ) * s ^ 4 + (-176 : ℂ) * s ^ 5 + (-31 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-144 : ℂ) * s ^ 2 + (-108 : ℂ) * s ^ 3 + (-20 : ℂ) * s ^ 4))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qt1_lauR_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt2_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt2_lauR s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((1080 : ℂ) * s ^ 2 + (4122 : ℂ) * s ^ 3 + (6411 : ℂ) * s ^ 4 + (5274 : ℂ) * s ^ 5 + (2490 : ℂ) * s ^ 6 + (678 : ℂ) * s ^ 7 + (99 : ℂ) * s ^ 8 + (6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((864 : ℂ) * s + (-711 : ℂ) * s ^ 2 + (-17679 / 2 : ℂ) * s ^ 3 + (-15257 : ℂ) * s ^ 4 + (-12023 : ℂ) * s ^ 5 + (-5065 : ℂ) * s ^ 6 + (-2327 / 2 : ℂ) * s ^ 7 + (-135 : ℂ) * s ^ 8 + (-6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2412 : ℂ) * s + (-2949 : ℂ) * s ^ 2 + (4886 : ℂ) * s ^ 3 + (11488 : ℂ) * s ^ 4 + (8586 : ℂ) * s ^ 5 + (3065 : ℂ) * s ^ 6 + (532 : ℂ) * s ^ 7 + (36 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1728 : ℂ) * s + (3285 : ℂ) * s ^ 2 + (411 / 2 : ℂ) * s ^ 3 + (-2736 : ℂ) * s ^ 4 + (-1931 : ℂ) * s ^ 5 + (-505 : ℂ) * s ^ 6 + (-93 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-180 : ℂ) * s + (-759 : ℂ) * s ^ 2 + (-410 : ℂ) * s ^ 3 + (88 : ℂ) * s ^ 4 + (94 : ℂ) * s ^ 5 + (15 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((54 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 4))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qt2_lauR_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT0_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT0_lauR s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((252 : ℂ) * s ^ 2 + (2217 / 4 : ℂ) * s ^ 3 + (579 / 2 : ℂ) * s ^ 4 + (-201 / 2 : ℂ) * s ^ 5 + (-115 : ℂ) * s ^ 6 + (-119 / 4 : ℂ) * s ^ 7 + (-5 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-528 : ℂ) * s + (-4685 / 2 : ℂ) * s ^ 2 + (-2111 / 2 : ℂ) * s ^ 3 + (609 : ℂ) * s ^ 4 + (717 : ℂ) * s ^ 5 + (529 / 2 : ℂ) * s ^ 6 + (89 / 2 : ℂ) * s ^ 7 + (3 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((2862 : ℂ) * s + (3225 : ℂ) * s ^ 2 + (4521 / 4 : ℂ) * s ^ 3 + (105 / 2 : ℂ) * s ^ 4 + (-243 / 2 : ℂ) * s ^ 5 + (-45 : ℂ) * s ^ 6 + (-27 / 4 : ℂ) * s ^ 7 + (-1 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-3252 : ℂ) * s + (-6265 / 2 : ℂ) * s ^ 2 + (-959 : ℂ) * s ^ 3 + (-133 : ℂ) * s ^ 4 + (9 : ℂ) * s ^ 5 + (7 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((1038 : ℂ) * s + (818 : ℂ) * s ^ 2 + (138 : ℂ) * s ^ 3 + (14 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-120 : ℂ) * s + (-80 : ℂ) * s ^ 2))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qT0_lauR_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT1_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT1_lauR s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-2880 : ℂ) * s + (-11670 : ℂ) * s ^ 2 + (-19113 : ℂ) * s ^ 3 + (-16245 : ℂ) * s ^ 4 + (-7669 : ℂ) * s ^ 5 + (-1999 : ℂ) * s ^ 6 + (-266 : ℂ) * s ^ 7 + (-14 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((14448 : ℂ) * s + (44558 : ℂ) * s ^ 2 + (52998 : ℂ) * s ^ 3 + (30939 : ℂ) * s ^ 4 + (9333 : ℂ) * s ^ 5 + (1345 : ℂ) * s ^ 6 + (61 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-25752 : ℂ) * s + (-55642 : ℂ) * s ^ 2 + (-44245 : ℂ) * s ^ 3 + (-16810 : ℂ) * s ^ 4 + (-3036 : ℂ) * s ^ 5 + (-184 : ℂ) * s ^ 6 + (5 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((19632 : ℂ) * s + (26606 : ℂ) * s ^ 2 + (13864 : ℂ) * s ^ 3 + (3336 : ℂ) * s ^ 4 + (308 : ℂ) * s ^ 5 + (-2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-6072 : ℂ) * s + (-5180 : ℂ) * s ^ 2 + (-1440 : ℂ) * s ^ 3 + (-156 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((624 : ℂ) * s + (320 : ℂ) * s ^ 2))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qT1_lauR_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT2_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT2_lauR s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((6720 : ℂ) * s + (25418 : ℂ) * s ^ 2 + (39067 : ℂ) * s ^ 3 + (31645 : ℂ) * s ^ 4 + (14647 : ℂ) * s ^ 5 + (3889 : ℂ) * s ^ 6 + (550 : ℂ) * s ^ 7 + (32 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-26784 : ℂ) * s + (-85210 : ℂ) * s ^ 2 + (-106794 : ℂ) * s ^ 3 + (-67552 : ℂ) * s ^ 4 + (-22848 : ℂ) * s ^ 5 + (-3934 : ℂ) * s ^ 6 + (-270 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((40404 : ℂ) * s + (102352 : ℂ) * s ^ 2 + (94427 : ℂ) * s ^ 3 + (41515 : ℂ) * s ^ 4 + (8829 : ℂ) * s ^ 5 + (729 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-28128 : ℂ) * s + (-48892 : ℂ) * s ^ 2 + (-29484 : ℂ) * s ^ 3 + (-7684 : ℂ) * s ^ 4 + (-756 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((8580 : ℂ) * s + (7904 : ℂ) * s ^ 2 + (2472 : ℂ) * s ^ 3 + (260 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-792 : ℂ) * s + (-312 : ℂ) * s ^ 2))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qT2_lauR_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT3_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT3_lauR s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((-2880 : ℂ) * s + (-10992 : ℂ) * s ^ 2 + (-17096 : ℂ) * s ^ 3 + (-14064 : ℂ) * s ^ 4 + (-6640 : ℂ) * s ^ 5 + (-1808 : ℂ) * s ^ 6 + (-264 : ℂ) * s ^ 7 + (-16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((11304 : ℂ) * s + (38292 : ℂ) * s ^ 2 + (51408 : ℂ) * s ^ 3 + (34984 : ℂ) * s ^ 4 + (12760 : ℂ) * s ^ 5 + (2372 : ℂ) * s ^ 6 + (176 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-16920 : ℂ) * s + (-48492 : ℂ) * s ^ 2 + (-51688 : ℂ) * s ^ 3 + (-25488 : ℂ) * s ^ 4 + (-5888 : ℂ) * s ^ 5 + (-516 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((11736 : ℂ) * s + (25728 : ℂ) * s ^ 2 + (16992 : ℂ) * s ^ 3 + (4608 : ℂ) * s ^ 4 + (456 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-3528 : ℂ) * s + (-3624 : ℂ) * s ^ 2 + (-1176 : ℂ) * s ^ 3 + (-120 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((288 : ℂ) * s + (96 : ℂ) * s ^ 2))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qT3_lauR_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewSrcFLam_lauR (s r : ℂ) : ℂ := (((960 : ℂ) * s + (4088 : ℂ) * s ^ 2 + (29435 / 4 : ℂ) * s ^ 3 + (115453 / 16 : ℂ) * s ^ 4 + (65057 / 16 : ℂ) * s ^ 5 + (1233 : ℂ) * s ^ 6 + (1125 / 8 : ℂ) * s ^ 7 + (-263 / 16 : ℂ) * s ^ 8 + (-87 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-5592 : ℂ) * s + (-35463 / 2 : ℂ) * s ^ 2 + (-35881 / 2 : ℂ) * s ^ 3 + (-46491 / 4 : ℂ) * s ^ 4 + (-42659 / 8 : ℂ) * s ^ 5 + (-2997 / 2 : ℂ) * s ^ 6 + (-186 : ℂ) * s ^ 7 + (15 : ℂ) * s ^ 8 + (63 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((2970 : ℂ) * s + (10731 : ℂ) * s ^ 2 + (33831 / 4 : ℂ) * s ^ 3 + (60361 / 16 : ℂ) * s ^ 4 + (18121 / 16 : ℂ) * s ^ 5 + (519 / 2 : ℂ) * s ^ 6 + (425 / 8 : ℂ) * s ^ 7 + (37 / 16 : ℂ) * s ^ 8 + (-39 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-3168 : ℂ) + (-1248 : ℂ) * s + (5695 / 2 : ℂ) * s ^ 2 + (2410 : ℂ) * s ^ 3 + (5391 / 8 : ℂ) * s ^ 4 + (539 / 4 : ℂ) * s ^ 5 + (13 / 2 : ℂ) * s ^ 6 + (-31 / 4 : ℂ) * s ^ 7 + (-7 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((4500 : ℂ) + (4206 : ℂ) * s + (226 : ℂ) * s ^ 2 + (-328 : ℂ) * s ^ 3 + (-85 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-1512 : ℂ) + (-1476 : ℂ) * s + (-201 : ℂ) * s ^ 2 + (42 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((180 : ℂ) + (180 : ℂ) * s + (40 : ℂ) * s ^ 2))))))))))))) / (r ^ 4 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3)

theorem skewSrcF_lauR_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewSrcF_lauR s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = skewSrcFLam_lauR s r := by
  unfold skewSrcF_lauR
  rw [skewPieceSF_qtr0_lauR s r hr hf hs hs3 hs1, skewPieceSF_qtr1_lauR s r hr hf hs hs3 hs1, skewPieceSF_qtr2_lauR s r hr hf hs hs3 hs1, skewPieceSF_qt0_lauR s r hr hf hs hs3 hs1, skewPieceSF_qt1_lauR s r hr hf hs hs3 hs1, skewPieceSF_qt2_lauR s r hr hf hs hs3 hs1, skewPieceSF_qT0_lauR s r hr hf hs hs3 hs1, skewPieceSF_qT1_lauR s r hr hf hs hs3 hs1, skewPieceSF_qT2_lauR s r hr hf hs hs3 hs1, skewPieceSF_qT3_lauR s r hr hf hs hs3 hs1]
  unfold skewSrcFLam_lauR
  simp only [← add_div]
  ring

theorem skewPieceSF_qtr0_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr0_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-216 : ℂ) * s ^ 2 + (-4131 / 4 : ℂ) * s ^ 3 + (-16269 / 8 : ℂ) * s ^ 4 + (-17043 / 8 : ℂ) * s ^ 5 + (-10233 / 8 : ℂ) * s ^ 6 + (-3519 / 8 : ℂ) * s ^ 7 + (-321 / 4 : ℂ) * s ^ 8 + (-6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((288 : ℂ) * s + (2430 : ℂ) * s ^ 2 + (5572 : ℂ) * s ^ 3 + (5822 : ℂ) * s ^ 4 + (13309 / 4 : ℂ) * s ^ 5 + (4395 / 4 : ℂ) * s ^ 6 + (795 / 4 : ℂ) * s ^ 7 + (61 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1884 : ℂ) * s + (-5968 : ℂ) * s ^ 2 + (-19009 / 4 : ℂ) * s ^ 3 + (-18447 / 8 : ℂ) * s ^ 4 + (-5019 / 8 : ℂ) * s ^ 5 + (-429 / 8 : ℂ) * s ^ 6 + (25 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((3048 : ℂ) * s + (1121 : ℂ) * s ^ 2 + (-575 / 2 : ℂ) * s ^ 3 + (-238 : ℂ) * s ^ 4 + (-159 / 2 : ℂ) * s ^ 5 + (-12 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((108 : ℂ) * s + (309 : ℂ) * s ^ 2 + (389 / 2 : ℂ) * s ^ 3 + (213 / 2 : ℂ) * s ^ 4 + (24 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-216 : ℂ) * s + (-36 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewQF_qtr0_lauI1_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr1_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr1_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((1350 : ℂ) * s ^ 2 + (21195 / 4 : ℂ) * s ^ 3 + (68433 / 8 : ℂ) * s ^ 4 + (59127 / 8 : ℂ) * s ^ 5 + (29733 / 8 : ℂ) * s ^ 6 + (8763 / 8 : ℂ) * s ^ 7 + (705 / 4 : ℂ) * s ^ 8 + (12 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-1080 : ℂ) * s + (-8037 : ℂ) * s ^ 2 + (-35355 / 2 : ℂ) * s ^ 3 + (-19942 : ℂ) * s ^ 4 + (-51985 / 4 : ℂ) * s ^ 5 + (-19555 / 4 : ℂ) * s ^ 6 + (-3937 / 4 : ℂ) * s ^ 7 + (-329 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3312 : ℂ) * s + (13851 : ℂ) * s ^ 2 + (65239 / 4 : ℂ) * s ^ 3 + (89531 / 8 : ℂ) * s ^ 4 + (39391 / 8 : ℂ) * s ^ 5 + (9609 / 8 : ℂ) * s ^ 6 + (951 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-4248 : ℂ) * s + (-5841 : ℂ) * s ^ 2 + (-4093 / 2 : ℂ) * s ^ 3 + (-261 : ℂ) * s ^ 4 + (67 / 2 : ℂ) * s ^ 5 + (19 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((912 : ℂ) * s + (-719 : ℂ) * s ^ 2 + (-1405 / 2 : ℂ) * s ^ 3 + (-721 / 2 : ℂ) * s ^ 4 + (-80 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((432 : ℂ) * s + (72 : ℂ) * s ^ 2 + (-24 : ℂ) * s ^ 3))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewQF_qtr1_lauI1_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr2_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr2_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((-810 : ℂ) * s ^ 2 + (-3159 : ℂ) * s ^ 3 + (-5049 : ℂ) * s ^ 4 + (-4296 : ℂ) * s ^ 5 + (-2112 : ℂ) * s ^ 6 + (-603 : ℂ) * s ^ 7 + (-93 : ℂ) * s ^ 8 + (-6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((432 : ℂ) * s + (4275 : ℂ) * s ^ 2 + (22107 / 2 : ℂ) * s ^ 3 + (13802 : ℂ) * s ^ 4 + (9557 : ℂ) * s ^ 5 + (3731 : ℂ) * s ^ 6 + (1531 / 2 : ℂ) * s ^ 7 + (64 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1368 : ℂ) * s + (-7593 : ℂ) * s ^ 2 + (-25173 / 2 : ℂ) * s ^ 3 + (-10688 : ℂ) * s ^ 4 + (-5379 : ℂ) * s ^ 5 + (-1447 : ℂ) * s ^ 6 + (-309 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((1488 : ℂ) * s + (5464 : ℂ) * s ^ 2 + (3288 : ℂ) * s ^ 3 + (1126 : ℂ) * s ^ 4 + (272 : ℂ) * s ^ 5 + (26 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-1008 : ℂ) * s + (384 : ℂ) * s ^ 2 + (528 : ℂ) * s ^ 3 + (276 : ℂ) * s ^ 4 + (60 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-216 : ℂ) * s + (-36 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewQF_qtr2_lauI1_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt0_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt0_lauI1 s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((9 / 2 : ℂ) * s ^ 3 + (-417 / 16 : ℂ) * s ^ 4 + (-861 / 8 : ℂ) * s ^ 5 + (-1077 / 8 : ℂ) * s ^ 6 + (-75 : ℂ) * s ^ 7 + (-309 / 16 : ℂ) * s ^ 8 + (-15 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-231 : ℂ) * s ^ 2 + (-2915 / 4 : ℂ) * s ^ 3 + (-2849 / 4 : ℂ) * s ^ 4 + (-1713 / 8 : ℂ) * s ^ 5 + (547 / 8 : ℂ) * s ^ 6 + (577 / 8 : ℂ) * s ^ 7 + (171 / 8 : ℂ) * s ^ 8 + (9 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-636 : ℂ) * s + (-611 : ℂ) * s ^ 2 + (517 / 2 : ℂ) * s ^ 3 + (9423 / 16 : ℂ) * s ^ 4 + (2397 / 8 : ℂ) * s ^ 5 + (549 / 8 : ℂ) * s ^ 6 + (15 / 4 : ℂ) * s ^ 7 + (-33 / 16 : ℂ) * s ^ 8 + (-3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-648 : ℂ) + (174 : ℂ) * s + (694 : ℂ) * s ^ 2 + (1865 / 4 : ℂ) * s ^ 3 + (1399 / 8 : ℂ) * s ^ 4 + (225 / 8 : ℂ) * s ^ 5 + (-19 / 8 : ℂ) * s ^ 6 + (-7 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((588 : ℂ) + (460 : ℂ) * s + (175 : ℂ) * s ^ 2 + (13 / 2 : ℂ) * s ^ 3 + (-51 / 2 : ℂ) * s ^ 4 + (-6 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((96 : ℂ) + (14 : ℂ) * s + (-27 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-36 : ℂ) + (-12 : ℂ) * s))))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewQF_qt0_lauI1_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt1_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt1_lauI1 s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-432 : ℂ) * s ^ 2 + (-2961 / 2 : ℂ) * s ^ 3 + (-7875 / 4 : ℂ) * s ^ 4 + (-5091 / 4 : ℂ) * s ^ 5 + (-1587 / 4 : ℂ) * s ^ 6 + (-153 / 4 : ℂ) * s ^ 7 + (15 / 2 : ℂ) * s ^ 8 + (3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-576 : ℂ) * s + (-408 : ℂ) * s ^ 2 + (1902 : ℂ) * s ^ 3 + (13093 / 4 : ℂ) * s ^ 4 + (4109 / 2 : ℂ) * s ^ 5 + (1129 / 2 : ℂ) * s ^ 6 + (41 : ℂ) * s ^ 7 + (-39 / 4 : ℂ) * s ^ 8 + (-3 / 2 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((744 : ℂ) * s + (1400 : ℂ) * s ^ 2 + (-165 / 2 : ℂ) * s ^ 3 + (-1285 : ℂ) * s ^ 4 + (-3225 / 4 : ℂ) * s ^ 5 + (-705 / 4 : ℂ) * s ^ 6 + (-17 / 4 : ℂ) * s ^ 7 + (9 / 4 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-96 : ℂ) * s + (-566 : ℂ) * s ^ 2 + (-439 : ℂ) * s ^ 3 + (-213 / 2 : ℂ) * s ^ 4 + (11 / 2 : ℂ) * s ^ 5 + (17 / 2 : ℂ) * s ^ 6 + (3 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-72 : ℂ) * s + (-30 : ℂ) * s ^ 2 + (88 : ℂ) * s ^ 3 + (87 : ℂ) * s ^ 4 + (19 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((36 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewQF_qt1_lauI1_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt2_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt2_lauI1 s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((270 : ℂ) * s ^ 2 + (963 : ℂ) * s ^ 3 + (1362 : ℂ) * s ^ 4 + (978 : ℂ) * s ^ 5 + (378 : ℂ) * s ^ 6 + (75 : ℂ) * s ^ 7 + (6 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((216 : ℂ) * s + (-153 : ℂ) * s ^ 2 + (-3789 / 2 : ℂ) * s ^ 3 + (-5911 / 2 : ℂ) * s ^ 4 + (-3993 / 2 : ℂ) * s ^ 5 + (-1331 / 2 : ℂ) * s ^ 6 + (-105 : ℂ) * s ^ 7 + (-6 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-540 : ℂ) * s + (-663 : ℂ) * s ^ 2 + (796 : ℂ) * s ^ 3 + (1786 : ℂ) * s ^ 4 + (1122 : ℂ) * s ^ 5 + (301 : ℂ) * s ^ 6 + (30 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((264 : ℂ) * s + (583 : ℂ) * s ^ 2 + (477 / 2 : ℂ) * s ^ 3 + (-239 / 2 : ℂ) * s ^ 4 + (-177 / 2 : ℂ) * s ^ 5 + (-27 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((60 : ℂ) * s + (-19 : ℂ) * s ^ 2 + (-97 : ℂ) * s ^ 3 + (-73 : ℂ) * s ^ 4 + (-15 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((-18 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewQF_qt2_lauI1_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT0_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT0_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((-5 : ℂ) * s ^ 2 + (-113 / 4 : ℂ) * s ^ 3 + (-219 / 4 : ℂ) * s ^ 4 + (-189 / 4 : ℂ) * s ^ 5 + (-73 / 4 : ℂ) * s ^ 6 + (-5 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-108 : ℂ) * s + (-221 / 2 : ℂ) * s ^ 2 + (210 : ℂ) * s ^ 3 + (308 : ℂ) * s ^ 4 + (130 : ℂ) * s ^ 5 + (55 / 2 : ℂ) * s ^ 6 + (3 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((530 : ℂ) * s + (-88 : ℂ) * s ^ 2 + (-277 / 4 : ℂ) * s ^ 3 + (-11 / 4 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 5 + (-5 / 4 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-376 : ℂ) * s + (-397 / 2 : ℂ) * s ^ 2 + (-65 / 2 : ℂ) * s ^ 3 + (3 / 2 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-70 : ℂ) * s + (-18 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((24 : ℂ) * s))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewQF_qT0_lauI1_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT1_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT1_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-576 : ℂ) * s + (-2078 : ℂ) * s ^ 2 + (-2991 : ℂ) * s ^ 3 + (-2202 : ℂ) * s ^ 4 + (-877 : ℂ) * s ^ 5 + (-178 : ℂ) * s ^ 6 + (-14 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((2616 : ℂ) * s + (6698 : ℂ) * s ^ 2 + (6292 : ℂ) * s ^ 3 + (2673 : ℂ) * s ^ 4 + (488 : ℂ) * s ^ 5 + (23 : ℂ) * s ^ 6 + (-2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-3832 : ℂ) * s + (-5654 : ℂ) * s ^ 2 + (-2483 : ℂ) * s ^ 3 + (-353 : ℂ) * s ^ 4 + (3 : ℂ) * s ^ 5 + (3 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((1752 : ℂ) * s + (422 : ℂ) * s ^ 2 + (-86 : ℂ) * s ^ 3 + (-30 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((184 : ℂ) * s + (276 : ℂ) * s ^ 2 + (68 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-144 : ℂ) * s))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewQF_qT1_lauI1_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT2_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT2_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((1440 : ℂ) * s + (5086 : ℂ) * s ^ 2 + (7119 : ℂ) * s ^ 3 + (5066 : ℂ) * s ^ 4 + (1951 : ℂ) * s ^ 5 + (390 : ℂ) * s ^ 6 + (32 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-5168 : ℂ) * s + (-14910 : ℂ) * s ^ 2 + (-16288 : ℂ) * s ^ 3 + (-8448 : ℂ) * s ^ 4 + (-2108 : ℂ) * s ^ 5 + (-206 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((6508 : ℂ) * s + (13940 : ℂ) * s ^ 2 + (9677 : ℂ) * s ^ 3 + (2810 : ℂ) * s ^ 4 + (289 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-3056 : ℂ) * s + (-3012 : ℂ) * s ^ 2 + (-572 : ℂ) * s ^ 3 + (48 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((60 : ℂ) * s + (-684 : ℂ) * s ^ 2 + (-180 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((216 : ℂ) * s))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewQF_qT2_lauI1_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT3_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT3_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((-720 : ℂ) * s + (-2568 : ℂ) * s ^ 2 + (-3632 : ℂ) * s ^ 3 + (-2608 : ℂ) * s ^ 4 + (-1008 : ℂ) * s ^ 5 + (-200 : ℂ) * s ^ 6 + (-16 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((2616 : ℂ) * s + (8180 : ℂ) * s ^ 2 + (9780 : ℂ) * s ^ 3 + (5580 : ℂ) * s ^ 4 + (1524 : ℂ) * s ^ 5 + (160 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-3432 : ℂ) * s + (-8804 : ℂ) * s ^ 2 + (-7836 : ℂ) * s ^ 3 + (-2812 : ℂ) * s ^ 4 + (-348 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((1800 : ℂ) * s + (3096 : ℂ) * s ^ 2 + (936 : ℂ) * s ^ 3 + (24 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * (((-168 : ℂ) * s + (432 : ℂ) * s ^ 2 + (120 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-96 : ℂ) * s))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2) := by
  rw [skewQF_qT3_lauI1_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewSrcFLam_lauI1 (s r : ℂ) : ℂ := (((144 : ℂ) * s + (597 : ℂ) * s ^ 2 + (4247 / 4 : ℂ) * s ^ 3 + (16639 / 16 : ℂ) * s ^ 4 + (4647 / 8 : ℂ) * s ^ 5 + (1327 / 8 : ℂ) * s ^ 6 + (55 / 4 : ℂ) * s ^ 7 + (-45 / 16 : ℂ) * s ^ 8 + (-3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-764 : ℂ) * s + (-4533 / 2 : ℂ) * s ^ 2 + (-7117 / 4 : ℂ) * s ^ 3 + (-1199 / 2 : ℂ) * s ^ 4 + (-1873 / 8 : ℂ) * s ^ 5 + (-697 / 8 : ℂ) * s ^ 6 + (-87 / 8 : ℂ) * s ^ 7 + (21 / 8 : ℂ) * s ^ 8 + (3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-598 : ℂ) * s + (-190 : ℂ) * s ^ 2 + (-3073 / 4 : ℂ) * s ^ 3 + (-17125 / 16 : ℂ) * s ^ 4 + (-4187 / 8 : ℂ) * s ^ 5 + (-835 / 8 : ℂ) * s ^ 6 + (-7 / 2 : ℂ) * s ^ 7 + (3 / 16 : ℂ) * s ^ 8 + (-3 / 8 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-648 : ℂ) + (750 : ℂ) * s + (3525 / 2 : ℂ) * s ^ 2 + (5861 / 4 : ℂ) * s ^ 3 + (4955 / 8 : ℂ) * s ^ 4 + (1397 / 8 : ℂ) * s ^ 5 + (205 / 8 : ℂ) * s ^ 6 + (5 / 8 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((588 : ℂ) + (466 : ℂ) * s + (106 : ℂ) * s ^ 2 + (43 / 2 : ℂ) * s ^ 3 + (21 / 2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((96 : ℂ) + (14 : ℂ) * s + (-9 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 3) + r * ((0 : ℂ) + r * ((-36 : ℂ) + (-12 : ℂ) * s))))))))))))) / (r ^ 6 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 2)

theorem skewSrcF_lauI1_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewSrcF_lauI1 s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = skewSrcFLam_lauI1 s r := by
  unfold skewSrcF_lauI1
  rw [skewPieceSF_qtr0_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qtr1_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qtr2_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qt0_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qt1_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qt2_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qT0_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qT1_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qT2_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qT3_lauI1 s r hr hf hs hs3 hs1]
  unfold skewSrcFLam_lauI1
  simp only [← add_div]
  ring

theorem skewPieceSF_qtr0_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr0_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-324 : ℂ) * s ^ 2 + (-6129 / 4 : ℂ) * s ^ 3 + (-25533 / 8 : ℂ) * s ^ 4 + (-15435 / 4 : ℂ) * s ^ 5 + (-11871 / 4 : ℂ) * s ^ 6 + (-5907 / 4 : ℂ) * s ^ 7 + (-3669 / 8 : ℂ) * s ^ 8 + (-321 / 4 : ℂ) * s ^ 9 + (-6 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((432 : ℂ) * s + (3339 : ℂ) * s ^ 2 + (15153 / 2 : ℂ) * s ^ 3 + (8259 : ℂ) * s ^ 4 + (18327 / 4 : ℂ) * s ^ 5 + (2303 / 2 : ℂ) * s ^ 6 + (97 / 2 : ℂ) * s ^ 7 + (-51 / 2 : ℂ) * s ^ 8 + (-11 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2448 : ℂ) * s + (-6042 : ℂ) * s ^ 2 + (-7523 / 4 : ℂ) * s ^ 3 + (26225 / 8 : ℂ) * s ^ 4 + (3552 : ℂ) * s ^ 5 + (7127 / 4 : ℂ) * s ^ 6 + (1903 / 4 : ℂ) * s ^ 7 + (409 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1836 : ℂ) * s + (-5796 : ℂ) * s ^ 2 + (-8412 : ℂ) * s ^ 3 + (-10217 / 2 : ℂ) * s ^ 4 + (-3085 / 2 : ℂ) * s ^ 5 + (-403 / 2 : ℂ) * s ^ 6 + (-15 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((5184 : ℂ) * s + (3357 : ℂ) * s ^ 2 + (1941 / 2 : ℂ) * s ^ 3 + (516 : ℂ) * s ^ 4 + (321 / 2 : ℂ) * s ^ 5 + (12 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-972 : ℂ) * s + (-270 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 4))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qtr0_lauI3_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr1_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr1_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((2160 : ℂ) * s ^ 2 + (38421 / 4 : ℂ) * s ^ 3 + (145257 / 8 : ℂ) * s ^ 4 + (76587 / 4 : ℂ) * s ^ 5 + (49587 / 4 : ℂ) * s ^ 6 + (20319 / 4 : ℂ) * s ^ 7 + (10353 / 8 : ℂ) * s ^ 8 + (753 / 4 : ℂ) * s ^ 9 + (12 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-1728 : ℂ) * s + (-11952 : ℂ) * s ^ 2 + (-27825 : ℂ) * s ^ 3 + (-35017 : ℂ) * s ^ 4 + (-109301 / 4 : ℂ) * s ^ 5 + (-13604 : ℂ) * s ^ 6 + (-8431 / 2 : ℂ) * s ^ 7 + (-747 : ℂ) * s ^ 8 + (-233 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((3852 : ℂ) * s + (13869 : ℂ) * s ^ 2 + (51397 / 4 : ℂ) * s ^ 3 + (25319 / 8 : ℂ) * s ^ 4 + (-1602 : ℂ) * s ^ 5 + (-5103 / 4 : ℂ) * s ^ 6 + (-1369 / 4 : ℂ) * s ^ 7 + (-281 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-2196 : ℂ) * s + (7116 : ℂ) * s ^ 2 + (16737 : ℂ) * s ^ 3 + (15777 : ℂ) * s ^ 4 + (7803 : ℂ) * s ^ 5 + (2019 : ℂ) * s ^ 6 + (216 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-4860 : ℂ) * s + (-10971 : ℂ) * s ^ 2 + (-14325 / 2 : ℂ) * s ^ 3 + (-3342 : ℂ) * s ^ 4 + (-2049 / 2 : ℂ) * s ^ 5 + (-120 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((2916 : ℂ) * s + (1134 : ℂ) * s ^ 2 + (-54 : ℂ) * s ^ 3 + (-36 : ℂ) * s ^ 4))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qtr1_lauI3_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr2_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr2_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((-1620 : ℂ) * s ^ 2 + (-7128 : ℂ) * s ^ 3 + (-13257 : ℂ) * s ^ 4 + (-13641 : ℂ) * s ^ 5 + (-8520 : ℂ) * s ^ 6 + (-3318 : ℂ) * s ^ 7 + (-789 : ℂ) * s ^ 8 + (-105 : ℂ) * s ^ 9 + (-6 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((864 : ℂ) * s + (8037 : ℂ) * s ^ 2 + (45483 / 2 : ℂ) * s ^ 3 + (65855 / 2 : ℂ) * s ^ 4 + (28131 : ℂ) * s ^ 5 + (14718 : ℂ) * s ^ 6 + (9243 / 2 : ℂ) * s ^ 7 + (1595 / 2 : ℂ) * s ^ 8 + (58 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-2232 : ℂ) * s + (-11433 : ℂ) * s ^ 2 + (-39091 / 2 : ℂ) * s ^ 3 + (-35255 / 2 : ℂ) * s ^ 4 + (-10343 : ℂ) * s ^ 5 + (-4052 : ℂ) * s ^ 6 + (-1839 / 2 : ℂ) * s ^ 7 + (-175 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((1296 : ℂ) * s + (2808 : ℂ) * s ^ 2 + (-4176 : ℂ) * s ^ 3 + (-8442 : ℂ) * s ^ 4 + (-5358 : ℂ) * s ^ 5 + (-1518 : ℂ) * s ^ 6 + (-162 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((7560 : ℂ) * s ^ 2 + (7200 : ℂ) * s ^ 3 + (3900 : ℂ) * s ^ 4 + (1320 : ℂ) * s ^ 5 + (180 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-1944 : ℂ) * s + (-972 : ℂ) * s ^ 2 + (36 : ℂ) * s ^ 4))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qtr2_lauI3_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt0_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt0_lauI3 s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((-72 : ℂ) * s ^ 3 + (-4839 / 16 : ℂ) * s ^ 4 + (-8559 / 16 : ℂ) * s ^ 5 + (-522 : ℂ) * s ^ 6 + (-2457 / 8 : ℂ) * s ^ 7 + (-1755 / 16 : ℂ) * s ^ 8 + (-351 / 16 : ℂ) * s ^ 9 + (-15 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-570 : ℂ) * s ^ 2 + (-1621 : ℂ) * s ^ 3 + (-1689 : ℂ) * s ^ 4 + (-5413 / 8 : ℂ) * s ^ 5 + (149 / 2 : ℂ) * s ^ 6 + (381 / 2 : ℂ) * s ^ 7 + (365 / 4 : ℂ) * s ^ 8 + (177 / 8 : ℂ) * s ^ 9 + (9 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-1200 : ℂ) * s + (-1891 : ℂ) * s ^ 2 + (-803 : ℂ) * s ^ 3 + (7617 / 16 : ℂ) * s ^ 4 + (11669 / 16 : ℂ) * s ^ 5 + (753 / 2 : ℂ) * s ^ 6 + (887 / 8 : ℂ) * s ^ 7 + (285 / 16 : ℂ) * s ^ 8 + (-3 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-1008 : ℂ) + (-1032 : ℂ) * s + (827 : ℂ) * s ^ 2 + (2021 : ℂ) * s ^ 3 + (11879 / 8 : ℂ) * s ^ 4 + (1945 / 4 : ℂ) * s ^ 5 + (141 / 2 : ℂ) * s ^ 6 + (23 / 4 : ℂ) * s ^ 7 + (5 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-108 : ℂ) + (1692 : ℂ) * s + (1629 : ℂ) * s ^ 2 + (483 : ℂ) * s ^ 3 + (55 / 2 : ℂ) * s ^ 4 + (-4 : ℂ) * s ^ 5 + (1 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((1224 : ℂ) + (576 : ℂ) * s + (5 : ℂ) * s ^ 2 + (-8 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-108 : ℂ) + (-36 : ℂ) * s))))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qt0_lauI3_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt1_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt1_lauI3 s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-648 : ℂ) * s ^ 2 + (-5085 / 2 : ℂ) * s ^ 3 + (-16233 / 4 : ℂ) * s ^ 4 + (-6765 / 2 : ℂ) * s ^ 5 + (-1548 : ℂ) * s ^ 6 + (-699 / 2 : ℂ) * s ^ 7 + (-45 / 4 : ℂ) * s ^ 8 + (21 / 2 : ℂ) * s ^ 9 + (3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-864 : ℂ) * s + (-1662 : ℂ) * s ^ 2 + (364 : ℂ) * s ^ 3 + (13171 / 4 : ℂ) * s ^ 4 + (13619 / 4 : ℂ) * s ^ 5 + (1605 : ℂ) * s ^ 6 + (693 / 2 : ℂ) * s ^ 7 + (23 / 4 : ℂ) * s ^ 8 + (-45 / 4 : ℂ) * s ^ 9 + (-3 / 2 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((288 : ℂ) * s + (2058 : ℂ) * s ^ 2 + (7431 / 2 : ℂ) * s ^ 3 + (2999 : ℂ) * s ^ 4 + (4747 / 4 : ℂ) * s ^ 5 + (208 : ℂ) * s ^ 6 + (7 : ℂ) * s ^ 7 + (1 : ℂ) * s ^ 8 + (3 / 4 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((1008 : ℂ) * s + (1080 : ℂ) * s ^ 2 + (-1495 : ℂ) * s ^ 3 + (-5317 / 2 : ℂ) * s ^ 4 + (-1393 : ℂ) * s ^ 5 + (-286 : ℂ) * s ^ 6 + (-4 : ℂ) * s ^ 7 + (9 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-432 : ℂ) * s + (-1044 : ℂ) * s ^ 2 + (-150 : ℂ) * s ^ 3 + (413 : ℂ) * s ^ 4 + (184 : ℂ) * s ^ 5 + (21 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((216 : ℂ) * s ^ 2 + (108 : ℂ) * s ^ 3 + (12 : ℂ) * s ^ 4))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qt1_lauI3_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt2_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt2_lauI3 s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((540 : ℂ) * s ^ 2 + (2196 : ℂ) * s ^ 3 + (3687 : ℂ) * s ^ 4 + (3318 : ℂ) * s ^ 5 + (1734 : ℂ) * s ^ 6 + (528 : ℂ) * s ^ 7 + (87 : ℂ) * s ^ 8 + (6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((432 : ℂ) * s + (225 : ℂ) * s ^ 2 + (-5667 / 2 : ℂ) * s ^ 3 + (-6265 : ℂ) * s ^ 4 + (-5867 : ℂ) * s ^ 5 + (-2921 : ℂ) * s ^ 6 + (-1595 / 2 : ℂ) * s ^ 7 + (-111 : ℂ) * s ^ 8 + (-6 : ℂ) * s ^ 9) + r * ((0 : ℂ) + r * (((-828 : ℂ) * s + (-2109 : ℂ) * s ^ 2 + (-1436 : ℂ) * s ^ 3 + (820 : ℂ) * s ^ 4 + (1718 : ℂ) * s ^ 5 + (985 : ℂ) * s ^ 6 + (250 : ℂ) * s ^ 7 + (24 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-144 : ℂ) * s + (741 : ℂ) * s ^ 2 + (4783 / 2 : ℂ) * s ^ 3 + (2496 : ℂ) * s ^ 4 + (1161 : ℂ) * s ^ 5 + (247 : ℂ) * s ^ 6 + (39 / 2 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((540 : ℂ) * s + (765 : ℂ) * s ^ 2 + (-210 : ℂ) * s ^ 3 + (-720 : ℂ) * s ^ 4 + (-330 : ℂ) * s ^ 5 + (-45 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * ((-162 : ℂ) * s ^ 2 + (-108 : ℂ) * s ^ 3 + (-18 : ℂ) * s ^ 4))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qt2_lauI3_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT0_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT0_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((-82 : ℂ) * s ^ 2 + (-1095 / 4 : ℂ) * s ^ 3 + (-717 / 2 : ℂ) * s ^ 4 + (-481 / 2 : ℂ) * s ^ 5 + (-93 : ℂ) * s ^ 6 + (-87 / 4 : ℂ) * s ^ 7 + (-5 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-168 : ℂ) * s + (143 / 2 : ℂ) * s ^ 2 + (1365 / 2 : ℂ) * s ^ 3 + (927 : ℂ) * s ^ 4 + (571 : ℂ) * s ^ 5 + (345 / 2 : ℂ) * s ^ 6 + (57 / 2 : ℂ) * s ^ 7 + (3 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((654 : ℂ) * s + (3 : ℂ) * s ^ 2 + (-471 / 4 : ℂ) * s ^ 3 + (649 / 2 : ℂ) * s ^ 4 + (349 / 2 : ℂ) * s ^ 5 + (25 : ℂ) * s ^ 6 + (5 / 4 : ℂ) * s ^ 7 + (-1 / 2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((276 : ℂ) * s + (-1909 / 2 : ℂ) * s ^ 2 + (-445 : ℂ) * s ^ 3 + (-55 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5 + (7 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-834 : ℂ) * s + (-298 : ℂ) * s ^ 2 + (-38 : ℂ) * s ^ 3 + (-6 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((72 : ℂ) * s))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qT0_lauI3_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT1_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT1_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-864 : ℂ) * s + (-3406 : ℂ) * s ^ 2 + (-5597 : ℂ) * s ^ 3 + (-5045 : ℂ) * s ^ 4 + (-2749 : ℂ) * s ^ 5 + (-919 : ℂ) * s ^ 6 + (-174 : ℂ) * s ^ 7 + (-14 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((3072 : ℂ) * s + (8350 : ℂ) * s ^ 2 + (8582 : ℂ) * s ^ 3 + (4083 : ℂ) * s ^ 4 + (765 : ℂ) * s ^ 5 + (-39 : ℂ) * s ^ 6 + (-27 : ℂ) * s ^ 7 + (-2 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-1752 : ℂ) * s + (-330 : ℂ) * s ^ 2 + (3207 : ℂ) * s ^ 3 + (2958 : ℂ) * s ^ 4 + (956 : ℂ) * s ^ 5 + (112 : ℂ) * s ^ 6 + (1 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-3648 : ℂ) * s + (-7930 : ℂ) * s ^ 2 + (-4736 : ℂ) * s ^ 3 + (-968 : ℂ) * s ^ 4 + (-36 : ℂ) * s ^ 5 + (6 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((3912 : ℂ) * s + (2404 : ℂ) * s ^ 2 + (608 : ℂ) * s ^ 3 + (36 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-720 : ℂ) * s + (-96 : ℂ) * s ^ 2))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qT1_lauI3_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT2_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT2_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((2400 : ℂ) * s + (9690 : ℂ) * s ^ 2 + (16187 : ℂ) * s ^ 3 + (14573 : ℂ) * s ^ 4 + (7703 : ℂ) * s ^ 5 + (2417 : ℂ) * s ^ 6 + (422 : ℂ) * s ^ 7 + (32 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-6720 : ℂ) * s + (-22442 : ℂ) * s ^ 2 + (-30162 : ℂ) * s ^ 3 + (-21008 : ℂ) * s ^ 4 + (-8072 : ℂ) * s ^ 5 + (-1646 : ℂ) * s ^ 6 + (-142 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((3828 : ℂ) * s + (8272 : ℂ) * s ^ 2 + (5243 : ℂ) * s ^ 3 + (859 : ℂ) * s ^ 4 + (-259 : ℂ) * s ^ 5 + (-87 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((4416 : ℂ) * s + (13108 : ℂ) * s ^ 2 + (11324 : ℂ) * s ^ 3 + (4060 : ℂ) * s ^ 4 + (500 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((-5436 : ℂ) * s + (-7728 : ℂ) * s ^ 2 + (-2904 : ℂ) * s ^ 3 + (-300 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((1512 : ℂ) * s + (360 : ℂ) * s ^ 2))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qT2_lauI3_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT3_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT3_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((-1440 : ℂ) * s + (-5856 : ℂ) * s ^ 2 + (-9832 : ℂ) * s ^ 3 + (-8848 : ℂ) * s ^ 4 + (-4624 : ℂ) * s ^ 5 + (-1408 : ℂ) * s ^ 6 + (-232 : ℂ) * s ^ 7 + (-16 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((4392 : ℂ) * s + (16020 : ℂ) * s ^ 2 + (23632 : ℂ) * s ^ 3 + (18056 : ℂ) * s ^ 4 + (7544 : ℂ) * s ^ 5 + (1636 : ℂ) * s ^ 6 + (144 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((-3672 : ℂ) * s + (-11196 : ℂ) * s ^ 2 + (-12936 : ℂ) * s ^ 3 + (-7056 : ℂ) * s ^ 4 + (-1824 : ℂ) * s ^ 5 + (-180 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((-936 : ℂ) * s + (-3552 : ℂ) * s ^ 2 + (-5184 : ℂ) * s ^ 3 + (-2592 : ℂ) * s ^ 4 + (-408 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * (((2520 : ℂ) * s + (5880 : ℂ) * s ^ 2 + (2760 : ℂ) * s ^ 3 + (360 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-864 : ℂ) * s + (-288 : ℂ) * s ^ 2))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3) := by
  rw [skewQF_qT3_lauI3_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewSrcFLam_lauI3 (s r : ℂ) : ℂ := (((96 : ℂ) * s + (454 : ℂ) * s ^ 2 + (4043 / 4 : ℂ) * s ^ 3 + (21701 / 16 : ℂ) * s ^ 4 + (18193 / 16 : ℂ) * s ^ 5 + (570 : ℂ) * s ^ 6 + (1205 / 8 : ℂ) * s ^ 7 + (193 / 16 : ℂ) * s ^ 8 + (-39 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-288 : ℂ) * s + (-1167 / 2 : ℂ) * s ^ 2 + (1137 : ℂ) * s ^ 3 + (14265 / 4 : ℂ) * s ^ 4 + (24453 / 8 : ℂ) * s ^ 5 + (2295 / 2 : ℂ) * s ^ 6 + (395 / 2 : ℂ) * s ^ 7 + (12 : ℂ) * s ^ 8 + (15 / 8 : ℂ) * s ^ 9 + (3 / 4 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-3510 : ℂ) * s + (-8799 : ℂ) * s ^ 2 + (-46817 / 4 : ℂ) * s ^ 3 + (-156863 / 16 : ℂ) * s ^ 4 + (-91383 / 16 : ℂ) * s ^ 5 + (-4213 / 2 : ℂ) * s ^ 6 + (-3327 / 8 : ℂ) * s ^ 7 + (-467 / 16 : ℂ) * s ^ 8 + (9 / 16 : ℂ) * s ^ 9 + (-3 / 8 : ℂ) * s ^ 10) + r * ((0 : ℂ) + r * (((-1008 : ℂ) + (876 : ℂ) * s + (14895 / 2 : ℂ) * s ^ 2 + (16051 / 2 : ℂ) * s ^ 3 + (31951 / 8 : ℂ) * s ^ 4 + (4847 / 4 : ℂ) * s ^ 5 + (681 / 2 : ℂ) * s ^ 6 + (271 / 4 : ℂ) * s ^ 7 + (41 / 8 : ℂ) * s ^ 8) + r * ((0 : ℂ) + r * (((-108 : ℂ) + (2286 : ℂ) * s + (1554 : ℂ) * s ^ 2 + (1557 : ℂ) * s ^ 3 + (1769 / 2 : ℂ) * s ^ 4 + (306 : ℂ) * s ^ 5 + (97 / 2 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((1224 : ℂ) + (576 : ℂ) * s + (-73 : ℂ) * s ^ 2 + (-26 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-108 : ℂ) + (-36 : ℂ) * s))))))))))))) / (r ^ 8 * (r ^ 2 - 1) ^ 3 * s ^ 2 * (s + 3) ^ 3)

theorem skewSrcF_lauI3_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewSrcF_lauI3 s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = skewSrcFLam_lauI3 s r := by
  unfold skewSrcF_lauI3
  rw [skewPieceSF_qtr0_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qtr1_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qtr2_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qt0_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qt1_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qt2_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qT0_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qT1_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qT2_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qT3_lauI3 s r hr hf hs hs3 hs1]
  unfold skewSrcFLam_lauI3
  simp only [← add_div]
  ring

end
end RHTower.D4BMScalarStream
