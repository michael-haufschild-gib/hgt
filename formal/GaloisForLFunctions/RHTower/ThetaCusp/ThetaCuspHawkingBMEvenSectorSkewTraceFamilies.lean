import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorSkewCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorBoundaryFlux

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

theorem ssSourceTR_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((81 / 2 : ℂ) + (243 / 2 : ℂ) * s + (1161 / 8 : ℂ) * s ^ (2 : ℕ) + (357 / 4 : ℂ) * s ^ (3 : ℕ) + (30 : ℂ) * s ^ (4 : ℕ) + (21 / 4 : ℂ) * s ^ (5 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((207 : ℂ) + (663 / 2 : ℂ) * s + (439 / 2 : ℂ) * s ^ (2 : ℕ) + (151 / 2 : ℂ) * s ^ (3 : ℕ) + (27 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((81 / 2 : ℂ) + (63 / 2 : ℂ) * s + (15 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ)))))) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) := by
  unfold ssSourceTR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTR1_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((-81 / 2 : ℂ) + (-405 / 2 : ℂ) * s + (-3105 / 8 : ℂ) * s ^ (2 : ℕ) + (-759 / 2 : ℂ) * s ^ (3 : ℕ) + (-417 / 2 : ℂ) * s ^ (4 : ℕ) + (-261 / 4 : ℂ) * s ^ (5 : ℕ) + (-87 / 8 : ℂ) * s ^ (6 : ℕ) + (-3 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-1809 / 2 : ℂ) + (-2259 : ℂ) * s + (-18699 / 8 : ℂ) * s ^ (2 : ℕ) + (-5161 / 4 : ℂ) * s ^ (3 : ℕ) + (-803 / 2 : ℂ) * s ^ (4 : ℕ) + (-267 / 4 : ℂ) * s ^ (5 : ℕ) + (-37 / 8 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-2475 / 2 : ℂ) + (-1896 : ℂ) * s + (-1198 : ℂ) * s ^ (2 : ℕ) + (-395 : ℂ) * s ^ (3 : ℕ) + (-137 / 2 : ℂ) * s ^ (4 : ℕ) + (-5 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-243 / 2 : ℂ) + (-189 / 2 : ℂ) * s + (-45 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ)))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) := by
  unfold ssSourceTR1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTR2_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((81 : ℂ) * s + (405 : ℂ) * s ^ (2 : ℕ) + (3105 / 4 : ℂ) * s ^ (3 : ℕ) + (759 : ℂ) * s ^ (4 : ℕ) + (417 : ℂ) * s ^ (5 : ℕ) + (261 / 2 : ℂ) * s ^ (6 : ℕ) + (87 / 4 : ℂ) * s ^ (7 : ℕ) + (3 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((2214 : ℂ) + (8352 : ℂ) * s + (13074 : ℂ) * s ^ (2 : ℕ) + (44201 / 4 : ℂ) * s ^ (3 : ℕ) + (10937 / 2 : ℂ) * s ^ (4 : ℕ) + (1589 : ℂ) * s ^ (5 : ℕ) + (503 / 2 : ℂ) * s ^ (6 : ℕ) + (67 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((12186 : ℂ) + (28131 : ℂ) * s + (27283 : ℂ) * s ^ (2 : ℕ) + (14298 : ℂ) * s ^ (3 : ℕ) + (4276 : ℂ) * s ^ (4 : ℕ) + (691 : ℂ) * s ^ (5 : ℕ) + (47 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((8154 : ℂ) + (12186 : ℂ) * s + (7512 : ℂ) * s ^ (2 : ℕ) + (2424 : ℂ) * s ^ (3 : ℕ) + (414 : ℂ) * s ^ (4 : ℕ) + (30 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((486 : ℂ) + (378 : ℂ) * s + (90 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)) := by
  unfold ssSourceTR2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceT_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((-81 / 4 : ℂ) + (-81 / 2 : ℂ) * s + (-513 / 16 : ℂ) * s ^ (2 : ℕ) + (-201 / 16 : ℂ) * s ^ (3 : ℕ) + (-39 / 16 : ℂ) * s ^ (4 : ℕ) + (-3 / 16 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-9 / 4 : ℂ) + (-15 / 4 : ℂ) * s + (-7 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-3 / 2 : ℂ) + (-1 / 2 : ℂ) * s))))) / (r ^ (4 : ℕ)) := by
  unfold ssSourceT
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceT1_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((81 / 2 : ℂ) + (243 / 2 : ℂ) * s + (1161 / 8 : ℂ) * s ^ (2 : ℕ) + (357 / 4 : ℂ) * s ^ (3 : ℕ) + (30 : ℂ) * s ^ (4 : ℕ) + (21 / 4 : ℂ) * s ^ (5 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((90 : ℂ) + (363 / 2 : ℂ) * s + (571 / 4 : ℂ) * s ^ (2 : ℕ) + (219 / 4 : ℂ) * s ^ (3 : ℕ) + (41 / 4 : ℂ) * s ^ (4 : ℕ) + (3 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((27 / 2 : ℂ) + (27 / 2 : ℂ) * s + (9 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ)))))) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) := by
  unfold ssSourceT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceT2_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((-81 / 2 : ℂ) + (-405 / 2 : ℂ) * s + (-3105 / 8 : ℂ) * s ^ (2 : ℕ) + (-759 / 2 : ℂ) * s ^ (3 : ℕ) + (-417 / 2 : ℂ) * s ^ (4 : ℕ) + (-261 / 4 : ℂ) * s ^ (5 : ℕ) + (-87 / 8 : ℂ) * s ^ (6 : ℕ) + (-3 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-1107 / 2 : ℂ) + (-1575 : ℂ) * s + (-14457 / 8 : ℂ) * s ^ (2 : ℕ) + (-2149 / 2 : ℂ) * s ^ (3 : ℕ) + (-1401 / 4 : ℂ) * s ^ (4 : ℕ) + (-119 / 2 : ℂ) * s ^ (5 : ℕ) + (-33 / 8 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-1035 / 2 : ℂ) + (-1002 : ℂ) * s + (-3053 / 4 : ℂ) * s ^ (2 : ℕ) + (-1141 / 4 : ℂ) * s ^ (3 : ℕ) + (-209 / 4 : ℂ) * s ^ (4 : ℕ) + (-15 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-81 / 2 : ℂ) + (-81 / 2 : ℂ) * s + (-27 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ)))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) := by
  unfold ssSourceT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTF_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((-3 : ℂ) + (-4 : ℂ) * s + (-7 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((3 : ℂ) + (1 : ℂ) * s))) / (r ^ (4 : ℕ) * s) := by
  unfold ssSourceTF
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTF1_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((6 : ℂ) + (14 : ℂ) * s + (23 / 2 : ℂ) * s ^ (2 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((6 : ℂ) * s + (5 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-6 : ℂ) + (-2 : ℂ) * s))))) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) * s) := by
  unfold ssSourceTF1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTF2_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((-6 : ℂ) + (-26 : ℂ) * s + (-79 / 2 : ℂ) * s ^ (2 : ℕ) + (-27 : ℂ) * s ^ (3 : ℕ) + (-17 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-42 : ℂ) + (-116 : ℂ) * s + (-215 / 2 : ℂ) * s ^ (2 : ℕ) + (-41 : ℂ) * s ^ (3 : ℕ) + (-11 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((30 : ℂ) + (-8 : ℂ) * s + (-21 : ℂ) * s ^ (2 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((18 : ℂ) + (6 : ℂ) * s))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s) := by
  unfold ssSourceTF2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssSourceTF3_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((12 : ℂ) * s + (52 : ℂ) * s ^ (2 : ℕ) + (79 : ℂ) * s ^ (3 : ℕ) + (54 : ℂ) * s ^ (4 : ℕ) + (17 : ℂ) * s ^ (5 : ℕ) + (2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((144 : ℂ) + (576 : ℂ) * s + (842 : ℂ) * s ^ (2 : ℕ) + (567 : ℂ) * s ^ (3 : ℕ) + (178 : ℂ) * s ^ (4 : ℕ) + (21 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((216 : ℂ) + (900 : ℂ) * s + (960 : ℂ) * s ^ (2 : ℕ) + (390 : ℂ) * s ^ (3 : ℕ) + (54 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-288 : ℂ) + (-24 : ℂ) * s + (114 : ℂ) * s ^ (2 : ℕ) + (30 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (-24 : ℂ) * s))))))))) / (r ^ (7 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s) := by
  unfold ssSourceTF3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  have hs3' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  field_simp
  all_goals (try ring)

theorem ssLaurentA_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0) : laurentMasterA (-3 - s) ((s + 1) * (s + 2)) = (((-6 : ℂ) + (7 / 2 : ℂ) * s + (5 / 2 : ℂ) * s ^ (2 : ℕ)) / (s)) := by
  have hs' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  have hs3' : (-3 : ℂ) - s + 3 ≠ 0 := by intro h; apply hs; linear_combination -h
  have hs1' : (-3 : ℂ) - s + 1 ≠ 0 := by intro h; apply hs2; linear_combination -h
  have h := ssLaurentA_lam (-3 - s) hs' hs3' hs1'
  rw [show ((-3 : ℂ) - s + 1) * (-3 - s + 2) = (s + 1) * (s + 2) by ring] at h
  rw [h]
  field_simp
  all_goals (try ring)

theorem ssLaurentB_lam' (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0) : laurentMasterB (-3 - s) ((s + 1) * (s + 2)) = (((6 : ℂ) + (25 / 2 : ℂ) * s + (11 : ℂ) * s ^ (2 : ℕ) + (41 / 8 : ℂ) * s ^ (3 : ℕ) + (5 / 4 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (5 : ℕ)) / (s)) := by
  have hs' : (-3 : ℂ) - s ≠ 0 := by intro h; apply hs3; linear_combination -h
  have hs3' : (-3 : ℂ) - s + 3 ≠ 0 := by intro h; apply hs; linear_combination -h
  have h := ssLaurentB_lam (-3 - s) hs' hs3'
  rw [show ((-3 : ℂ) - s + 1) * (-3 - s + 2) = (s + 1) * (s + 2) by ring] at h
  rw [h]
  field_simp
  all_goals (try ring)

theorem skewFF_lauR_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauR_lauR s r ((s + 1) * (s + 2)) = (((-576 : ℂ) * s + (-1179 / 2 : ℂ) * s ^ (2 : ℕ) + (-146 : ℂ) * s ^ (3 : ℕ) + (-15 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-1056 : ℂ) + (-632 : ℂ) * s + (171 / 2 : ℂ) * s ^ (2 : ℕ) + (34 : ℂ) * s ^ (3 : ℕ) + (15 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((444 : ℂ) + (296 : ℂ) * s) + r * ((0 : ℂ) + r * ((-60 : ℂ) + (-40 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFF_lauR_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauR_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauR_lauI1 s r ((s + 1) * (s + 2)) = (((-220 : ℂ) * s + (15 / 2 : ℂ) * s ^ (2 : ℕ) + (-9 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-216 : ℂ) + (-82 : ℂ) * s + (17 / 2 : ℂ) * s ^ (2 : ℕ) + (9 / 2 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-20 : ℂ) + (6 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3)) := by
  unfold skewFF_lauR_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauR_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauR_lauI3 s r ((s + 1) * (s + 2)) = (((-464 : ℂ) * s + (-235 / 2 : ℂ) * s ^ (2 : ℕ) + (70 : ℂ) * s ^ (3 : ℕ) + (-15 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-336 : ℂ) + (-740 : ℂ) * s + (211 / 2 : ℂ) * s ^ (2 : ℕ) + (74 : ℂ) * s ^ (3 : ℕ) + (15 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-372 : ℂ) + (-68 : ℂ) * s + (20 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((36 : ℂ)))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFF_lauR_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI1_lauR s r ((s + 1) * (s + 2)) = (((768 : ℂ) + (557 / 2 : ℂ) * s + (-6 : ℂ) * s ^ (2 : ℕ) + (-15 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((66 : ℂ) + (239 / 2 : ℂ) * s + (22 : ℂ) * s ^ (2 : ℕ) + (15 / 2 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-38 : ℂ) + (-6 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFF_lauI1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI1_lauI1 s r ((s + 1) * (s + 2)) = (((132 : ℂ) + (167 / 2 : ℂ) * s + (-9 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((84 : ℂ) + (121 / 2 : ℂ) * s + (9 / 2 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ)))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3)) := by
  unfold skewFF_lauI1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI1_lauI3 s r ((s + 1) * (s + 2)) = (((144 : ℂ) + (477 / 2 : ℂ) * s + (82 : ℂ) * s ^ (2 : ℕ) + (-15 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((374 : ℂ) + (1175 / 2 : ℂ) * s + (190 : ℂ) * s ^ (2 : ℕ) + (15 / 2 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-18 : ℂ) + (78 : ℂ) * s) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFF_lauI1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI3_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI3_lauR s r ((s + 1) * (s + 2)) = (((1920 : ℂ) + (2536 : ℂ) * s + (1765 / 2 : ℂ) * s ^ (2 : ℕ) + (70 : ℂ) * s ^ (3 : ℕ) + (-15 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-1200 : ℂ) + (220 : ℂ) * s + (851 / 2 : ℂ) * s ^ (2 : ℕ) + (74 : ℂ) * s ^ (3 : ℕ) + (15 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-188 : ℂ) * s + (-20 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-36 : ℂ)))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFF_lauI3_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI3_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI3_lauI1 s r ((s + 1) * (s + 2)) = (((288 : ℂ) + (348 : ℂ) * s + (191 / 2 : ℂ) * s ^ (2 : ℕ) + (-9 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((200 : ℂ) + (458 : ℂ) * s + (353 / 2 : ℂ) * s ^ (2 : ℕ) + (9 / 2 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-252 : ℂ) + (-78 : ℂ) * s) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3)) := by
  unfold skewFF_lauI3_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFF_lauI3_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFF_lauI3_lauI3 s r ((s + 1) * (s + 2)) = (((192 : ℂ) + (344 : ℂ) * s + (405 / 2 : ℂ) * s ^ (2 : ℕ) + (30 : ℂ) * s ^ (3 : ℕ) + (-15 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((1344 : ℂ) + (2480 : ℂ) * s + (3195 / 2 : ℂ) * s ^ (2 : ℕ) + (370 : ℂ) * s ^ (3 : ℕ) + (15 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-540 : ℂ) + (-360 : ℂ) * s) + r * ((0 : ℂ) + r * ((-324 : ℂ) + (-216 : ℂ) * s))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFF_lauI3_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qt0 s r ((s + 1) * (s + 2)) = (((-216 : ℂ) * s + (129 : ℂ) * s ^ (2 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ) + (-51 : ℂ) * s ^ (4 : ℕ) + (-10 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-120 : ℂ) + (222 : ℂ) * s + (175 : ℂ) * s ^ (2 : ℕ) + (-46 : ℂ) * s ^ (3 : ℕ) + (7 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((240 : ℂ) + (10 : ℂ) * s + (-140 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-120 : ℂ) + (-80 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauR_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-107 : ℂ) * s + (73 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ) + (-16 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-72 : ℂ) + (82 : ℂ) * s + (108 : ℂ) * s ^ (2 : ℕ) + (-46 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((144 : ℂ) + (53 : ℂ) * s + (-93 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (-60 : ℂ) * s)))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauR_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qT0 s r ((s + 1) * (s + 2)) = (((360 : ℂ) * s + (-177 : ℂ) * s ^ (2 : ℕ) + (-36 : ℂ) * s ^ (3 : ℕ) + (51 : ℂ) * s ^ (4 : ℕ) + (10 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((240 : ℂ) + (-428 : ℂ) * s + (-284 : ℂ) * s ^ (2 : ℕ) + (70 : ℂ) * s ^ (3 : ℕ) + (-26 : ℂ) * s ^ (4 : ℕ) + (-12 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-552 : ℂ) + (76 : ℂ) * s + (375 : ℂ) * s ^ (2 : ℕ) + (-12 : ℂ) * s ^ (3 : ℕ) + (7 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((432 : ℂ) + (168 : ℂ) * s + (-122 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-120 : ℂ) + (-80 : ℂ) * s))))))))) / ((r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauR_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-282 : ℂ) * s + (90 : ℂ) * s ^ (2 : ℕ) + (84 : ℂ) * s ^ (3 : ℕ) + (-28 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-192 : ℂ) + (154 : ℂ) * s + (364 : ℂ) * s ^ (2 : ℕ) + (-130 : ℂ) * s ^ (3 : ℕ) + (-4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((360 : ℂ) + (208 : ℂ) * s + (-262 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-168 : ℂ) + (-160 : ℂ) * s)))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauR_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qt0 s r ((s + 1) * (s + 2)) = (((12 : ℂ) + (-47 : ℂ) * s + (-128 : ℂ) * s ^ (2 : ℕ) + (-67 : ℂ) * s ^ (3 : ℕ) + (-10 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-114 : ℂ) + (187 : ℂ) * s + (78 : ℂ) * s ^ (2 : ℕ) + (23 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((14 : ℂ) + (24 : ℂ) * s + (2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qtr0 s r ((s + 1) * (s + 2)) = (((21 : ℂ) + (-7 : ℂ) * s + (-42 : ℂ) * s ^ (2 : ℕ) + (-16 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-82 : ℂ) + (92 : ℂ) * s + (2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((5 : ℂ) + (3 : ℂ) * s) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))) / (r * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qT0 s r ((s + 1) * (s + 2)) = (((-24 : ℂ) + (67 : ℂ) * s + (136 : ℂ) * s ^ (2 : ℕ) + (67 : ℂ) * s ^ (3 : ℕ) + (10 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((144 : ℂ) + (-408 : ℂ) * s + (-170 : ℂ) * s ^ (2 : ℕ) + (-58 : ℂ) * s ^ (3 : ℕ) + (-12 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-20 : ℂ) + (115 : ℂ) * s + (48 : ℂ) * s ^ (2 : ℕ) + (23 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-28 : ℂ) + (18 : ℂ) * s + (2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauI1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qT1 s r ((s + 1) * (s + 2)) = (((102 : ℂ) + (70 : ℂ) * s + (-8 : ℂ) * s ^ (2 : ℕ) + (-28 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-270 : ℂ) + (116 : ℂ) * s + (-42 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((16 : ℂ) + (6 : ℂ) * s + (2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((72 : ℂ)))))))) / (r * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauI1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qt0 s r ((s + 1) * (s + 2)) = (((-96 : ℂ) + (-368 : ℂ) * s + (-463 : ℂ) * s ^ (2 : ℕ) + (-276 : ℂ) * s ^ (3 : ℕ) + (-83 : ℂ) * s ^ (4 : ℕ) + (-10 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((120 : ℂ) + (638 : ℂ) * s + (679 : ℂ) * s ^ (2 : ℕ) + (234 : ℂ) * s ^ (3 : ℕ) + (39 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((48 : ℂ) + (-334 : ℂ) * s + (-52 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ)))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI3_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qtr0 s r ((s + 1) * (s + 2)) = (((-123 : ℂ) * s + (-183 : ℂ) * s ^ (2 : ℕ) + (-90 : ℂ) * s ^ (3 : ℕ) + (-16 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-72 : ℂ) + (202 : ℂ) * s + (268 : ℂ) * s ^ (2 : ℕ) + (50 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((144 : ℂ) + (-123 : ℂ) * s + (3 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (12 : ℂ) * s))))))) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI3_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qT0 s r ((s + 1) * (s + 2)) = (((192 : ℂ) + (664 : ℂ) * s + (695 : ℂ) * s ^ (2 : ℕ) + (324 : ℂ) * s ^ (3 : ℕ) + (83 : ℂ) * s ^ (4 : ℕ) + (10 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-528 : ℂ) + (-1764 : ℂ) * s + (-1492 : ℂ) * s ^ (2 : ℕ) + (-458 : ℂ) * s ^ (3 : ℕ) + (-90 : ℂ) * s ^ (4 : ℕ) + (-12 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((360 : ℂ) + (1500 : ℂ) * s + (623 : ℂ) * s ^ (2 : ℕ) + (156 : ℂ) * s ^ (3 : ℕ) + (39 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((48 : ℂ) + (-304 : ℂ) * s + (-34 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ)))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauI3_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qT1 s r ((s + 1) * (s + 2)) = (((192 : ℂ) + (70 : ℂ) * s + (-142 : ℂ) * s ^ (2 : ℕ) + (-100 : ℂ) * s ^ (3 : ℕ) + (-28 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-576 : ℂ) + (-118 : ℂ) * s + (252 : ℂ) * s ^ (2 : ℕ) + (46 : ℂ) * s ^ (3 : ℕ) + (-4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((600 : ℂ) + (-80 : ℂ) * s + (82 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-216 : ℂ) + (48 : ℂ) * s))))))) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauI3_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((34 : ℂ) * s + (34 : ℂ) * s ^ (2 : ℕ) + (-40 : ℂ) * s ^ (3 : ℕ) + (-4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((24 : ℂ) + (38 : ℂ) * s + (-76 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-24 : ℂ) + (-40 : ℂ) * s)))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauR_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((9 : ℂ) * s + (19 : ℂ) * s ^ (2 : ℕ) + (-16 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((12 : ℂ) + (31 : ℂ) * s + (-43 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-12 : ℂ) + (-24 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauR_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((2 : ℂ) * s + (54 : ℂ) * s ^ (2 : ℕ) + (-32 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((24 : ℂ) + (78 : ℂ) * s + (-94 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-24 : ℂ) + (-52 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauR_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qt1 s r ((s + 1) * (s + 2)) = (((-30 : ℂ) + (-42 : ℂ) * s + (-44 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((38 : ℂ) + (2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((24 : ℂ)))))) / (r * (r ^ (2 : ℕ) - 1) * s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI1_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qtr1 s r ((s + 1) * (s + 2)) = (((-15 : ℂ) + (-13 : ℂ) * s + (-16 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((15 : ℂ) + (-11 : ℂ) * s) + r * ((0 : ℂ) + r * ((16 : ℂ)))))) / ((r ^ (2 : ℕ) - 1) * s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI1_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qT2 s r ((s + 1) * (s + 2)) = (((-30 : ℂ) + (-10 : ℂ) * s + (-32 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((22 : ℂ) + (-30 : ℂ) * s) + r * ((0 : ℂ) + r * ((36 : ℂ)))))) / ((r ^ (2 : ℕ) - 1) * s * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauI1_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qt1 s r ((s + 1) * (s + 2)) = (((-96 : ℂ) + (-158 : ℂ) * s + (-118 : ℂ) * s ^ (2 : ℕ) + (-48 : ℂ) * s ^ (3 : ℕ) + (-4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((168 : ℂ) + (166 : ℂ) * s + (76 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (24 : ℂ) * s))))) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI3_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qtr1 s r ((s + 1) * (s + 2)) = (((-48 : ℂ) + (-71 : ℂ) * s + (-45 : ℂ) * s ^ (2 : ℕ) + (-16 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((84 : ℂ) + (63 : ℂ) * s + (21 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-36 : ℂ) + (24 : ℂ) * s))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI3_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qT2 s r ((s + 1) * (s + 2)) = (((-96 : ℂ) + (-126 : ℂ) * s + (-74 : ℂ) * s ^ (2 : ℕ) + (-32 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((168 : ℂ) + (94 : ℂ) * s + (34 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ) + (60 : ℂ) * s))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauI3_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-4 : ℂ)))))) / (s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauR_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((4 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((-2 : ℂ))))))) / (s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauR_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauR_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauR_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-4 : ℂ))))))) / (s * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauR_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qt2 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((4 : ℂ)))) / (s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI1_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((2 : ℂ))))) / (s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI1_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI1_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI1_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((4 : ℂ))))) / (s * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauI1_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qt2 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ)))) / (r ^ (2 : ℕ) * s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI3_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qtr2 s r ((s + 1) * (s + 2)) = (((-4 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((6 : ℂ)))) / (r * s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewFQ_lauI3_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewFQ_lauI3_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewFQ_lauI3_qT3 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ)))) / (r * s * (s + 3) ^ (2 : ℕ)) := by
  unfold skewFQ_lauI3_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt0_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt0_lauR s r ((s + 1) * (s + 2)) = (((-576 : ℂ) * s + (39 : ℂ) * s ^ (2 : ℕ) + (284 : ℂ) * s ^ (3 : ℕ) + (99 : ℂ) * s ^ (4 : ℕ) + (10 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((2112 : ℂ) + (2016 : ℂ) * s + (427 : ℂ) * s ^ (2 : ℕ) + (-50 : ℂ) * s ^ (3 : ℕ) + (-23 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-888 : ℂ) + (-688 : ℂ) * s + (-86 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((120 : ℂ) + (80 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qt0_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt1_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((960 : ℂ) + (818 : ℂ) * s + (178 : ℂ) * s ^ (2 : ℕ) + (-8 : ℂ) * s ^ (3 : ℕ) + (-4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-720 : ℂ) + (-440 : ℂ) * s + (-58 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((96 : ℂ) + (40 : ℂ) * s)))))) / ((r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qt1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr0_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr0_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-480 : ℂ) + (-1345 : ℂ) * s + (-845 : ℂ) * s ^ (2 : ℕ) + (-198 : ℂ) * s ^ (3 : ℕ) + (-16 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((1896 : ℂ) + (1808 : ℂ) * s + (522 : ℂ) * s ^ (2 : ℕ) + (46 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-852 : ℂ) + (-611 : ℂ) * s + (-93 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((108 : ℂ) + (60 : ℂ) * s)))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qtr0_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr1_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((576 : ℂ) + (537 : ℂ) * s + (163 : ℂ) * s ^ (2 : ℕ) + (16 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-468 : ℂ) + (-289 : ℂ) * s + (-43 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((60 : ℂ) + (24 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qtr1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT0_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT0_lauR s r ((s + 1) * (s + 2)) = (((-1008 : ℂ) * s + (-201 : ℂ) * s ^ (2 : ℕ) + (252 : ℂ) * s ^ (3 : ℕ) + (99 : ℂ) * s ^ (4 : ℕ) + (10 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((2112 : ℂ) + (1114 : ℂ) * s + (-922 : ℂ) * s ^ (2 : ℕ) + (-698 : ℂ) * s ^ (3 : ℕ) + (-154 : ℂ) * s ^ (4 : ℕ) + (-12 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-3000 : ℂ) + (-2444 : ℂ) * s + (-321 : ℂ) * s ^ (2 : ℕ) + (84 : ℂ) * s ^ (3 : ℕ) + (23 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((1008 : ℂ) + (738 : ℂ) * s + (68 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-120 : ℂ) + (-80 : ℂ) * s))))))))) / ((r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qT0_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT1_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT1_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((2880 : ℂ) + (4470 : ℂ) * s + (2178 : ℂ) * s ^ (2 : ℕ) + (420 : ℂ) * s ^ (3 : ℕ) + (28 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-5808 : ℂ) + (-5108 : ℂ) * s + (-1318 : ℂ) * s ^ (2 : ℕ) + (-82 : ℂ) * s ^ (3 : ℕ) + (4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((2568 : ℂ) + (1726 : ℂ) * s + (244 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-312 : ℂ) + (-160 : ℂ) * s)))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qT1_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT2_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT2_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-1344 : ℂ) + (-1186 : ℂ) * s + (-342 : ℂ) * s ^ (2 : ℕ) + (-32 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((1056 : ℂ) + (642 : ℂ) * s + (94 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-132 : ℂ) + (-52 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qT2_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt0_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt0_lauI1 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) * s + (65 : ℂ) * s ^ (2 : ℕ) + (53 : ℂ) * s ^ (3 : ℕ) + (10 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((432 : ℂ) + (124 : ℂ) * s + (21 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((40 : ℂ) + (12 : ℂ) * s + (-2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQF_qt0_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt1_lauI1 s r ((s + 1) * (s + 2)) = (((192 : ℂ) + (114 : ℂ) * s + (8 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-56 : ℂ) + (-12 : ℂ) * s + (-2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))) / (r * (r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQF_qt1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr0_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr0_lauI1 s r ((s + 1) * (s + 2)) = (((-96 : ℂ) + (-187 : ℂ) * s + (-102 : ℂ) * s ^ (2 : ℕ) + (-16 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((340 : ℂ) + (80 : ℂ) * s + (-2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((4 : ℂ) + (3 : ℂ) * s) + r * ((0 : ℂ) + r * ((-24 : ℂ)))))))) / (r * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQF_qtr0_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr1_lauI1 s r ((s + 1) * (s + 2)) = (((120 : ℂ) + (83 : ℂ) * s + (16 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((-48 : ℂ) + (-11 : ℂ) * s) + r * ((0 : ℂ) + r * ((-16 : ℂ)))))) / ((r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQF_qtr1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT0_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT0_lauI1 s r ((s + 1) * (s + 2)) = (((20 : ℂ) * s + (73 : ℂ) * s ^ (2 : ℕ) + (53 : ℂ) * s ^ (3 : ℕ) + (10 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((432 : ℂ) + (-342 : ℂ) * s + (-296 : ℂ) * s ^ (2 : ℕ) + (-86 : ℂ) * s ^ (3 : ℕ) + (-12 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-392 : ℂ) + (-232 : ℂ) * s + (-51 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-64 : ℂ) + (-6 : ℂ) * s + (2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((24 : ℂ)))))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3)) := by
  unfold skewQF_qT0_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT1_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT1_lauI1 s r ((s + 1) * (s + 2)) = (((576 : ℂ) + (638 : ℂ) * s + (244 : ℂ) * s ^ (2 : ℕ) + (28 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-888 : ℂ) + (-260 : ℂ) * s + (-6 : ℂ) * s ^ (2 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((16 : ℂ) + (6 : ℂ) * s + (2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((72 : ℂ)))))))) / (r * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3)) := by
  unfold skewQF_qT1_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT2_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT2_lauI1 s r ((s + 1) * (s + 2)) = (((-288 : ℂ) + (-182 : ℂ) * s + (-32 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((112 : ℂ) + (30 : ℂ) * s) + r * ((0 : ℂ) + r * ((36 : ℂ)))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3)) := by
  unfold skewQF_qT2_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt0_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt0_lauI3 s r ((s + 1) * (s + 2)) = (((128 : ℂ) * s + (239 : ℂ) * s ^ (2 : ℕ) + (180 : ℂ) * s ^ (3 : ℕ) + (67 : ℂ) * s ^ (4 : ℕ) + (10 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((672 : ℂ) + (520 : ℂ) * s + (139 : ℂ) * s ^ (2 : ℕ) + (54 : ℂ) * s ^ (3 : ℕ) + (9 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((744 : ℂ) + (184 : ℂ) * s + (2 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ)))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qt0_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt1_lauI3 s r ((s + 1) * (s + 2)) = (((288 : ℂ) + (314 : ℂ) * s + (98 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((192 : ℂ) + (128 : ℂ) * s + (22 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-144 : ℂ) + (-24 : ℂ) * s))))) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qt1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr0_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr0_lauI3 s r ((s + 1) * (s + 2)) = (((-144 : ℂ) + (-273 : ℂ) * s + (-237 : ℂ) * s ^ (2 : ℕ) + (-102 : ℂ) * s ^ (3 : ℕ) + (-16 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((384 : ℂ) + (56 : ℂ) * s + (-182 : ℂ) * s ^ (2 : ℕ) + (-50 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((540 : ℂ) + (141 : ℂ) * s + (3 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-108 : ℂ) + (-12 : ℂ) * s))))))) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qtr0_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr1_lauI3 s r ((s + 1) * (s + 2)) = (((192 : ℂ) + (233 : ℂ) * s + (99 : ℂ) * s ^ (2 : ℕ) + (16 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((84 : ℂ) + (63 : ℂ) * s + (21 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-108 : ℂ) + (-24 : ℂ) * s))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qtr1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT0_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT0_lauI3 s r ((s + 1) * (s + 2)) = (((328 : ℂ) * s + (439 : ℂ) * s ^ (2 : ℕ) + (228 : ℂ) * s ^ (3 : ℕ) + (67 : ℂ) * s ^ (4 : ℕ) + (10 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((672 : ℂ) + (-318 : ℂ) * s + (-1010 : ℂ) * s ^ (2 : ℕ) + (-458 : ℂ) * s ^ (3 : ℕ) + (-90 : ℂ) * s ^ (4 : ℕ) + (-12 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((72 : ℂ) + (-1428 : ℂ) * s + (-785 : ℂ) * s ^ (2 : ℕ) + (-132 : ℂ) * s ^ (3 : ℕ) + (-9 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-816 : ℂ) + (-262 : ℂ) * s + (-20 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((72 : ℂ)))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qT0_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT1_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT1_lauI3 s r ((s + 1) * (s + 2)) = (((864 : ℂ) + (1246 : ℂ) * s + (754 : ℂ) * s ^ (2 : ℕ) + (236 : ℂ) * s ^ (3 : ℕ) + (28 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-480 : ℂ) + (44 : ℂ) * s + (378 : ℂ) * s ^ (2 : ℕ) + (94 : ℂ) * s ^ (3 : ℕ) + (4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-1416 : ℂ) + (-410 : ℂ) * s + (-28 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((360 : ℂ) + (48 : ℂ) * s))))))) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qT1_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT2_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT2_lauI3 s r ((s + 1) * (s + 2)) = (((-480 : ℂ) + (-546 : ℂ) * s + (-214 : ℂ) * s ^ (2 : ℕ) + (-32 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-192 : ℂ) + (-110 : ℂ) * s + (-34 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((252 : ℂ) + (60 : ℂ) * s))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQF_qT2_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt2_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt2_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-32 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((4 : ℂ)))))) / (s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQF_qt2_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr2_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr2_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-16 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((2 : ℂ))))))) / (s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQF_qtr2_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT3_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT3_lauR s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((32 : ℂ) + (8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-4 : ℂ))))))) / (s ^ (2 : ℕ) * (s + 3)) := by
  unfold skewQF_qT3_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt2_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt2_lauI1 s r ((s + 1) * (s + 2)) = (((-24 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-4 : ℂ)))) / (s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQF_qt2_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr2_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr2_lauI1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-12 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((-2 : ℂ))))) / (s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQF_qtr2_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT3_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT3_lauI1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((24 : ℂ) + (8 : ℂ) * s) + r * ((0 : ℂ) + r * ((4 : ℂ))))) / (s ^ (2 : ℕ) * (s + 3)) := by
  unfold skewQF_qT3_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qt2_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qt2_lauI3 s r ((s + 1) * (s + 2)) = (((-16 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-12 : ℂ)))) / (r ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQF_qt2_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qtr2_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qtr2_lauI3 s r ((s + 1) * (s + 2)) = (((-8 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((-6 : ℂ)))) / (r * s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQF_qtr2_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQF_qT3_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQF_qT3_lauI3 s r ((s + 1) * (s + 2)) = (((16 : ℂ) + (8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ)))) / (r * s ^ (2 : ℕ) * (s + 3)) := by
  unfold skewQF_qT3_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-30 : ℂ) + (-20 : ℂ) * s) + r * ((0 : ℂ) + r * ((126 : ℂ) + (84 : ℂ) * s))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qtr0_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-6 : ℂ) + (-16 : ℂ) * s) + r * ((0 : ℂ) + r * ((18 : ℂ) + (28 : ℂ) * s)))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qtr0_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-2 : ℂ)) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))) / (s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qtr0_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-48 : ℂ) + (2 : ℂ) * s + (30 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((216 : ℂ) + (120 : ℂ) * s)))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qtr0_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-24 : ℂ) * s + (6 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((36 : ℂ) + (48 : ℂ) * s))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qtr0_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))) / (s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qtr0_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-96 : ℂ) + (-50 : ℂ) * s + (30 : ℂ) * s ^ (2 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((552 : ℂ) + (304 : ℂ) * s + (-36 : ℂ) * s ^ (2 : ℕ) + (-20 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-624 : ℂ) + (-358 : ℂ) * s + (6 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((216 : ℂ) + (120 : ℂ) * s)))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qtr0_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((84 : ℂ) + (88 : ℂ) * s + (-6 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-396 : ℂ) + (-312 : ℂ) * s + (6 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((288 : ℂ) + (216 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qtr0_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-40 : ℂ) * s) + r * ((0 : ℂ) + r * ((36 : ℂ) + (60 : ℂ) * s)))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qtr0_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr0_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr0_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ)))))))) / (s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qtr0_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-42 : ℂ) + (-16 : ℂ) * s) + r * ((0 : ℂ) + r * ((66 : ℂ) + (28 : ℂ) * s)))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qtr1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-6 : ℂ) + (-4 : ℂ) * s) + r * ((0 : ℂ) + r * ((6 : ℂ) + (4 : ℂ) * s))))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
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

theorem skewQQ_qtr1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-72 : ℂ) + (-24 : ℂ) * s + (6 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((120 : ℂ) + (48 : ℂ) * s))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qtr1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ) + (8 : ℂ) * s)))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
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

theorem skewQQ_qtr1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((144 : ℂ) + (66 : ℂ) * s + (-2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-288 : ℂ) + (-122 : ℂ) * s + (2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((120 : ℂ) + (48 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qtr1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-108 : ℂ) + (-48 : ℂ) * s) + r * ((0 : ℂ) + r * ((144 : ℂ) + (64 : ℂ) * s)))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qtr1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr1_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ) + (8 : ℂ) * s))))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
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

theorem skewQQ_qtr2_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-2 : ℂ)) + r * ((0 : ℂ) + r * ((2 : ℂ)))))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
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

theorem skewQQ_qtr2_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
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

theorem skewQQ_qtr2_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))) / (s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQQ_qtr2_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qtr2_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qtr2_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ)))))))) / (s ^ (3 : ℕ) * (s + 3)) := by
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

theorem skewQQ_qt0_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((38 : ℂ) * s + (42 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((144 : ℂ) + (120 : ℂ) * s)))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qt0_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-6 : ℂ) * s + (12 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((24 : ℂ) + (48 : ℂ) * s))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qt0_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))) / (s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qt0_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qt0 s r ((s + 1) * (s + 2)) = (((108 : ℂ) * s + (108 : ℂ) * s ^ (2 : ℕ) + (24 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((240 : ℂ) + (160 : ℂ) * s))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qt0_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((4 : ℂ) * s + (36 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((48 : ℂ) + (80 : ℂ) * s)))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qt0_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ)) + r * ((0 : ℂ) + r * ((8 : ℂ)))))) / (s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qt0_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qT0 s r ((s + 1) * (s + 2)) = (((144 : ℂ) * s + (234 : ℂ) * s ^ (2 : ℕ) + (116 : ℂ) * s ^ (3 : ℕ) + (30 : ℂ) * s ^ (4 : ℕ) + (4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((480 : ℂ) + (168 : ℂ) * s + (-258 : ℂ) * s ^ (2 : ℕ) + (-132 : ℂ) * s ^ (3 : ℕ) + (-30 : ℂ) * s ^ (4 : ℕ) + (-4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-624 : ℂ) + (-368 : ℂ) * s + (72 : ℂ) * s ^ (2 : ℕ) + (24 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((240 : ℂ) + (160 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qt0_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-84 : ℂ) * s + (-144 : ℂ) * s ^ (2 : ℕ) + (-28 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-384 : ℂ) + (-288 : ℂ) * s + (120 : ℂ) * s ^ (2 : ℕ) + (24 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((336 : ℂ) + (320 : ℂ) * s)))))) / ((r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qt0_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-28 : ℂ) * s + (24 : ℂ) * s ^ (2 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((48 : ℂ) + (104 : ℂ) * s))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qt0_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt0_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt0_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ)) + r * ((0 : ℂ) + r * ((8 : ℂ))))))) / (s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qt0_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-60 : ℂ) + (-6 : ℂ) * s + (12 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((108 : ℂ) + (48 : ℂ) * s))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qt1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) + (-8 : ℂ) * s) + r * ((0 : ℂ) + r * ((12 : ℂ) + (8 : ℂ) * s)))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
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

theorem skewQQ_qt1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-96 : ℂ) + (4 : ℂ) * s + (36 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((192 : ℂ) + (80 : ℂ) * s)))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qt1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-24 : ℂ) + (-16 : ℂ) * s) + r * ((0 : ℂ) + r * ((24 : ℂ) + (16 : ℂ) * s))))) / (s ^ (3 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
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

theorem skewQQ_qt1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((192 : ℂ) + (28 : ℂ) * s + (-48 : ℂ) * s ^ (2 : ℕ) + (-12 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-432 : ℂ) + (-160 : ℂ) * s + (24 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((192 : ℂ) + (80 : ℂ) * s)))))) / ((r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qt1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-168 : ℂ) + (-44 : ℂ) * s + (24 : ℂ) * s ^ (2 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((240 : ℂ) + (112 : ℂ) * s))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qt1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt1_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-24 : ℂ) + (-16 : ℂ) * s) + r * ((0 : ℂ) + r * ((24 : ℂ) + (16 : ℂ) * s)))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
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

theorem skewQQ_qt2_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-4 : ℂ)) + r * ((0 : ℂ) + r * ((4 : ℂ))))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
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

theorem skewQQ_qt2_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ)) + r * ((0 : ℂ) + r * ((8 : ℂ)))))) / (s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
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

theorem skewQQ_qt2_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-16 : ℂ)) + r * ((0 : ℂ) + r * ((8 : ℂ)))))) / (s ^ (3 : ℕ) * (s + 3)) := by
  unfold skewQQ_qt2_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qt2_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qt2_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((-8 : ℂ)) + r * ((0 : ℂ) + r * ((8 : ℂ))))))) / (s ^ (3 : ℕ) * (s + 3)) := by
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

theorem skewQQ_qT0_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-94 : ℂ) * s + (-78 : ℂ) * s ^ (2 : ℕ) + (-12 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-144 : ℂ) + (20 : ℂ) * s + (144 : ℂ) * s ^ (2 : ℕ) + (20 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((288 : ℂ) + (178 : ℂ) * s + (-66 : ℂ) * s ^ (2 : ℕ) + (-8 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-144 : ℂ) + (-120 : ℂ) * s)))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT0_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-12 : ℂ) * s + (18 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((24 : ℂ) + (68 : ℂ) * s + (-18 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-24 : ℂ) + (-48 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT0_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * ((-4 : ℂ))))))) / (s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT0_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qt0 s r ((s + 1) * (s + 2)) = (((-252 : ℂ) * s + (-270 : ℂ) * s ^ (2 : ℕ) + (-116 : ℂ) * s ^ (3 : ℕ) + (-30 : ℂ) * s ^ (4 : ℕ) + (-4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-240 : ℂ) + (228 : ℂ) * s + (390 : ℂ) * s ^ (2 : ℕ) + (132 : ℂ) * s ^ (3 : ℕ) + (30 : ℂ) * s ^ (4 : ℕ) + (4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((480 : ℂ) + (152 : ℂ) * s + (-144 : ℂ) * s ^ (2 : ℕ) + (-24 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-240 : ℂ) + (-160 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT0_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((8 : ℂ) * s + (60 : ℂ) * s ^ (2 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((48 : ℂ) + (88 : ℂ) * s + (-48 : ℂ) * s ^ (2 : ℕ) + (-8 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-48 : ℂ) + (-80 : ℂ) * s)))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT0_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((16 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))) / (s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT0_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qT0 s r ((s + 1) * (s + 2)) = (((-360 : ℂ) * s + (-414 : ℂ) * s ^ (2 : ℕ) + (-152 : ℂ) * s ^ (3 : ℕ) + (-30 : ℂ) * s ^ (4 : ℕ) + (-4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-480 : ℂ) + (4 : ℂ) * s + (378 : ℂ) * s ^ (2 : ℕ) + (144 : ℂ) * s ^ (3 : ℕ) + (30 : ℂ) * s ^ (4 : ℕ) + (4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((624 : ℂ) + (308 : ℂ) * s + (-108 : ℂ) * s ^ (2 : ℕ) + (-24 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-240 : ℂ) + (-160 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qT0_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-204 : ℂ) * s + (-252 : ℂ) * s ^ (2 : ℕ) + (-40 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-384 : ℂ) + (-64 : ℂ) * s + (432 : ℂ) * s ^ (2 : ℕ) + (64 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((720 : ℂ) + (572 : ℂ) * s + (-180 : ℂ) * s ^ (2 : ℕ) + (-24 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-336 : ℂ) + (-320 : ℂ) * s)))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qT0_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-56 : ℂ) * s + (36 : ℂ) * s ^ (2 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((48 : ℂ) + (168 : ℂ) * s + (-36 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-48 : ℂ) + (-104 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qT0_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT0_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT0_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((16 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ))))))) / (s * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qT0_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-180 : ℂ) + (-70 : ℂ) * s + (12 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((540 : ℂ) + (294 : ℂ) * s + (-12 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-360 : ℂ) + (-216 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT1_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((36 : ℂ) + (48 : ℂ) * s) + r * ((0 : ℂ) + r * ((-48 : ℂ) + (-64 : ℂ) * s)))))) / (s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT1_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((4 : ℂ)) + r * ((0 : ℂ) + r * ((-4 : ℂ)))))))) / (s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT1_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-288 : ℂ) + (-24 : ℂ) * s + (108 : ℂ) * s ^ (2 : ℕ) + (28 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((912 : ℂ) + (360 : ℂ) * s + (-96 : ℂ) * s ^ (2 : ℕ) + (-24 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-624 : ℂ) + (-320 : ℂ) * s)))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT1_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((72 : ℂ) + (80 : ℂ) * s + (-12 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-96 : ℂ) + (-112 : ℂ) * s))))) / (s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT1_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qt2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ))))))) / (s * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT1_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((576 : ℂ) + (228 : ℂ) * s + (-108 : ℂ) * s ^ (2 : ℕ) + (-40 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-1968 : ℂ) + (-928 : ℂ) * s + (144 : ℂ) * s ^ (2 : ℕ) + (64 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((1968 : ℂ) + (1004 : ℂ) * s + (-36 : ℂ) * s ^ (2 : ℕ) + (-24 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-624 : ℂ) + (-320 : ℂ) * s)))))))) / ((r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qT1_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-504 : ℂ) + (-300 : ℂ) * s + (36 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((1344 : ℂ) + (860 : ℂ) * s + (-36 : ℂ) * s ^ (2 : ℕ) + (-8 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-816 : ℂ) + (-544 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qT1_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((72 : ℂ) + (112 : ℂ) * s) + r * ((0 : ℂ) + r * ((-96 : ℂ) + (-136 : ℂ) * s)))))) / (s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qT1_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT1_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT1_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))))) / (s * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qT1_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((108 : ℂ) + (40 : ℂ) * s) + r * ((0 : ℂ) + r * ((-144 : ℂ) + (-60 : ℂ) * s)))))) / (s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT2_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qtr1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((12 : ℂ) + (8 : ℂ) * s) + r * ((0 : ℂ) + r * ((-12 : ℂ) + (-8 : ℂ) * s))))))) / (s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
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

theorem skewQQ_qT2_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((192 : ℂ) + (64 : ℂ) * s + (-12 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-264 : ℂ) + (-104 : ℂ) * s))))) / (s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  unfold skewQQ_qT2_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qt1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((24 : ℂ) + (16 : ℂ) * s) + r * ((0 : ℂ) + r * ((-24 : ℂ) + (-16 : ℂ) * s)))))) / (s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
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

theorem skewQQ_qT2_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * (((-384 : ℂ) + (-164 : ℂ) * s + (4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((672 : ℂ) + (276 : ℂ) * s + (-4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-264 : ℂ) + (-104 : ℂ) * s))))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qT2_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((264 : ℂ) + (112 : ℂ) * s) + r * ((0 : ℂ) + r * ((-312 : ℂ) + (-136 : ℂ) * s)))))) / (s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  unfold skewQQ_qT2_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT2_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT2_qT2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((24 : ℂ) + (16 : ℂ) * s) + r * ((0 : ℂ) + r * ((-24 : ℂ) + (-16 : ℂ) * s))))))) / (s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
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

theorem skewQQ_qT3_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qtr0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((4 : ℂ)) + r * ((0 : ℂ) + r * ((-4 : ℂ)))))))) / (s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
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

theorem skewQQ_qT3_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qt0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ))))))) / (s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
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

theorem skewQQ_qT3_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qT0 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((16 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ))))))) / (s ^ (2 : ℕ) * (s + 3)) := by
  unfold skewQQ_qT3_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  all_goals (try ring)

theorem skewQQ_qT3_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : skewQQ_qT3_qT1 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * ((0 : ℂ) + r * (((8 : ℂ)) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))))) / (s ^ (2 : ℕ) * (s + 3)) := by
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

theorem skewPieceFS_lauR_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((-2889 / 2 : ℂ) * s ^ (2 : ℕ) + (-5733 / 2 : ℂ) * s ^ (3 : ℕ) + (-9465 / 8 : ℂ) * s ^ (4 : ℕ) + (1539 / 2 : ℂ) * s ^ (5 : ℕ) + (975 / 2 : ℂ) * s ^ (6 : ℕ) + (-861 / 4 : ℂ) * s ^ (7 : ℕ) + (-1839 / 8 : ℂ) * s ^ (8 : ℕ) + (-255 / 4 : ℂ) * s ^ (9 : ℕ) + (-6 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-972 : ℂ) * s + (-8868 : ℂ) * s ^ (2 : ℕ) + (-5069 / 2 : ℂ) * s ^ (3 : ℕ) + (28297 / 4 : ℂ) * s ^ (4 : ℕ) + (19721 / 4 : ℂ) * s ^ (5 : ℕ) + (65 : ℂ) * s ^ (6 : ℕ) + (-1805 / 2 : ℂ) * s ^ (7 : ℕ) + (-1245 / 4 : ℂ) * s ^ (8 : ℕ) + (-133 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-3024 : ℂ) * s + (3813 : ℂ) * s ^ (2 : ℕ) + (17693 : ℂ) * s ^ (3 : ℕ) + (85691 / 8 : ℂ) * s ^ (4 : ℕ) + (-1929 / 4 : ℂ) * s ^ (5 : ℕ) + (-4535 / 2 : ℂ) * s ^ (6 : ℕ) + (-2987 / 4 : ℂ) * s ^ (7 : ℕ) + (-647 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((7992 : ℂ) * s + (13530 : ℂ) * s ^ (2 : ℕ) + (3383 / 2 : ℂ) * s ^ (3 : ℕ) + (-7677 : ℂ) * s ^ (4 : ℕ) + (-4968 : ℂ) * s ^ (5 : ℕ) + (-1221 : ℂ) * s ^ (6 : ℕ) + (-231 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-3024 : ℂ) * s + (-17721 / 2 : ℂ) * s ^ (2 : ℕ) + (-18567 / 2 : ℂ) * s ^ (3 : ℕ) + (-7855 / 2 : ℂ) * s ^ (4 : ℕ) + (-1497 / 2 : ℂ) * s ^ (5 : ℕ) + (-60 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-972 : ℂ) * s + (-1242 : ℂ) * s ^ (2 : ℕ) + (-396 : ℂ) * s ^ (3 : ℕ) + (-30 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauR_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((-243 / 2 : ℂ) * s ^ (2 : ℕ) + (-1647 / 2 : ℂ) * s ^ (3 : ℕ) + (-15651 / 8 : ℂ) * s ^ (4 : ℕ) + (-3729 / 2 : ℂ) * s ^ (5 : ℕ) + (-675 / 2 : ℂ) * s ^ (6 : ℕ) + (2481 / 4 : ℂ) * s ^ (7 : ℕ) + (3675 / 8 : ℂ) * s ^ (8 : ℕ) + (495 / 4 : ℂ) * s ^ (9 : ℕ) + (12 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-162 : ℂ) * s + (-3888 : ℂ) * s ^ (2 : ℕ) + (-14274 : ℂ) * s ^ (3 : ℕ) + (-57453 / 4 : ℂ) * s ^ (4 : ℕ) + (-4123 / 4 : ℂ) * s ^ (5 : ℕ) + (12915 / 2 : ℂ) * s ^ (6 : ℕ) + (8513 / 2 : ℂ) * s ^ (7 : ℕ) + (4423 / 4 : ℂ) * s ^ (8 : ℕ) + (425 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-3456 : ℂ) * s + (-19809 : ℂ) * s ^ (2 : ℕ) + (-23478 : ℂ) * s ^ (3 : ℕ) + (52097 / 8 : ℂ) * s ^ (4 : ℕ) + (86411 / 4 : ℂ) * s ^ (5 : ℕ) + (12488 : ℂ) * s ^ (6 : ℕ) + (12429 / 4 : ℂ) * s ^ (7 : ℕ) + (2375 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-1332 : ℂ) * s + (-4020 : ℂ) * s ^ (2 : ℕ) + (21062 : ℂ) * s ^ (3 : ℕ) + (30038 : ℂ) * s ^ (4 : ℕ) + (15088 : ℂ) * s ^ (5 : ℕ) + (3494 : ℂ) * s ^ (6 : ℕ) + (326 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((4464 : ℂ) * s + (28725 / 2 : ℂ) * s ^ (2 : ℕ) + (31695 / 2 : ℂ) * s ^ (3 : ℕ) + (13995 / 2 : ℂ) * s ^ (4 : ℕ) + (2817 / 2 : ℂ) * s ^ (5 : ℕ) + (120 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((486 : ℂ) * s + (1188 : ℂ) * s ^ (2 : ℕ) + (450 : ℂ) * s ^ (3 : ℕ) + (36 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauR_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((108 : ℂ) * s ^ (3 : ℕ) + (396 : ℂ) * s ^ (4 : ℕ) + (363 : ℂ) * s ^ (5 : ℕ) + (-144 : ℂ) * s ^ (6 : ℕ) + (-408 : ℂ) * s ^ (7 : ℕ) + (-246 : ℂ) * s ^ (8 : ℕ) + (-63 : ℂ) * s ^ (9 : ℕ) + (-6 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((2952 : ℂ) * s ^ (2 : ℕ) + (7146 : ℂ) * s ^ (3 : ℕ) + (3644 : ℂ) * s ^ (4 : ℕ) + (-8861 / 2 : ℂ) * s ^ (5 : ℕ) + (-12943 / 2 : ℂ) * s ^ (6 : ℕ) + (-6587 / 2 : ℂ) * s ^ (7 : ℕ) + (-1545 / 2 : ℂ) * s ^ (8 : ℕ) + (-70 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((14772 : ℂ) * s ^ (2 : ℕ) + (10768 : ℂ) * s ^ (3 : ℕ) + (-13436 : ℂ) * s ^ (4 : ℕ) + (-40403 / 2 : ℂ) * s ^ (5 : ℕ) + (-20549 / 2 : ℂ) * s ^ (6 : ℕ) + (-4829 / 2 : ℂ) * s ^ (7 : ℕ) + (-443 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((2748 : ℂ) * s ^ (2 : ℕ) + (-14294 : ℂ) * s ^ (3 : ℕ) + (-19656 : ℂ) * s ^ (4 : ℕ) + (-9764 : ℂ) * s ^ (5 : ℕ) + (-2276 : ℂ) * s ^ (6 : ℕ) + (-214 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-4788 : ℂ) * s ^ (2 : ℕ) + (-6672 : ℂ) * s ^ (3 : ℕ) + (-3168 : ℂ) * s ^ (4 : ℕ) + (-672 : ℂ) * s ^ (5 : ℕ) + (-60 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-324 : ℂ) * s ^ (2 : ℕ) + (-144 : ℂ) * s ^ (3 : ℕ) + (-12 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauR_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qt0 s r ((s + 1) * (s + 2)) * ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((-1458 : ℂ) * s ^ (2 : ℕ) + (-6237 / 4 : ℂ) * s ^ (3 : ℕ) + (-81 / 4 : ℂ) * s ^ (4 : ℕ) + (3051 / 16 : ℂ) * s ^ (5 : ℕ) + (-3297 / 8 : ℂ) * s ^ (6 : ℕ) + (-3477 / 8 : ℂ) * s ^ (7 : ℕ) + (-657 / 4 : ℂ) * s ^ (8 : ℕ) + (-453 / 16 : ℂ) * s ^ (9 : ℕ) + (-15 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-810 : ℂ) * s + (2889 / 2 : ℂ) * s ^ (2 : ℕ) + (17145 / 4 : ℂ) * s ^ (3 : ℕ) + (24573 / 8 : ℂ) * s ^ (4 : ℕ) + (7559 / 8 : ℂ) * s ^ (5 : ℕ) + (995 / 2 : ℂ) * s ^ (6 : ℕ) + (859 / 2 : ℂ) * s ^ (7 : ℕ) + (1441 / 8 : ℂ) * s ^ (8 : ℕ) + (267 / 8 : ℂ) * s ^ (9 : ℕ) + (9 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((2340 : ℂ) * s + (5439 / 2 : ℂ) * s ^ (2 : ℕ) + (-6027 / 4 : ℂ) * s ^ (3 : ℕ) + (-7899 / 2 : ℂ) * s ^ (4 : ℕ) + (-34129 / 16 : ℂ) * s ^ (5 : ℕ) + (-3165 / 8 : ℂ) * s ^ (6 : ℕ) + (-229 / 8 : ℂ) * s ^ (7 : ℕ) + (-33 / 2 : ℂ) * s ^ (8 : ℕ) + (-81 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-2220 : ℂ) * s + (-8475 / 2 : ℂ) * s ^ (2 : ℕ) + (-11601 / 4 : ℂ) * s ^ (3 : ℕ) + (-375 / 8 : ℂ) * s ^ (4 : ℕ) + (1575 / 2 : ℂ) * s ^ (5 : ℕ) + (1179 / 4 : ℂ) * s ^ (6 : ℕ) + (135 / 4 : ℂ) * s ^ (7 : ℕ) + (5 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((720 : ℂ) * s + (2713 / 2 : ℂ) * s ^ (2 : ℕ) + (1500 : ℂ) * s ^ (3 : ℕ) + (922 : ℂ) * s ^ (4 : ℕ) + (210 : ℂ) * s ^ (5 : ℕ) + (31 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-90 : ℂ) * s + (135 : ℂ) * s ^ (2 : ℕ) + (180 : ℂ) * s ^ (3 : ℕ) + (23 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((60 : ℂ) * s + (40 : ℂ) * s ^ (2 : ℕ)))))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauR_qt0_lam s r hs hs3 hs1, ssSourceT_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((-459 : ℂ) * s ^ (2 : ℕ) + (-1683 : ℂ) * s ^ (3 : ℕ) + (-7683 / 4 : ℂ) * s ^ (4 : ℕ) + (-342 : ℂ) * s ^ (5 : ℕ) + (1719 / 2 : ℂ) * s ^ (6 : ℕ) + (1395 / 2 : ℂ) * s ^ (7 : ℕ) + (891 / 4 : ℂ) * s ^ (8 : ℕ) + (63 / 2 : ℂ) * s ^ (9 : ℕ) + (3 / 2 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-324 : ℂ) * s + (-1938 : ℂ) * s ^ (2 : ℕ) + (-2269 : ℂ) * s ^ (3 : ℕ) + (1316 : ℂ) * s ^ (4 : ℕ) + (12929 / 4 : ℂ) * s ^ (5 : ℕ) + (3043 / 2 : ℂ) * s ^ (6 : ℕ) + (109 / 2 : ℂ) * s ^ (7 : ℕ) + (-124 : ℂ) * s ^ (8 : ℕ) + (-111 / 4 : ℂ) * s ^ (9 : ℕ) + (-3 / 2 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-72 : ℂ) * s + (1296 : ℂ) * s ^ (2 : ℕ) + (5633 : ℂ) * s ^ (3 : ℕ) + (20325 / 4 : ℂ) * s ^ (4 : ℕ) + (603 / 4 : ℂ) * s ^ (5 : ℕ) + (-1534 : ℂ) * s ^ (6 : ℕ) + (-662 : ℂ) * s ^ (7 : ℕ) + (-389 / 4 : ℂ) * s ^ (8 : ℕ) + (-15 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((1008 : ℂ) * s + (3270 : ℂ) * s ^ (2 : ℕ) + (1293 : ℂ) * s ^ (3 : ℕ) + (-5673 / 2 : ℂ) * s ^ (4 : ℕ) + (-2659 : ℂ) * s ^ (5 : ℕ) + (-816 : ℂ) * s ^ (6 : ℕ) + (-90 : ℂ) * s ^ (7 : ℕ) + (-3 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-504 : ℂ) * s + (-1917 : ℂ) * s ^ (2 : ℕ) + (-2842 : ℂ) * s ^ (3 : ℕ) + (-1620 : ℂ) * s ^ (4 : ℕ) + (-382 : ℂ) * s ^ (5 : ℕ) + (-31 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s + (-252 : ℂ) * s ^ (2 : ℕ) + (-132 : ℂ) * s ^ (3 : ℕ) + (-20 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauR_qt1_lam s r hs hs3 hs1, ssSourceT1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((108 : ℂ) * s ^ (2 : ℕ) + (396 : ℂ) * s ^ (3 : ℕ) + (363 : ℂ) * s ^ (4 : ℕ) + (-144 : ℂ) * s ^ (5 : ℕ) + (-408 : ℂ) * s ^ (6 : ℕ) + (-246 : ℂ) * s ^ (7 : ℕ) + (-63 : ℂ) * s ^ (8 : ℕ) + (-6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((1314 : ℂ) * s ^ (2 : ℕ) + (1584 : ℂ) * s ^ (3 : ℕ) + (-1843 / 2 : ℂ) * s ^ (4 : ℕ) + (-4259 / 2 : ℂ) * s ^ (5 : ℕ) + (-2087 / 2 : ℂ) * s ^ (6 : ℕ) + (-265 / 2 : ℂ) * s ^ (7 : ℕ) + (27 : ℂ) * s ^ (8 : ℕ) + (6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-780 : ℂ) * s ^ (2 : ℕ) + (-3002 : ℂ) * s ^ (3 : ℕ) + (-2147 : ℂ) * s ^ (4 : ℕ) + (468 : ℂ) * s ^ (5 : ℕ) + (965 : ℂ) * s ^ (6 : ℕ) + (332 : ℂ) * s ^ (7 : ℕ) + (36 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-1224 : ℂ) * s ^ (2 : ℕ) + (-120 : ℂ) * s ^ (3 : ℕ) + (3993 / 2 : ℂ) * s ^ (4 : ℕ) + (3259 / 2 : ℂ) * s ^ (5 : ℕ) + (943 / 2 : ℂ) * s ^ (6 : ℕ) + (93 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((528 : ℂ) * s ^ (2 : ℕ) + (1106 : ℂ) * s ^ (3 : ℕ) + (703 : ℂ) * s ^ (4 : ℕ) + (176 : ℂ) * s ^ (5 : ℕ) + (15 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((54 : ℂ) * s ^ (2 : ℕ) + (36 : ℂ) * s ^ (3 : ℕ) + (6 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauR_qt2_lam s r hs hs3 hs1, ssSourceT2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((-1080 : ℂ) * s + (-909 : ℂ) * s ^ (2 : ℕ) + (186 : ℂ) * s ^ (3 : ℕ) + (843 / 4 : ℂ) * s ^ (4 : ℕ) + (-507 / 4 : ℂ) * s ^ (5 : ℕ) + (-481 / 4 : ℂ) * s ^ (6 : ℕ) + (-121 / 4 : ℂ) * s ^ (7 : ℕ) + (-5 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-720 : ℂ) + (1404 : ℂ) * s + (1973 : ℂ) * s ^ (2 : ℕ) + (1330 : ℂ) * s ^ (3 : ℕ) + (519 : ℂ) * s ^ (4 : ℕ) + (339 / 2 : ℂ) * s ^ (5 : ℕ) + (86 : ℂ) * s ^ (6 : ℕ) + (55 / 2 : ℂ) * s ^ (7 : ℕ) + (3 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((2376 : ℂ) + (936 : ℂ) * s + (-1743 : ℂ) * s ^ (2 : ℕ) + (-1533 : ℂ) * s ^ (3 : ℕ) + (-2625 / 4 : ℂ) * s ^ (4 : ℕ) + (-675 / 4 : ℂ) * s ^ (5 : ℕ) + (-117 / 4 : ℂ) * s ^ (6 : ℕ) + (-21 / 4 : ℂ) * s ^ (7 : ℕ) + (-1 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-2952 : ℂ) + (-2556 : ℂ) * s + (139 : ℂ) * s ^ (2 : ℕ) + (443 : ℂ) * s ^ (3 : ℕ) + (409 / 2 : ℂ) * s ^ (4 : ℕ) + (54 : ℂ) * s ^ (5 : ℕ) + (7 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((1656 : ℂ) + (1656 : ℂ) * s + (332 : ℂ) * s ^ (2 : ℕ) + (30 : ℂ) * s ^ (3 : ℕ) + (14 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-360 : ℂ) + (-360 : ℂ) * s + (-80 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauR_qT0_lam s r hs hs3 hs1, ssSourceTF_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((-1692 : ℂ) * s + (-3408 : ℂ) * s ^ (2 : ℕ) + (-1479 : ℂ) * s ^ (3 : ℕ) + (915 : ℂ) * s ^ (4 : ℕ) + (793 : ℂ) * s ^ (5 : ℕ) + (59 : ℂ) * s ^ (6 : ℕ) + (-70 : ℂ) * s ^ (7 : ℕ) + (-14 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-1152 : ℂ) + (-1764 : ℂ) * s + (440 : ℂ) * s ^ (2 : ℕ) + (4449 : ℂ) * s ^ (3 : ℕ) + (3534 : ℂ) * s ^ (4 : ℕ) + (324 : ℂ) * s ^ (5 : ℕ) + (-440 : ℂ) * s ^ (6 : ℕ) + (-109 : ℂ) * s ^ (7 : ℕ) + (-2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((2160 : ℂ) + (6828 : ℂ) * s + (5468 : ℂ) * s ^ (2 : ℕ) + (2230 : ℂ) * s ^ (3 : ℕ) + (-835 : ℂ) * s ^ (4 : ℕ) + (-1221 : ℂ) * s ^ (5 : ℕ) + (-289 : ℂ) * s ^ (6 : ℕ) + (-5 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((144 : ℂ) + (-1692 : ℂ) * s + (-3616 : ℂ) * s ^ (2 : ℕ) + (-2632 : ℂ) * s ^ (3 : ℕ) + (-1554 : ℂ) * s ^ (4 : ℕ) + (-344 : ℂ) * s ^ (5 : ℕ) + (-2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-2160 : ℂ) + (-2976 : ℂ) * s + (-644 : ℂ) * s ^ (2 : ℕ) + (-432 : ℂ) * s ^ (3 : ℕ) + (-156 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((1008 : ℂ) + (1296 : ℂ) * s + (320 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauR_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((-12 : ℂ) * s + (-376 : ℂ) * s ^ (2 : ℕ) + (-1291 : ℂ) * s ^ (3 : ℕ) + (-1355 : ℂ) * s ^ (4 : ℕ) + (-211 : ℂ) * s ^ (5 : ℕ) + (403 : ℂ) * s ^ (6 : ℕ) + (218 : ℂ) * s ^ (7 : ℕ) + (32 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-144 : ℂ) + (-1176 : ℂ) * s + (-4912 : ℂ) * s ^ (2 : ℕ) + (-6420 : ℂ) * s ^ (3 : ℕ) + (-772 : ℂ) * s ^ (4 : ℕ) + (3066 : ℂ) * s ^ (5 : ℕ) + (1736 : ℂ) * s ^ (6 : ℕ) + (270 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-864 : ℂ) + (-5064 : ℂ) * s + (-3776 : ℂ) * s ^ (2 : ℕ) + (2803 : ℂ) * s ^ (3 : ℕ) + (7495 : ℂ) * s ^ (4 : ℕ) + (4293 : ℂ) * s ^ (5 : ℕ) + (729 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((1728 : ℂ) + (7152 : ℂ) * s + (5648 : ℂ) * s ^ (2 : ℕ) + (5316 : ℂ) * s ^ (3 : ℕ) + (3656 : ℂ) * s ^ (4 : ℕ) + (756 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-288 : ℂ) + (180 : ℂ) * s + (-304 : ℂ) * s ^ (2 : ℕ) + (648 : ℂ) * s ^ (3 : ℕ) + (260 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-432 : ℂ) + (-1080 : ℂ) * s + (-312 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauR_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauR_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauR_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((96 : ℂ) * s ^ (2 : ℕ) + (320 : ℂ) * s ^ (3 : ℕ) + (216 : ℂ) * s ^ (4 : ℕ) + (-200 : ℂ) * s ^ (5 : ℕ) + (-296 : ℂ) * s ^ (6 : ℕ) + (-120 : ℂ) * s ^ (7 : ℕ) + (-16 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((1152 : ℂ) * s + (3408 : ℂ) * s ^ (2 : ℕ) + (1920 : ℂ) * s ^ (3 : ℕ) + (-2516 : ℂ) * s ^ (4 : ℕ) + (-3328 : ℂ) * s ^ (5 : ℕ) + (-1324 : ℂ) * s ^ (6 : ℕ) + (-176 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((1152 : ℂ) * s + (3168 : ℂ) * s ^ (2 : ℕ) + (-2888 : ℂ) * s ^ (3 : ℕ) + (-6828 : ℂ) * s ^ (4 : ℕ) + (-3400 : ℂ) * s ^ (5 : ℕ) + (-516 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-3168 : ℂ) * s + (-1488 : ℂ) * s ^ (2 : ℕ) + (-2736 : ℂ) * s ^ (3 : ℕ) + (-2232 : ℂ) * s ^ (4 : ℕ) + (-456 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((576 : ℂ) * s + (480 : ℂ) * s ^ (2 : ℕ) + (-264 : ℂ) * s ^ (3 : ℕ) + (-120 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((288 : ℂ) * s + (96 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauR_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewFSrcLam_lauR (s r : ℂ) : ℂ := (((-2784 : ℂ) * s + (-7972 : ℂ) * s ^ (2 : ℕ) + (-34769 / 4 : ℂ) * s ^ (3 : ℕ) + (-17339 / 4 : ℂ) * s ^ (4 : ℕ) + (-12353 / 16 : ℂ) * s ^ (5 : ℕ) + (729 / 8 : ℂ) * s ^ (6 : ℕ) + (93 / 8 : ℂ) * s ^ (7 : ℕ) + (-43 / 2 : ℂ) * s ^ (8 : ℕ) + (-93 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-2016 : ℂ) + (-2652 : ℂ) * s + (-16149 / 2 : ℂ) * s ^ (2 : ℕ) + (-19129 / 4 : ℂ) * s ^ (3 : ℕ) + (4689 / 8 : ℂ) * s ^ (4 : ℕ) + (13985 / 8 : ℂ) * s ^ (5 : ℕ) + (2169 / 2 : ℂ) * s ^ (6 : ℕ) + (849 / 2 : ℂ) * s ^ (7 : ℕ) + (849 / 8 : ℂ) * s ^ (8 : ℕ) + (117 / 8 : ℂ) * s ^ (9 : ℕ) + (3 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((3672 : ℂ) + (-360 : ℂ) * s + (10257 / 2 : ℂ) * s ^ (2 : ℕ) + (26877 / 4 : ℂ) * s ^ (3 : ℕ) + (1948 : ℂ) * s ^ (4 : ℕ) + (-17473 / 16 : ℂ) * s ^ (5 : ℕ) + (-8991 / 8 : ℂ) * s ^ (6 : ℕ) + (-3383 / 8 : ℂ) * s ^ (7 : ℕ) + (-335 / 4 : ℂ) * s ^ (8 : ℕ) + (-141 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-1080 : ℂ) + (5184 : ℂ) * s + (21499 / 2 : ℂ) * s ^ (2 : ℕ) + (28493 / 4 : ℂ) * s ^ (3 : ℕ) + (15141 / 8 : ℂ) * s ^ (4 : ℕ) + (124 : ℂ) * s ^ (5 : ℕ) + (-205 / 4 : ℂ) * s ^ (6 : ℕ) + (-53 / 4 : ℂ) * s ^ (7 : ℕ) + (-7 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-792 : ℂ) + (1092 : ℂ) * s + (1091 / 2 : ℂ) * s ^ (2 : ℕ) + (-362 : ℂ) * s ^ (3 : ℕ) + (-95 : ℂ) * s ^ (4 : ℕ) + (-8 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((216 : ℂ) + (-540 : ℂ) * s + (-417 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((60 : ℂ) * s + (40 : ℂ) * s ^ (2 : ℕ)))))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ))

theorem skewFSrc_lauR_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFSrc_lauR s r ((s + 1) * (s + 2)) (ssSourceTR (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2))) = skewFSrcLam_lauR s r := by
  unfold skewFSrc_lauR
  rw [skewPieceFS_lauR_qtr0 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qtr1 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qtr2 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qt0 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qt1 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qt2 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qT0 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qT1 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qT2 s r hr hf hs hs3 hs1, skewPieceFS_lauR_qT3 s r hr hf hs hs3 hs1]
  unfold skewFSrcLam_lauR
  simp only [← add_div]
  ring

theorem skewPieceFS_lauI1_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((567 / 2 : ℂ) * s + (1323 / 2 : ℂ) * s ^ (2 : ℕ) + (-441 / 8 : ℂ) * s ^ (3 : ℕ) + (-3225 / 2 : ℂ) * s ^ (4 : ℕ) + (-4281 / 2 : ℂ) * s ^ (5 : ℕ) + (-5373 / 4 : ℂ) * s ^ (6 : ℕ) + (-3663 / 8 : ℂ) * s ^ (7 : ℕ) + (-327 / 4 : ℂ) * s ^ (8 : ℕ) + (-6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((342 : ℂ) * s + (-711 / 2 : ℂ) * s ^ (2 : ℕ) + (-8921 / 4 : ℂ) * s ^ (3 : ℕ) + (-11573 / 4 : ℂ) * s ^ (4 : ℕ) + (-3889 / 2 : ℂ) * s ^ (5 : ℕ) + (-768 : ℂ) * s ^ (6 : ℕ) + (-669 / 4 : ℂ) * s ^ (7 : ℕ) + (-61 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-5307 : ℂ) * s + (-575 : ℂ) * s ^ (2 : ℕ) + (34171 / 8 : ℂ) * s ^ (3 : ℕ) + (12351 / 4 : ℂ) * s ^ (4 : ℕ) + (1857 / 2 : ℂ) * s ^ (5 : ℕ) + (477 / 4 : ℂ) * s ^ (6 : ℕ) + (25 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-438 : ℂ) * s + (4517 / 2 : ℂ) * s ^ (2 : ℕ) + (3787 / 2 : ℂ) * s ^ (3 : ℕ) + (1331 / 2 : ℂ) * s ^ (4 : ℕ) + (273 / 2 : ℂ) * s ^ (5 : ℕ) + (12 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((3447 / 2 : ℂ) * s + (4341 / 2 : ℂ) * s ^ (2 : ℕ) + (2153 / 2 : ℂ) * s ^ (3 : ℕ) + (507 / 2 : ℂ) * s ^ (4 : ℕ) + (24 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((324 : ℂ) * s + (144 : ℂ) * s ^ (2 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI1_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((405 / 2 : ℂ) * s + (2241 / 2 : ℂ) * s ^ (2 : ℕ) + (21285 / 8 : ℂ) * s ^ (3 : ℕ) + (7545 / 2 : ℂ) * s ^ (4 : ℕ) + (6999 / 2 : ℂ) * s ^ (5 : ℕ) + (8349 / 4 : ℂ) * s ^ (6 : ℕ) + (6027 / 8 : ℂ) * s ^ (7 : ℕ) + (591 / 4 : ℂ) * s ^ (8 : ℕ) + (12 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((4320 : ℂ) * s + (25821 / 2 : ℂ) * s ^ (2 : ℕ) + (83193 / 4 : ℂ) * s ^ (3 : ℕ) + (84883 / 4 : ℂ) * s ^ (4 : ℕ) + (13340 : ℂ) * s ^ (5 : ℕ) + (9893 / 2 : ℂ) * s ^ (6 : ℕ) + (3959 / 4 : ℂ) * s ^ (7 : ℕ) + (329 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((1449 : ℂ) * s + (5301 : ℂ) * s ^ (2 : ℕ) + (108521 / 8 : ℂ) * s ^ (3 : ℕ) + (51407 / 4 : ℂ) * s ^ (4 : ℕ) + (5771 : ℂ) * s ^ (5 : ℕ) + (5181 / 4 : ℂ) * s ^ (6 : ℕ) + (951 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-10404 : ℂ) * s + (-25047 / 2 : ℂ) * s ^ (2 : ℕ) + (-12319 / 2 : ℂ) * s ^ (3 : ℕ) + (-3603 / 2 : ℂ) * s ^ (4 : ℕ) + (-617 / 2 : ℂ) * s ^ (5 : ℕ) + (-19 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-14415 / 2 : ℂ) * s + (-15473 / 2 : ℂ) * s ^ (2 : ℕ) + (-7153 / 2 : ℂ) * s ^ (3 : ℕ) + (-1679 / 2 : ℂ) * s ^ (4 : ℕ) + (-80 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-648 : ℂ) * s + (-288 : ℂ) * s ^ (2 : ℕ) + (-24 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI1_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((-108 : ℂ) * s ^ (3 : ℕ) + (-504 : ℂ) * s ^ (4 : ℕ) + (-867 : ℂ) * s ^ (5 : ℕ) + (-723 : ℂ) * s ^ (6 : ℕ) + (-315 : ℂ) * s ^ (7 : ℕ) + (-69 : ℂ) * s ^ (8 : ℕ) + (-6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-2898 : ℂ) * s ^ (2 : ℕ) + (-9900 : ℂ) * s ^ (3 : ℕ) + (-27229 / 2 : ℂ) * s ^ (4 : ℕ) + (-19379 / 2 : ℂ) * s ^ (5 : ℕ) + (-7567 / 2 : ℂ) * s ^ (6 : ℕ) + (-1541 / 2 : ℂ) * s ^ (7 : ℕ) + (-64 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((1476 : ℂ) * s + (-11172 : ℂ) * s ^ (2 : ℕ) + (-25068 : ℂ) * s ^ (3 : ℕ) + (-41309 / 2 : ℂ) * s ^ (4 : ℕ) + (-17067 / 2 : ℂ) * s ^ (5 : ℕ) + (-3595 / 2 : ℂ) * s ^ (6 : ℕ) + (-309 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((8124 : ℂ) * s + (5174 : ℂ) * s ^ (2 : ℕ) + (216 : ℂ) * s ^ (3 : ℕ) + (-556 : ℂ) * s ^ (4 : ℕ) + (-196 : ℂ) * s ^ (5 : ℕ) + (-26 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((5436 : ℂ) * s + (5664 : ℂ) * s ^ (2 : ℕ) + (2616 : ℂ) * s ^ (3 : ℕ) + (624 : ℂ) * s ^ (4 : ℕ) + (60 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((324 : ℂ) * s + (144 : ℂ) * s ^ (2 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI1_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qt0 s r ((s + 1) * (s + 2)) * ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((81 : ℂ) * s + (-729 / 4 : ℂ) * s ^ (2 : ℕ) + (-2619 / 2 : ℂ) * s ^ (3 : ℕ) + (-35133 / 16 : ℂ) * s ^ (4 : ℕ) + (-14361 / 8 : ℂ) * s ^ (5 : ℕ) + (-6609 / 8 : ℂ) * s ^ (6 : ℕ) + (-219 : ℂ) * s ^ (7 : ℕ) + (-501 / 16 : ℂ) * s ^ (8 : ℕ) + (-15 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-1683 / 2 : ℂ) * s + (555 / 4 : ℂ) * s ^ (2 : ℕ) + (24071 / 8 : ℂ) * s ^ (3 : ℕ) + (32977 / 8 : ℂ) * s ^ (4 : ℕ) + (11325 / 4 : ℂ) * s ^ (5 : ℕ) + (4651 / 4 : ℂ) * s ^ (6 : ℕ) + (2305 / 8 : ℂ) * s ^ (7 : ℕ) + (315 / 8 : ℂ) * s ^ (8 : ℕ) + (9 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((1551 / 2 : ℂ) * s + (1463 / 4 : ℂ) * s ^ (2 : ℕ) + (-4663 / 4 : ℂ) * s ^ (3 : ℕ) + (-25641 / 16 : ℂ) * s ^ (4 : ℕ) + (-7485 / 8 : ℂ) * s ^ (5 : ℕ) + (-2565 / 8 : ℂ) * s ^ (6 : ℕ) + (-273 / 4 : ℂ) * s ^ (7 : ℕ) + (-129 / 16 : ℂ) * s ^ (8 : ℕ) + (-3 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((201 / 2 : ℂ) * s + (293 / 4 : ℂ) * s ^ (2 : ℕ) + (-2393 / 8 : ℂ) * s ^ (3 : ℕ) + (-1037 / 4 : ℂ) * s ^ (4 : ℕ) + (-189 / 2 : ℂ) * s ^ (5 : ℕ) + (-16 : ℂ) * s ^ (6 : ℕ) + (-7 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-181 / 2 : ℂ) * s + (-719 / 2 : ℂ) * s ^ (2 : ℕ) + (-455 / 2 : ℂ) * s ^ (3 : ℕ) + (-129 / 2 : ℂ) * s ^ (4 : ℕ) + (-6 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-13 : ℂ) * s + (-36 : ℂ) * s ^ (2 : ℕ) + (-7 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-12 : ℂ) * s))))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI1_qt0_lam s r hs hs3 hs1, ssSourceT_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((405 : ℂ) * s + (1647 : ℂ) * s ^ (2 : ℕ) + (12789 / 4 : ℂ) * s ^ (3 : ℕ) + (7389 / 2 : ℂ) * s ^ (4 : ℕ) + (5217 / 2 : ℂ) * s ^ (5 : ℕ) + (2211 / 2 : ℂ) * s ^ (6 : ℕ) + (1071 / 4 : ℂ) * s ^ (7 : ℕ) + (33 : ℂ) * s ^ (8 : ℕ) + (3 / 2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-18 : ℂ) * s + (-240 : ℂ) * s ^ (2 : ℕ) + (-243 : ℂ) * s ^ (3 : ℕ) + (-2251 / 4 : ℂ) * s ^ (4 : ℕ) + (-1849 / 2 : ℂ) * s ^ (5 : ℕ) + (-1297 / 2 : ℂ) * s ^ (6 : ℕ) + (-211 : ℂ) * s ^ (7 : ℕ) + (-123 / 4 : ℂ) * s ^ (8 : ℕ) + (-3 / 2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-1716 : ℂ) * s + (-3911 : ℂ) * s ^ (2 : ℕ) + (-18867 / 4 : ℂ) * s ^ (3 : ℕ) + (-15155 / 4 : ℂ) * s ^ (4 : ℕ) + (-1839 : ℂ) * s ^ (5 : ℕ) + (-480 : ℂ) * s ^ (6 : ℕ) + (-233 / 4 : ℂ) * s ^ (7 : ℕ) + (-9 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((438 : ℂ) * s + (1178 : ℂ) * s ^ (2 : ℕ) + (1993 / 2 : ℂ) * s ^ (3 : ℕ) + (459 : ℂ) * s ^ (4 : ℕ) + (136 : ℂ) * s ^ (5 : ℕ) + (23 : ℂ) * s ^ (6 : ℕ) + (3 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((783 : ℂ) * s + (1254 : ℂ) * s ^ (2 : ℕ) + (754 : ℂ) * s ^ (3 : ℕ) + (198 : ℂ) * s ^ (4 : ℕ) + (19 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((108 : ℂ) * s + (72 : ℂ) * s ^ (2 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI1_qt1_lam s r hs hs3 hs1, ssSourceT1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((-108 : ℂ) * s ^ (2 : ℕ) + (-504 : ℂ) * s ^ (3 : ℕ) + (-867 : ℂ) * s ^ (4 : ℕ) + (-723 : ℂ) * s ^ (5 : ℕ) + (-315 : ℂ) * s ^ (6 : ℕ) + (-69 : ℂ) * s ^ (7 : ℕ) + (-6 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((54 : ℂ) * s + (-1116 : ℂ) * s ^ (2 : ℕ) + (-5541 / 2 : ℂ) * s ^ (3 : ℕ) + (-4709 / 2 : ℂ) * s ^ (4 : ℕ) + (-1581 / 2 : ℂ) * s ^ (5 : ℕ) + (-55 / 2 : ℂ) * s ^ (6 : ℕ) + (39 : ℂ) * s ^ (7 : ℕ) + (6 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((684 : ℂ) * s + (1698 : ℂ) * s ^ (2 : ℕ) + (2854 : ℂ) * s ^ (3 : ℕ) + (2759 : ℂ) * s ^ (4 : ℕ) + (1374 : ℂ) * s ^ (5 : ℕ) + (329 : ℂ) * s ^ (6 : ℕ) + (30 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-48 : ℂ) * s + (524 : ℂ) * s ^ (2 : ℕ) + (1995 / 2 : ℂ) * s ^ (3 : ℕ) + (1229 / 2 : ℂ) * s ^ (4 : ℕ) + (309 / 2 : ℂ) * s ^ (5 : ℕ) + (27 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-636 : ℂ) * s + (-962 : ℂ) * s ^ (2 : ℕ) + (-571 : ℂ) * s ^ (3 : ℕ) + (-152 : ℂ) * s ^ (4 : ℕ) + (-15 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-54 : ℂ) * s + (-36 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI1_qt2_lam s r hs hs3 hs1, ssSourceT2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((72 : ℂ) + (-105 : ℂ) * s + (-634 : ℂ) * s ^ (2 : ℕ) + (-3425 / 4 : ℂ) * s ^ (3 : ℕ) + (-2211 / 4 : ℂ) * s ^ (4 : ℕ) + (-765 / 4 : ℂ) * s ^ (5 : ℕ) + (-137 / 4 : ℂ) * s ^ (6 : ℕ) + (-5 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-504 : ℂ) + (825 : ℂ) * s + (2365 : ℂ) * s ^ (2 : ℕ) + (1869 : ℂ) * s ^ (3 : ℕ) + (1529 / 2 : ℂ) * s ^ (4 : ℕ) + (202 : ℂ) * s ^ (5 : ℕ) + (71 / 2 : ℂ) * s ^ (6 : ℕ) + (3 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((492 : ℂ) + (-1345 : ℂ) * s + (-1487 : ℂ) * s ^ (2 : ℕ) + (-3205 / 4 : ℂ) * s ^ (3 : ℕ) + (-1219 / 4 : ℂ) * s ^ (4 : ℕ) + (-289 / 4 : ℂ) * s ^ (5 : ℕ) + (-37 / 4 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((24 : ℂ) + (383 : ℂ) * s + (230 : ℂ) * s ^ (2 : ℕ) + (169 / 2 : ℂ) * s ^ (3 : ℕ) + (21 : ℂ) * s ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-156 : ℂ) + (-70 : ℂ) * s + (-18 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((72 : ℂ) + (24 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI1_qT0_lam s r hs hs3 hs1, ssSourceTF_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((612 : ℂ) + (1848 : ℂ) * s + (2105 : ℂ) * s ^ (2 : ℕ) + (933 : ℂ) * s ^ (3 : ℕ) + (-153 : ℂ) * s ^ (4 : ℕ) + (-319 : ℂ) * s ^ (5 : ℕ) + (-116 : ℂ) * s ^ (6 : ℕ) + (-14 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-1620 : ℂ) + (-2472 : ℂ) * s + (-803 : ℂ) * s ^ (2 : ℕ) + (46 : ℂ) * s ^ (3 : ℕ) + (-348 : ℂ) * s ^ (4 : ℕ) + (-304 : ℂ) * s ^ (5 : ℕ) + (-65 : ℂ) * s ^ (6 : ℕ) + (-2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-516 : ℂ) + (-1984 : ℂ) * s + (-466 : ℂ) * s ^ (2 : ℕ) + (403 : ℂ) * s ^ (3 : ℕ) + (-7 : ℂ) * s ^ (4 : ℕ) + (-51 : ℂ) * s ^ (5 : ℕ) + (-3 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((2052 : ℂ) + (948 : ℂ) * s + (964 : ℂ) * s ^ (2 : ℕ) + (454 : ℂ) * s ^ (3 : ℕ) + (60 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-96 : ℂ) + (364 : ℂ) * s + (336 : ℂ) * s ^ (2 : ℕ) + (68 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-432 : ℂ) + (-144 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI1_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((180 : ℂ) + (840 : ℂ) * s + (1637 : ℂ) * s ^ (2 : ℕ) + (2037 : ℂ) * s ^ (3 : ℕ) + (1789 : ℂ) * s ^ (4 : ℕ) + (979 : ℂ) * s ^ (5 : ℕ) + (282 : ℂ) * s ^ (6 : ℕ) + (32 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((1128 : ℂ) + (3508 : ℂ) * s + (5640 : ℂ) * s ^ (2 : ℕ) + (6608 : ℂ) * s ^ (3 : ℕ) + (4638 : ℂ) * s ^ (4 : ℕ) + (1600 : ℂ) * s ^ (5 : ℕ) + (206 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-2040 : ℂ) + (-2288 : ℂ) * s + (-557 : ℂ) * s ^ (2 : ℕ) + (1967 : ℂ) * s ^ (3 : ℕ) + (1525 : ℂ) * s ^ (4 : ℕ) + (289 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-1392 : ℂ) + (-5612 : ℂ) * s + (-4728 : ℂ) * s ^ (2 : ℕ) + (-1148 : ℂ) * s ^ (3 : ℕ) + (-48 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((1476 : ℂ) + (-696 : ℂ) * s + (-936 : ℂ) * s ^ (2 : ℕ) + (-180 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((648 : ℂ) + (216 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI1_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI1_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI1_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((-96 : ℂ) * s ^ (2 : ℕ) + (-416 : ℂ) * s ^ (3 : ℕ) + (-632 : ℂ) * s ^ (4 : ℕ) + (-432 : ℂ) * s ^ (5 : ℕ) + (-136 : ℂ) * s ^ (6 : ℕ) + (-16 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-1104 : ℂ) * s + (-4400 : ℂ) * s ^ (2 : ℕ) + (-6420 : ℂ) * s ^ (3 : ℕ) + (-4320 : ℂ) * s ^ (4 : ℕ) + (-1356 : ℂ) * s ^ (5 : ℕ) + (-160 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((576 : ℂ) + (576 : ℂ) * s + (-3832 : ℂ) * s ^ (2 : ℕ) + (-5412 : ℂ) * s ^ (3 : ℕ) + (-2408 : ℂ) * s ^ (4 : ℕ) + (-348 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((864 : ℂ) + (5904 : ℂ) * s + (4032 : ℂ) * s ^ (2 : ℕ) + (648 : ℂ) * s ^ (3 : ℕ) + (-24 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-1152 : ℂ) + (480 : ℂ) * s + (648 : ℂ) * s ^ (2 : ℕ) + (120 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-288 : ℂ) + (-96 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI1_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewFSrcLam_lauI1 (s r : ℂ) : ℂ := (((864 : ℂ) + (3555 : ℂ) * s + (24603 / 4 : ℂ) * s ^ (2 : ℕ) + (5579 : ℂ) * s ^ (3 : ℕ) + (43823 / 16 : ℂ) * s ^ (4 : ℕ) + (4953 / 8 : ℂ) * s ^ (5 : ℕ) + (-151 / 8 : ℂ) * s ^ (6 : ℕ) + (-161 / 4 : ℂ) * s ^ (7 : ℕ) + (-117 / 16 : ℂ) * s ^ (8 : ℕ) + (-3 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-996 : ℂ) + (9227 / 2 : ℂ) * s + (44967 / 4 : ℂ) * s ^ (2 : ℕ) + (86131 / 8 : ℂ) * s ^ (3 : ℕ) + (53219 / 8 : ℂ) * s ^ (4 : ℕ) + (11857 / 4 : ℂ) * s ^ (5 : ℕ) + (3593 / 4 : ℂ) * s ^ (6 : ℕ) + (1353 / 8 : ℂ) * s ^ (7 : ℕ) + (141 / 8 : ℂ) * s ^ (8 : ℕ) + (3 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-1488 : ℂ) + (-15359 / 2 : ℂ) * s + (-58541 / 4 : ℂ) * s ^ (2 : ℕ) + (-56413 / 4 : ℂ) * s ^ (3 : ℕ) + (-136673 / 16 : ℂ) * s ^ (4 : ℕ) + (-27335 / 8 : ℂ) * s ^ (5 : ℕ) + (-6935 / 8 : ℂ) * s ^ (6 : ℕ) + (-259 / 2 : ℂ) * s ^ (7 : ℕ) + (-165 / 16 : ℂ) * s ^ (8 : ℕ) + (-3 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((1548 : ℂ) + (-1209 / 2 : ℂ) * s + (-11271 / 4 : ℂ) * s ^ (2 : ℕ) + (-18533 / 8 : ℂ) * s ^ (3 : ℕ) + (-3475 / 4 : ℂ) * s ^ (4 : ℕ) + (-337 / 2 : ℂ) * s ^ (5 : ℕ) + (-25 / 2 : ℂ) * s ^ (6 : ℕ) + (5 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((72 : ℂ) + (173 / 2 : ℂ) * s + (121 / 2 : ℂ) * s ^ (2 : ℕ) + (151 / 2 : ℂ) * s ^ (3 : ℕ) + (39 / 2 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((41 : ℂ) * s + (-1 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-12 : ℂ) * s))))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ))

theorem skewFSrc_lauI1_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFSrc_lauI1 s r ((s + 1) * (s + 2)) (ssSourceTR (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2))) = skewFSrcLam_lauI1 s r := by
  unfold skewFSrc_lauI1
  rw [skewPieceFS_lauI1_qtr0 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qtr1 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qtr2 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qt0 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qt1 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qt2 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qT0 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qT1 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qT2 s r hr hf hs hs3 hs1, skewPieceFS_lauI1_qT3 s r hr hf hs hs3 hs1]
  unfold skewFSrcLam_lauI1
  simp only [← add_div]
  ring

theorem skewPieceFS_lauI3_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR (-3 - s) r ((s + 1) * (s + 2)) = (((-3321 / 2 : ℂ) * s ^ (2 : ℕ) + (-13797 / 2 : ℂ) * s ^ (3 : ℕ) + (-98217 / 8 : ℂ) * s ^ (4 : ℕ) + (-24561 / 2 : ℂ) * s ^ (5 : ℕ) + (-15165 / 2 : ℂ) * s ^ (6 : ℕ) + (-11877 / 4 : ℂ) * s ^ (7 : ℕ) + (-5775 / 8 : ℂ) * s ^ (8 : ℕ) + (-399 / 4 : ℂ) * s ^ (9 : ℕ) + (-6 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-972 : ℂ) * s + (-8352 : ℂ) * s ^ (2 : ℕ) + (-30237 / 2 : ℂ) * s ^ (3 : ℕ) + (-44931 / 4 : ℂ) * s ^ (4 : ℕ) + (-14043 / 4 : ℂ) * s ^ (5 : ℕ) + (-56 : ℂ) * s ^ (6 : ℕ) + (461 / 2 : ℂ) * s ^ (7 : ℕ) + (195 / 4 : ℂ) * s ^ (8 : ℕ) + (11 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-3024 : ℂ) * s + (9501 : ℂ) * s ^ (2 : ℕ) + (30641 : ℂ) * s ^ (3 : ℕ) + (246635 / 8 : ℂ) * s ^ (4 : ℕ) + (63615 / 4 : ℂ) * s ^ (5 : ℕ) + (9349 / 2 : ℂ) * s ^ (6 : ℕ) + (3005 / 4 : ℂ) * s ^ (7 : ℕ) + (409 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((7992 : ℂ) * s + (3978 : ℂ) * s ^ (2 : ℕ) + (-3225 / 2 : ℂ) * s ^ (3 : ℕ) + (-2086 : ℂ) * s ^ (4 : ℕ) + (-667 : ℂ) * s ^ (5 : ℕ) + (-44 : ℂ) * s ^ (6 : ℕ) + (15 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-3024 : ℂ) * s + (-12537 / 2 : ℂ) * s ^ (2 : ℕ) + (-5487 / 2 : ℂ) * s ^ (3 : ℕ) + (-543 / 2 : ℂ) * s ^ (4 : ℕ) + (111 / 2 : ℂ) * s ^ (5 : ℕ) + (12 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-972 : ℂ) * s + (-270 : ℂ) * s ^ (2 : ℕ) + (36 : ℂ) * s ^ (3 : ℕ) + (6 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI3_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2)) = (((648 : ℂ) * s + (7965 / 2 : ℂ) * s ^ (2 : ℕ) + (20565 / 2 : ℂ) * s ^ (3 : ℕ) + (120669 / 8 : ℂ) * s ^ (4 : ℕ) + (28383 / 2 : ℂ) * s ^ (5 : ℕ) + (18021 / 2 : ℂ) * s ^ (6 : ℕ) + (15465 / 4 : ℂ) * s ^ (7 : ℕ) + (8571 / 8 : ℂ) * s ^ (8 : ℕ) + (687 / 4 : ℂ) * s ^ (9 : ℕ) + (12 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((13338 : ℂ) * s + (46584 : ℂ) * s ^ (2 : ℕ) + (73497 : ℂ) * s ^ (3 : ℕ) + (279911 / 4 : ℂ) * s ^ (4 : ℕ) + (176873 / 4 : ℂ) * s ^ (5 : ℕ) + (37577 / 2 : ℂ) * s ^ (6 : ℕ) + (10321 / 2 : ℂ) * s ^ (7 : ℕ) + (3303 / 4 : ℂ) * s ^ (8 : ℕ) + (233 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-5040 : ℂ) * s + (-18837 : ℂ) * s ^ (2 : ℕ) + (-27298 : ℂ) * s ^ (3 : ℕ) + (-166111 / 8 : ℂ) * s ^ (4 : ℕ) + (-39141 / 4 : ℂ) * s ^ (5 : ℕ) + (-2940 : ℂ) * s ^ (6 : ℕ) + (-2003 / 4 : ℂ) * s ^ (7 : ℕ) + (-281 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-21852 : ℂ) * s + (-47532 : ℂ) * s ^ (2 : ℕ) + (-51783 : ℂ) * s ^ (3 : ℕ) + (-32823 : ℂ) * s ^ (4 : ℕ) + (-12285 : ℂ) * s ^ (5 : ℕ) + (-2517 : ℂ) * s ^ (6 : ℕ) + (-216 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((11448 : ℂ) * s + (7677 / 2 : ℂ) * s ^ (2 : ℕ) + (-11073 / 2 : ℂ) * s ^ (3 : ℕ) + (-8349 / 2 : ℂ) * s ^ (4 : ℕ) + (-2271 / 2 : ℂ) * s ^ (5 : ℕ) + (-120 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((1458 : ℂ) * s + (-324 : ℂ) * s ^ (2 : ℕ) + (-378 : ℂ) * s ^ (3 : ℕ) + (-36 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI3_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2)) = (((-108 : ℂ) * s ^ (3 : ℕ) + (-612 : ℂ) * s ^ (4 : ℕ) + (-1371 : ℂ) * s ^ (5 : ℕ) + (-1590 : ℂ) * s ^ (6 : ℕ) + (-1038 : ℂ) * s ^ (7 : ℕ) + (-384 : ℂ) * s ^ (8 : ℕ) + (-75 : ℂ) * s ^ (9 : ℕ) + (-6 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-2952 : ℂ) * s ^ (2 : ℕ) + (-12942 : ℂ) * s ^ (3 : ℕ) + (-23444 : ℂ) * s ^ (4 : ℕ) + (-45597 / 2 : ℂ) * s ^ (5 : ℕ) + (-25815 / 2 : ℂ) * s ^ (6 : ℕ) + (-8547 / 2 : ℂ) * s ^ (7 : ℕ) + (-1537 / 2 : ℂ) * s ^ (8 : ℕ) + (-58 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-11820 : ℂ) * s ^ (2 : ℕ) + (-33112 : ℂ) * s ^ (3 : ℕ) + (-36700 : ℂ) * s ^ (4 : ℕ) + (-42215 / 2 : ℂ) * s ^ (5 : ℕ) + (-13585 / 2 : ℂ) * s ^ (6 : ℕ) + (-2361 / 2 : ℂ) * s ^ (7 : ℕ) + (-175 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((13500 : ℂ) * s ^ (2 : ℕ) + (24642 : ℂ) * s ^ (3 : ℕ) + (20088 : ℂ) * s ^ (4 : ℕ) + (8652 : ℂ) * s ^ (5 : ℕ) + (1884 : ℂ) * s ^ (6 : ℕ) + (162 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((15660 : ℂ) * s ^ (2 : ℕ) + (18000 : ℂ) * s ^ (3 : ℕ) + (8400 : ℂ) * s ^ (4 : ℕ) + (1920 : ℂ) * s ^ (5 : ℕ) + (180 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((972 : ℂ) * s ^ (2 : ℕ) + (432 : ℂ) * s ^ (3 : ℕ) + (36 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI3_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qt0 s r ((s + 1) * (s + 2)) * ssSourceT (-3 - s) r ((s + 1) * (s + 2)) = (((-648 : ℂ) * s + (-3564 : ℂ) * s ^ (2 : ℕ) + (-31725 / 4 : ℂ) * s ^ (3 : ℕ) + (-39219 / 4 : ℂ) * s ^ (4 : ℕ) + (-121365 / 16 : ℂ) * s ^ (5 : ℕ) + (-30825 / 8 : ℂ) * s ^ (6 : ℕ) + (-10341 / 8 : ℂ) * s ^ (7 : ℕ) + (-1107 / 4 : ℂ) * s ^ (8 : ℕ) + (-549 / 16 : ℂ) * s ^ (9 : ℕ) + (-15 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((1386 : ℂ) * s + (17697 / 2 : ℂ) * s ^ (2 : ℕ) + (79141 / 4 : ℂ) * s ^ (3 : ℕ) + (183297 / 8 : ℂ) * s ^ (4 : ℕ) + (127651 / 8 : ℂ) * s ^ (5 : ℕ) + (7162 : ℂ) * s ^ (6 : ℕ) + (2121 : ℂ) * s ^ (7 : ℕ) + (3241 / 8 : ℂ) * s ^ (8 : ℕ) + (363 / 8 : ℂ) * s ^ (9 : ℕ) + (9 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-372 : ℂ) * s + (-13169 / 2 : ℂ) * s ^ (2 : ℕ) + (-58735 / 4 : ℂ) * s ^ (3 : ℕ) + (-15084 : ℂ) * s ^ (4 : ℕ) + (-144401 / 16 : ℂ) * s ^ (5 : ℕ) + (-27333 / 8 : ℂ) * s ^ (6 : ℕ) + (-6701 / 8 : ℂ) * s ^ (7 : ℕ) + (-129 : ℂ) * s ^ (8 : ℕ) + (-177 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-756 : ℂ) * s + (1213 / 2 : ℂ) * s ^ (2 : ℕ) + (9235 / 4 : ℂ) * s ^ (3 : ℕ) + (14549 / 8 : ℂ) * s ^ (4 : ℕ) + (641 : ℂ) * s ^ (5 : ℕ) + (429 / 4 : ℂ) * s ^ (6 : ℕ) + (37 / 4 : ℂ) * s ^ (7 : ℕ) + (5 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((360 : ℂ) * s + (909 / 2 : ℂ) * s ^ (2 : ℕ) + (477 : ℂ) * s ^ (3 : ℕ) + (155 : ℂ) * s ^ (4 : ℕ) + (13 : ℂ) * s ^ (5 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-6 : ℂ) * s + (239 : ℂ) * s ^ (2 : ℕ) + (44 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((36 : ℂ) * s))))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI3_qt0_lam s r hs hs3 hs1, ssSourceT_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 (-3 - s) r ((s + 1) * (s + 2)) = (((1296 : ℂ) * s + (5589 : ℂ) * s ^ (2 : ℕ) + (10773 : ℂ) * s ^ (3 : ℕ) + (49341 / 4 : ℂ) * s ^ (4 : ℕ) + (9255 : ℂ) * s ^ (5 : ℕ) + (9315 / 2 : ℂ) * s ^ (6 : ℕ) + (3075 / 2 : ℂ) * s ^ (7 : ℕ) + (1251 / 4 : ℂ) * s ^ (8 : ℕ) + (69 / 2 : ℂ) * s ^ (9 : ℕ) + (3 / 2 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-684 : ℂ) * s + (-4290 : ℂ) * s ^ (2 : ℕ) + (-9415 : ℂ) * s ^ (3 : ℕ) + (-11126 : ℂ) * s ^ (4 : ℕ) + (-33383 / 4 : ℂ) * s ^ (5 : ℕ) + (-8445 / 2 : ℂ) * s ^ (6 : ℕ) + (-2847 / 2 : ℂ) * s ^ (7 : ℕ) + (-298 : ℂ) * s ^ (8 : ℕ) + (-135 / 4 : ℂ) * s ^ (9 : ℕ) + (-3 / 2 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-4248 : ℂ) * s + (-11496 : ℂ) * s ^ (2 : ℕ) + (-14379 : ℂ) * s ^ (3 : ℕ) + (-42523 / 4 : ℂ) * s ^ (4 : ℕ) + (-19633 / 4 : ℂ) * s ^ (5 : ℕ) + (-1388 : ℂ) * s ^ (6 : ℕ) + (-226 : ℂ) * s ^ (7 : ℕ) + (-77 / 4 : ℂ) * s ^ (8 : ℕ) + (-3 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((5040 : ℂ) * s + (11862 : ℂ) * s ^ (2 : ℕ) + (13099 : ℂ) * s ^ (3 : ℕ) + (17843 / 2 : ℂ) * s ^ (4 : ℕ) + (3805 : ℂ) * s ^ (5 : ℕ) + (932 : ℂ) * s ^ (6 : ℕ) + (112 : ℂ) * s ^ (7 : ℕ) + (9 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-1080 : ℂ) * s + (-1557 : ℂ) * s ^ (2 : ℕ) + (-114 : ℂ) * s ^ (3 : ℕ) + (488 : ℂ) * s ^ (4 : ℕ) + (194 : ℂ) * s ^ (5 : ℕ) + (21 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-324 : ℂ) * s + (-108 : ℂ) * s ^ (2 : ℕ) + (36 : ℂ) * s ^ (3 : ℕ) + (12 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI3_qt1_lam s r hs hs3 hs1, ssSourceT1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 (-3 - s) r ((s + 1) * (s + 2)) = (((-108 : ℂ) * s ^ (2 : ℕ) + (-612 : ℂ) * s ^ (3 : ℕ) + (-1371 : ℂ) * s ^ (4 : ℕ) + (-1590 : ℂ) * s ^ (5 : ℕ) + (-1038 : ℂ) * s ^ (6 : ℕ) + (-384 : ℂ) * s ^ (7 : ℕ) + (-75 : ℂ) * s ^ (8 : ℕ) + (-6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-1206 : ℂ) * s ^ (2 : ℕ) + (-3816 : ℂ) * s ^ (3 : ℕ) + (-9239 / 2 : ℂ) * s ^ (4 : ℕ) + (-5159 / 2 : ℂ) * s ^ (5 : ℕ) + (-1075 / 2 : ℂ) * s ^ (6 : ℕ) + (155 / 2 : ℂ) * s ^ (7 : ℕ) + (51 : ℂ) * s ^ (8 : ℕ) + (6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((2148 : ℂ) * s ^ (2 : ℕ) + (6398 : ℂ) * s ^ (3 : ℕ) + (7855 : ℂ) * s ^ (4 : ℕ) + (5050 : ℂ) * s ^ (5 : ℕ) + (1783 : ℂ) * s ^ (6 : ℕ) + (326 : ℂ) * s ^ (7 : ℕ) + (24 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((1128 : ℂ) * s ^ (2 : ℕ) + (1168 : ℂ) * s ^ (3 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (-801 / 2 : ℂ) * s ^ (5 : ℕ) + (-325 / 2 : ℂ) * s ^ (6 : ℕ) + (-39 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-1800 : ℂ) * s ^ (2 : ℕ) + (-3030 : ℂ) * s ^ (3 : ℕ) + (-1845 : ℂ) * s ^ (4 : ℕ) + (-480 : ℂ) * s ^ (5 : ℕ) + (-45 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-162 : ℂ) * s ^ (2 : ℕ) + (-108 : ℂ) * s ^ (3 : ℕ) + (-18 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI3_qt2_lam s r hs hs3 hs1, ssSourceT2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF (-3 - s) r ((s + 1) * (s + 2)) = (((-576 : ℂ) + (-2760 : ℂ) * s + (-5077 : ℂ) * s ^ (2 : ℕ) + (-4962 : ℂ) * s ^ (3 : ℕ) + (-11709 / 4 : ℂ) * s ^ (4 : ℕ) + (-4411 / 4 : ℂ) * s ^ (5 : ℕ) + (-1065 / 4 : ℂ) * s ^ (6 : ℕ) + (-153 / 4 : ℂ) * s ^ (7 : ℕ) + (-5 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((2160 : ℂ) + (9588 : ℂ) * s + (15205 : ℂ) * s ^ (2 : ℕ) + (12228 : ℂ) * s ^ (3 : ℕ) + (5727 : ℂ) * s ^ (4 : ℕ) + (3367 / 2 : ℂ) * s ^ (5 : ℕ) + (330 : ℂ) * s ^ (6 : ℕ) + (87 / 2 : ℂ) * s ^ (7 : ℕ) + (3 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-2664 : ℂ) + (-11760 : ℂ) * s + (-14739 : ℂ) * s ^ (2 : ℕ) + (-8541 : ℂ) * s ^ (3 : ℕ) + (-11737 / 4 : ℂ) * s ^ (4 : ℕ) + (-2867 / 4 : ℂ) * s ^ (5 : ℕ) + (-509 / 4 : ℂ) * s ^ (6 : ℕ) + (-53 / 4 : ℂ) * s ^ (7 : ℕ) + (-1 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((936 : ℂ) + (5580 : ℂ) * s + (4603 : ℂ) * s ^ (2 : ℕ) + (1765 : ℂ) * s ^ (3 : ℕ) + (865 / 2 : ℂ) * s ^ (4 : ℕ) + (64 : ℂ) * s ^ (5 : ℕ) + (7 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((360 : ℂ) + (-576 : ℂ) * s + (-280 : ℂ) * s ^ (2 : ℕ) + (-34 : ℂ) * s ^ (3 : ℕ) + (-6 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-216 : ℂ) + (-72 : ℂ) * s))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI3_qT0_lam s r hs hs3 hs1, ssSourceTF_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2)) = (((1152 : ℂ) + (3108 : ℂ) * s + (2336 : ℂ) * s ^ (2 : ℕ) + (-1015 : ℂ) * s ^ (3 : ℕ) + (-2825 : ℂ) * s ^ (4 : ℕ) + (-2075 : ℂ) * s ^ (5 : ℕ) + (-793 : ℂ) * s ^ (6 : ℕ) + (-162 : ℂ) * s ^ (7 : ℕ) + (-14 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-3456 : ℂ) + (-7620 : ℂ) * s + (-5384 : ℂ) * s ^ (2 : ℕ) + (-167 : ℂ) * s ^ (3 : ℕ) + (1518 : ℂ) * s ^ (4 : ℕ) + (612 : ℂ) * s ^ (5 : ℕ) + (24 : ℂ) * s ^ (6 : ℕ) + (-21 : ℂ) * s ^ (7 : ℕ) + (-2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((2448 : ℂ) + (3660 : ℂ) * s + (3396 : ℂ) * s ^ (2 : ℕ) + (3894 : ℂ) * s ^ (3 : ℕ) + (2793 : ℂ) * s ^ (4 : ℕ) + (871 : ℂ) * s ^ (5 : ℕ) + (91 : ℂ) * s ^ (6 : ℕ) + (-1 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((2160 : ℂ) + (2724 : ℂ) * s + (-568 : ℂ) * s ^ (2 : ℕ) + (-400 : ℂ) * s ^ (3 : ℕ) + (382 : ℂ) * s ^ (4 : ℕ) + (144 : ℂ) * s ^ (5 : ℕ) + (6 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-3600 : ℂ) + (-2016 : ℂ) * s + (-1124 : ℂ) * s ^ (2 : ℕ) + (-176 : ℂ) * s ^ (3 : ℕ) + (36 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((1296 : ℂ) + (144 : ℂ) * s + (-96 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI3_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2)) = (((576 : ℂ) + (3252 : ℂ) * s + (7512 : ℂ) * s ^ (2 : ℕ) + (9685 : ℂ) * s ^ (3 : ℕ) + (7973 : ℂ) * s ^ (4 : ℕ) + (4429 : ℂ) * s ^ (5 : ℕ) + (1619 : ℂ) * s ^ (6 : ℕ) + (346 : ℂ) * s ^ (7 : ℕ) + (32 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((3024 : ℂ) + (11496 : ℂ) * s + (18760 : ℂ) * s ^ (2 : ℕ) + (18276 : ℂ) * s ^ (3 : ℕ) + (12052 : ℂ) * s ^ (4 : ℕ) + (5282 : ℂ) * s ^ (5 : ℕ) + (1336 : ℂ) * s ^ (6 : ℕ) + (142 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-9504 : ℂ) + (-24936 : ℂ) * s + (-28304 : ℂ) * s ^ (2 : ℕ) + (-18605 : ℂ) * s ^ (3 : ℕ) + (-7001 : ℂ) * s ^ (4 : ℕ) + (-1307 : ℂ) * s ^ (5 : ℕ) + (-87 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((6336 : ℂ) + (4464 : ℂ) * s + (-4568 : ℂ) * s ^ (2 : ℕ) + (-7604 : ℂ) * s ^ (3 : ℕ) + (-3440 : ℂ) * s ^ (4 : ℕ) + (-500 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((864 : ℂ) + (5076 : ℂ) * s + (2208 : ℂ) * s ^ (2 : ℕ) + (-696 : ℂ) * s ^ (3 : ℕ) + (-300 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-1296 : ℂ) + (648 : ℂ) * s + (360 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI3_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceFS_lauI3_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFQ_lauI3_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2)) = (((-96 : ℂ) * s ^ (2 : ℕ) + (-512 : ℂ) * s ^ (3 : ℕ) + (-1048 : ℂ) * s ^ (4 : ℕ) + (-1064 : ℂ) * s ^ (5 : ℕ) + (-568 : ℂ) * s ^ (6 : ℕ) + (-152 : ℂ) * s ^ (7 : ℕ) + (-16 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-1152 : ℂ) * s + (-5616 : ℂ) * s ^ (2 : ℕ) + (-10720 : ℂ) * s ^ (3 : ℕ) + (-10324 : ℂ) * s ^ (4 : ℕ) + (-5312 : ℂ) * s ^ (5 : ℕ) + (-1388 : ℂ) * s ^ (6 : ℕ) + (-144 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-2016 : ℂ) * s ^ (2 : ℕ) + (-4776 : ℂ) * s ^ (3 : ℕ) + (-3996 : ℂ) * s ^ (4 : ℕ) + (-1416 : ℂ) * s ^ (5 : ℕ) + (-180 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((4896 : ℂ) * s + (13296 : ℂ) * s ^ (2 : ℕ) + (10800 : ℂ) * s ^ (3 : ℕ) + (3528 : ℂ) * s ^ (4 : ℕ) + (408 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-2880 : ℂ) * s + (480 : ℂ) * s ^ (2 : ℕ) + (1560 : ℂ) * s ^ (3 : ℕ) + (360 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-864 : ℂ) * s + (-288 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewFQ_lauI3_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam' s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewFSrcLam_lauI3 (s r : ℂ) : ℂ := (((1152 : ℂ) + (4896 : ℂ) * s + (8914 : ℂ) * s ^ (2 : ℕ) + (34807 / 4 : ℂ) * s ^ (3 : ℕ) + (18107 / 4 : ℂ) * s ^ (4 : ℕ) + (12911 / 16 : ℂ) * s ^ (5 : ℕ) + (-3231 / 8 : ℂ) * s ^ (6 : ℕ) + (-2291 / 8 : ℂ) * s ^ (7 : ℕ) + (-74 : ℂ) * s ^ (8 : ℕ) + (-141 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((1728 : ℂ) + (25380 : ℂ) * s + (123195 / 2 : ℂ) * s ^ (2 : ℕ) + (286431 / 4 : ℂ) * s ^ (3 : ℕ) + (411525 / 8 : ℂ) * s ^ (4 : ℕ) + (201645 / 8 : ℂ) * s ^ (5 : ℕ) + (8529 : ℂ) * s ^ (6 : ℕ) + (1913 : ℂ) * s ^ (7 : ℕ) + (2121 / 8 : ℂ) * s ^ (8 : ℕ) + (165 / 8 : ℂ) * s ^ (9 : ℕ) + (3 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-9720 : ℂ) + (-45720 : ℂ) * s + (-157503 / 2 : ℂ) * s ^ (2 : ℕ) + (-321847 / 4 : ℂ) * s ^ (3 : ℕ) + (-111265 / 2 : ℂ) * s ^ (4 : ℕ) + (-423057 / 16 : ℂ) * s ^ (5 : ℕ) + (-67063 / 8 : ℂ) * s ^ (6 : ℕ) + (-13455 / 8 : ℂ) * s ^ (7 : ℕ) + (-785 / 4 : ℂ) * s ^ (8 : ℕ) + (-189 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((9432 : ℂ) + (8088 : ℂ) * s + (-7389 / 2 : ℂ) * s ^ (2 : ℕ) + (-30467 / 4 : ℂ) * s ^ (3 : ℕ) + (-25439 / 8 : ℂ) * s ^ (4 : ℕ) + (-277 / 2 : ℂ) * s ^ (5 : ℕ) + (837 / 4 : ℂ) * s ^ (6 : ℕ) + (221 / 4 : ℂ) * s ^ (7 : ℕ) + (41 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-2376 : ℂ) + (7308 : ℂ) * s + (23223 / 2 : ℂ) * s ^ (2 : ℕ) + (7707 : ℂ) * s ^ (3 : ℕ) + (2842 : ℂ) * s ^ (4 : ℕ) + (567 : ℂ) * s ^ (5 : ℕ) + (97 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-216 : ℂ) + (12 : ℂ) * s + (323 : ℂ) * s ^ (2 : ℕ) + (62 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((36 : ℂ) * s))))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (3 : ℕ) * (s + 3) ^ (2 : ℕ))

theorem skewFSrc_lauI3_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewFSrc_lauI3 s r ((s + 1) * (s + 2)) (ssSourceTR (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTR2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceT2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF1 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF2 (-3 - s) r ((s + 1) * (s + 2))) (ssSourceTF3 (-3 - s) r ((s + 1) * (s + 2))) = skewFSrcLam_lauI3 s r := by
  unfold skewFSrc_lauI3
  rw [skewPieceFS_lauI3_qtr0 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qtr1 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qtr2 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qt0 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qt1 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qt2 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qT0 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qT1 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qT2 s r hr hf hs hs3 hs1, skewPieceFS_lauI3_qT3 s r hr hf hs hs3 hs1]
  unfold skewFSrcLam_lauI3
  simp only [← add_div]
  ring

/-! ## Sources against the reflected family -/

theorem skewPieceSF_qtr0_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr0_lauR s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-1080 : ℂ) * s ^ (2 : ℕ) + (-24345 / 4 : ℂ) * s ^ (3 : ℕ) + (-108285 / 8 : ℂ) * s ^ (4 : ℕ) + (-62667 / 4 : ℂ) * s ^ (5 : ℕ) + (-41583 / 4 : ℂ) * s ^ (6 : ℕ) + (-16347 / 4 : ℂ) * s ^ (7 : ℕ) + (-7509 / 8 : ℂ) * s ^ (8 : ℕ) + (-465 / 4 : ℂ) * s ^ (9 : ℕ) + (-6 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((1440 : ℂ) * s + (13821 : ℂ) * s ^ (2 : ℕ) + (75995 / 2 : ℂ) * s ^ (3 : ℕ) + (48019 : ℂ) * s ^ (4 : ℕ) + (142207 / 4 : ℂ) * s ^ (5 : ℕ) + (31987 / 2 : ℂ) * s ^ (6 : ℕ) + (8411 / 2 : ℂ) * s ^ (7 : ℕ) + (1173 / 2 : ℂ) * s ^ (8 : ℕ) + (133 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-10008 : ℂ) * s + (-41970 : ℂ) * s ^ (2 : ℕ) + (-214859 / 4 : ℂ) * s ^ (3 : ℕ) + (-328399 / 8 : ℂ) * s ^ (4 : ℕ) + (-21480 : ℂ) * s ^ (5 : ℕ) + (-27865 / 4 : ℂ) * s ^ (6 : ℕ) + (-4777 / 4 : ℂ) * s ^ (7 : ℕ) + (-647 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((19620 : ℂ) * s + (30990 : ℂ) * s ^ (2 : ℕ) + (21407 : ℂ) * s ^ (3 : ℕ) + (22311 / 2 : ℂ) * s ^ (4 : ℕ) + (9639 / 2 : ℂ) * s ^ (5 : ℕ) + (2409 / 2 : ℂ) * s ^ (6 : ℕ) + (231 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-7992 : ℂ) * s + (-8199 : ℂ) * s ^ (2 : ℕ) + (-5763 / 2 : ℂ) * s ^ (3 : ℕ) + (-800 : ℂ) * s ^ (4 : ℕ) + (-663 / 2 : ℂ) * s ^ (5 : ℕ) + (-60 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((972 : ℂ) * s + (702 : ℂ) * s ^ (2 : ℕ) + (36 : ℂ) * s ^ (3 : ℕ) + (-30 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qtr0_lauR_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr1_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr1_lauR s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((6480 : ℂ) * s ^ (2 : ℕ) + (107973 / 4 : ℂ) * s ^ (3 : ℕ) + (376569 / 8 : ℂ) * s ^ (4 : ℕ) + (179907 / 4 : ℂ) * s ^ (5 : ℕ) + (103419 / 4 : ℂ) * s ^ (6 : ℕ) + (36759 / 4 : ℂ) * s ^ (7 : ℕ) + (15825 / 8 : ℂ) * s ^ (8 : ℕ) + (945 / 4 : ℂ) * s ^ (9 : ℕ) + (12 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-5184 : ℂ) * s + (-42498 : ℂ) * s ^ (2 : ℕ) + (-104724 : ℂ) * s ^ (3 : ℕ) + (-133092 : ℂ) * s ^ (4 : ℕ) + (-398825 / 4 : ℂ) * s ^ (5 : ℕ) + (-45255 : ℂ) * s ^ (6 : ℕ) + (-24287 / 2 : ℂ) * s ^ (7 : ℕ) + (-1763 : ℂ) * s ^ (8 : ℕ) + (-425 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((18036 : ℂ) * s + (86841 : ℂ) * s ^ (2 : ℕ) + (526869 / 4 : ℂ) * s ^ (3 : ℕ) + (922247 / 8 : ℂ) * s ^ (4 : ℕ) + (64786 : ℂ) * s ^ (5 : ℕ) + (88193 / 4 : ℂ) * s ^ (6 : ℕ) + (16071 / 4 : ℂ) * s ^ (7 : ℕ) + (2375 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-27324 : ℂ) * s + (-63654 : ℂ) * s ^ (2 : ℕ) + (-55976 : ℂ) * s ^ (3 : ℕ) + (-32662 : ℂ) * s ^ (4 : ℕ) + (-13810 : ℂ) * s ^ (5 : ℕ) + (-3352 : ℂ) * s ^ (6 : ℕ) + (-326 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((14076 : ℂ) * s + (15105 : ℂ) * s ^ (2 : ℕ) + (12315 / 2 : ℂ) * s ^ (3 : ℕ) + (2070 : ℂ) * s ^ (4 : ℕ) + (1503 / 2 : ℂ) * s ^ (5 : ℕ) + (120 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-1620 : ℂ) * s + (-918 : ℂ) * s ^ (2 : ℕ) + (-18 : ℂ) * s ^ (3 : ℕ) + (36 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qtr1_lauR_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr2_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr2_lauR s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((-3240 : ℂ) * s ^ (2 : ℕ) + (-13446 : ℂ) * s ^ (3 : ℕ) + (-23355 : ℂ) * s ^ (4 : ℕ) + (-22233 : ℂ) * s ^ (5 : ℕ) + (-12744 : ℂ) * s ^ (6 : ℕ) + (-4524 : ℂ) * s ^ (7 : ℕ) + (-975 : ℂ) * s ^ (8 : ℕ) + (-117 : ℂ) * s ^ (9 : ℕ) + (-6 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((1728 : ℂ) * s + (18477 : ℂ) * s ^ (2 : ℕ) + (104259 / 2 : ℂ) * s ^ (3 : ℕ) + (143983 / 2 : ℂ) * s ^ (4 : ℕ) + (56815 : ℂ) * s ^ (5 : ℕ) + (26782 : ℂ) * s ^ (6 : ℕ) + (14867 / 2 : ℂ) * s ^ (7 : ℕ) + (2235 / 2 : ℂ) * s ^ (8 : ℕ) + (70 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-5976 : ℂ) * s + (-36861 : ℂ) * s ^ (2 : ℕ) + (-142319 / 2 : ℂ) * s ^ (3 : ℕ) + (-143347 / 2 : ℂ) * s ^ (4 : ℕ) + (-43307 : ℂ) * s ^ (5 : ℕ) + (-15388 : ℂ) * s ^ (6 : ℕ) + (-5803 / 2 : ℂ) * s ^ (7 : ℕ) + (-443 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((7632 : ℂ) * s + (32952 : ℂ) * s ^ (2 : ℕ) + (34832 : ℂ) * s ^ (3 : ℕ) + (21774 : ℂ) * s ^ (4 : ℕ) + (9242 : ℂ) * s ^ (5 : ℕ) + (2218 : ℂ) * s ^ (6 : ℕ) + (214 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-6048 : ℂ) * s + (-7272 : ℂ) * s ^ (2 : ℕ) + (-3264 : ℂ) * s ^ (3 : ℕ) + (-1188 : ℂ) * s ^ (4 : ℕ) + (-408 : ℂ) * s ^ (5 : ℕ) + (-60 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((648 : ℂ) * s + (324 : ℂ) * s ^ (2 : ℕ) + (-12 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qtr2_lauR_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt0_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt0_lauR s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((324 : ℂ) * s ^ (3 : ℕ) + (11745 / 16 : ℂ) * s ^ (4 : ℕ) + (5265 / 16 : ℂ) * s ^ (5 : ℕ) + (-357 : ℂ) * s ^ (6 : ℕ) + (-3273 / 8 : ℂ) * s ^ (7 : ℕ) + (-2547 / 16 : ℂ) * s ^ (8 : ℕ) + (-447 / 16 : ℂ) * s ^ (9 : ℕ) + (-15 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-324 : ℂ) * s ^ (2 : ℕ) + (-7137 / 2 : ℂ) * s ^ (3 : ℕ) + (-5931 : ℂ) * s ^ (4 : ℕ) + (-29285 / 8 : ℂ) * s ^ (5 : ℕ) + (-1105 / 2 : ℂ) * s ^ (6 : ℕ) + (370 : ℂ) * s ^ (7 : ℕ) + (761 / 4 : ℂ) * s ^ (8 : ℕ) + (273 / 8 : ℂ) * s ^ (9 : ℕ) + (9 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-2304 : ℂ) * s + (-4611 : ℂ) * s ^ (2 : ℕ) + (663 : ℂ) * s ^ (3 : ℕ) + (91641 / 16 : ℂ) * s ^ (4 : ℕ) + (66853 / 16 : ℂ) * s ^ (5 : ℕ) + (2301 / 2 : ℂ) * s ^ (6 : ℕ) + (463 / 8 : ℂ) * s ^ (7 : ℕ) + (-507 / 16 : ℂ) * s ^ (8 : ℕ) + (-99 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-3168 : ℂ) + (-444 : ℂ) * s + (5361 : ℂ) * s ^ (2 : ℕ) + (6903 / 2 : ℂ) * s ^ (3 : ℕ) + (-3345 / 8 : ℂ) * s ^ (4 : ℕ) + (-3663 / 4 : ℂ) * s ^ (5 : ℕ) + (-513 / 2 : ℂ) * s ^ (6 : ℕ) + (-75 / 4 : ℂ) * s ^ (7 : ℕ) + (5 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((4500 : ℂ) + (4044 : ℂ) * s + (-223 : ℂ) * s ^ (2 : ℕ) + (-966 : ℂ) * s ^ (3 : ℕ) + (-271 / 2 : ℂ) * s ^ (4 : ℕ) + (69 : ℂ) * s ^ (5 : ℕ) + (31 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-1512 : ℂ) + (-1476 : ℂ) * s + (-243 : ℂ) * s ^ (2 : ℕ) + (96 : ℂ) * s ^ (3 : ℕ) + (23 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((180 : ℂ) + (180 : ℂ) * s + (40 : ℂ) * s ^ (2 : ℕ)))))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qt0_lauR_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt1_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt1_lauR s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-2160 : ℂ) * s ^ (2 : ℕ) + (-15921 / 2 : ℂ) * s ^ (3 : ℕ) + (-46941 / 4 : ℂ) * s ^ (4 : ℕ) + (-17703 / 2 : ℂ) * s ^ (5 : ℕ) + (-3582 : ℂ) * s ^ (6 : ℕ) + (-1395 / 2 : ℂ) * s ^ (7 : ℕ) + (-81 / 4 : ℂ) * s ^ (8 : ℕ) + (27 / 2 : ℂ) * s ^ (9 : ℕ) + (3 / 2 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-2880 : ℂ) * s + (-1794 : ℂ) * s ^ (2 : ℕ) + (12508 : ℂ) * s ^ (3 : ℕ) + (94667 / 4 : ℂ) * s ^ (4 : ℕ) + (70915 / 4 : ℂ) * s ^ (5 : ℕ) + (6551 : ℂ) * s ^ (6 : ℕ) + (2201 / 2 : ℂ) * s ^ (7 : ℕ) + (71 / 4 : ℂ) * s ^ (8 : ℕ) + (-69 / 4 : ℂ) * s ^ (9 : ℕ) + (-3 / 2 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((5040 : ℂ) * s + (8838 : ℂ) * s ^ (2 : ℕ) + (-7117 / 2 : ℂ) * s ^ (3 : ℕ) + (-15270 : ℂ) * s ^ (4 : ℕ) + (-45657 / 4 : ℂ) * s ^ (5 : ℕ) + (-3634 : ℂ) * s ^ (6 : ℕ) + (-457 : ℂ) * s ^ (7 : ℕ) + (4 : ℂ) * s ^ (8 : ℕ) + (15 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-2448 : ℂ) * s + (-6396 : ℂ) * s ^ (2 : ℕ) + (-1923 : ℂ) * s ^ (3 : ℕ) + (6867 / 2 : ℂ) * s ^ (4 : ℕ) + (2713 : ℂ) * s ^ (5 : ℕ) + (696 : ℂ) * s ^ (6 : ℕ) + (54 : ℂ) * s ^ (7 : ℕ) + (-3 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((288 : ℂ) * s + (1656 : ℂ) * s ^ (2 : ℕ) + (1042 : ℂ) * s ^ (3 : ℕ) + (-75 : ℂ) * s ^ (4 : ℕ) + (-176 : ℂ) * s ^ (5 : ℕ) + (-31 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-144 : ℂ) * s ^ (2 : ℕ) + (-108 : ℂ) * s ^ (3 : ℕ) + (-20 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qt1_lauR_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt2_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt2_lauR s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((1080 : ℂ) * s ^ (2 : ℕ) + (4122 : ℂ) * s ^ (3 : ℕ) + (6411 : ℂ) * s ^ (4 : ℕ) + (5274 : ℂ) * s ^ (5 : ℕ) + (2490 : ℂ) * s ^ (6 : ℕ) + (678 : ℂ) * s ^ (7 : ℕ) + (99 : ℂ) * s ^ (8 : ℕ) + (6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((864 : ℂ) * s + (-711 : ℂ) * s ^ (2 : ℕ) + (-17679 / 2 : ℂ) * s ^ (3 : ℕ) + (-15257 : ℂ) * s ^ (4 : ℕ) + (-12023 : ℂ) * s ^ (5 : ℕ) + (-5065 : ℂ) * s ^ (6 : ℕ) + (-2327 / 2 : ℂ) * s ^ (7 : ℕ) + (-135 : ℂ) * s ^ (8 : ℕ) + (-6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-2412 : ℂ) * s + (-2949 : ℂ) * s ^ (2 : ℕ) + (4886 : ℂ) * s ^ (3 : ℕ) + (11488 : ℂ) * s ^ (4 : ℕ) + (8586 : ℂ) * s ^ (5 : ℕ) + (3065 : ℂ) * s ^ (6 : ℕ) + (532 : ℂ) * s ^ (7 : ℕ) + (36 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((1728 : ℂ) * s + (3285 : ℂ) * s ^ (2 : ℕ) + (411 / 2 : ℂ) * s ^ (3 : ℕ) + (-2736 : ℂ) * s ^ (4 : ℕ) + (-1931 : ℂ) * s ^ (5 : ℕ) + (-505 : ℂ) * s ^ (6 : ℕ) + (-93 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-180 : ℂ) * s + (-759 : ℂ) * s ^ (2 : ℕ) + (-410 : ℂ) * s ^ (3 : ℕ) + (88 : ℂ) * s ^ (4 : ℕ) + (94 : ℂ) * s ^ (5 : ℕ) + (15 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((54 : ℂ) * s ^ (2 : ℕ) + (36 : ℂ) * s ^ (3 : ℕ) + (6 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qt2_lauR_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT0_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT0_lauR s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((252 : ℂ) * s ^ (2 : ℕ) + (2217 / 4 : ℂ) * s ^ (3 : ℕ) + (579 / 2 : ℂ) * s ^ (4 : ℕ) + (-201 / 2 : ℂ) * s ^ (5 : ℕ) + (-115 : ℂ) * s ^ (6 : ℕ) + (-119 / 4 : ℂ) * s ^ (7 : ℕ) + (-5 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-528 : ℂ) * s + (-4685 / 2 : ℂ) * s ^ (2 : ℕ) + (-2111 / 2 : ℂ) * s ^ (3 : ℕ) + (609 : ℂ) * s ^ (4 : ℕ) + (717 : ℂ) * s ^ (5 : ℕ) + (529 / 2 : ℂ) * s ^ (6 : ℕ) + (89 / 2 : ℂ) * s ^ (7 : ℕ) + (3 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((2862 : ℂ) * s + (3225 : ℂ) * s ^ (2 : ℕ) + (4521 / 4 : ℂ) * s ^ (3 : ℕ) + (105 / 2 : ℂ) * s ^ (4 : ℕ) + (-243 / 2 : ℂ) * s ^ (5 : ℕ) + (-45 : ℂ) * s ^ (6 : ℕ) + (-27 / 4 : ℂ) * s ^ (7 : ℕ) + (-1 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-3252 : ℂ) * s + (-6265 / 2 : ℂ) * s ^ (2 : ℕ) + (-959 : ℂ) * s ^ (3 : ℕ) + (-133 : ℂ) * s ^ (4 : ℕ) + (9 : ℂ) * s ^ (5 : ℕ) + (7 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((1038 : ℂ) * s + (818 : ℂ) * s ^ (2 : ℕ) + (138 : ℂ) * s ^ (3 : ℕ) + (14 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-120 : ℂ) * s + (-80 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qT0_lauR_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT1_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT1_lauR s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-2880 : ℂ) * s + (-11670 : ℂ) * s ^ (2 : ℕ) + (-19113 : ℂ) * s ^ (3 : ℕ) + (-16245 : ℂ) * s ^ (4 : ℕ) + (-7669 : ℂ) * s ^ (5 : ℕ) + (-1999 : ℂ) * s ^ (6 : ℕ) + (-266 : ℂ) * s ^ (7 : ℕ) + (-14 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((14448 : ℂ) * s + (44558 : ℂ) * s ^ (2 : ℕ) + (52998 : ℂ) * s ^ (3 : ℕ) + (30939 : ℂ) * s ^ (4 : ℕ) + (9333 : ℂ) * s ^ (5 : ℕ) + (1345 : ℂ) * s ^ (6 : ℕ) + (61 : ℂ) * s ^ (7 : ℕ) + (-2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-25752 : ℂ) * s + (-55642 : ℂ) * s ^ (2 : ℕ) + (-44245 : ℂ) * s ^ (3 : ℕ) + (-16810 : ℂ) * s ^ (4 : ℕ) + (-3036 : ℂ) * s ^ (5 : ℕ) + (-184 : ℂ) * s ^ (6 : ℕ) + (5 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((19632 : ℂ) * s + (26606 : ℂ) * s ^ (2 : ℕ) + (13864 : ℂ) * s ^ (3 : ℕ) + (3336 : ℂ) * s ^ (4 : ℕ) + (308 : ℂ) * s ^ (5 : ℕ) + (-2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-6072 : ℂ) * s + (-5180 : ℂ) * s ^ (2 : ℕ) + (-1440 : ℂ) * s ^ (3 : ℕ) + (-156 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((624 : ℂ) * s + (320 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qT1_lauR_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT2_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT2_lauR s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((6720 : ℂ) * s + (25418 : ℂ) * s ^ (2 : ℕ) + (39067 : ℂ) * s ^ (3 : ℕ) + (31645 : ℂ) * s ^ (4 : ℕ) + (14647 : ℂ) * s ^ (5 : ℕ) + (3889 : ℂ) * s ^ (6 : ℕ) + (550 : ℂ) * s ^ (7 : ℕ) + (32 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-26784 : ℂ) * s + (-85210 : ℂ) * s ^ (2 : ℕ) + (-106794 : ℂ) * s ^ (3 : ℕ) + (-67552 : ℂ) * s ^ (4 : ℕ) + (-22848 : ℂ) * s ^ (5 : ℕ) + (-3934 : ℂ) * s ^ (6 : ℕ) + (-270 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((40404 : ℂ) * s + (102352 : ℂ) * s ^ (2 : ℕ) + (94427 : ℂ) * s ^ (3 : ℕ) + (41515 : ℂ) * s ^ (4 : ℕ) + (8829 : ℂ) * s ^ (5 : ℕ) + (729 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-28128 : ℂ) * s + (-48892 : ℂ) * s ^ (2 : ℕ) + (-29484 : ℂ) * s ^ (3 : ℕ) + (-7684 : ℂ) * s ^ (4 : ℕ) + (-756 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((8580 : ℂ) * s + (7904 : ℂ) * s ^ (2 : ℕ) + (2472 : ℂ) * s ^ (3 : ℕ) + (260 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-792 : ℂ) * s + (-312 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qT2_lauR_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT3_lauR (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT3_lauR s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((-2880 : ℂ) * s + (-10992 : ℂ) * s ^ (2 : ℕ) + (-17096 : ℂ) * s ^ (3 : ℕ) + (-14064 : ℂ) * s ^ (4 : ℕ) + (-6640 : ℂ) * s ^ (5 : ℕ) + (-1808 : ℂ) * s ^ (6 : ℕ) + (-264 : ℂ) * s ^ (7 : ℕ) + (-16 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((11304 : ℂ) * s + (38292 : ℂ) * s ^ (2 : ℕ) + (51408 : ℂ) * s ^ (3 : ℕ) + (34984 : ℂ) * s ^ (4 : ℕ) + (12760 : ℂ) * s ^ (5 : ℕ) + (2372 : ℂ) * s ^ (6 : ℕ) + (176 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-16920 : ℂ) * s + (-48492 : ℂ) * s ^ (2 : ℕ) + (-51688 : ℂ) * s ^ (3 : ℕ) + (-25488 : ℂ) * s ^ (4 : ℕ) + (-5888 : ℂ) * s ^ (5 : ℕ) + (-516 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((11736 : ℂ) * s + (25728 : ℂ) * s ^ (2 : ℕ) + (16992 : ℂ) * s ^ (3 : ℕ) + (4608 : ℂ) * s ^ (4 : ℕ) + (456 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-3528 : ℂ) * s + (-3624 : ℂ) * s ^ (2 : ℕ) + (-1176 : ℂ) * s ^ (3 : ℕ) + (-120 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((288 : ℂ) * s + (96 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qT3_lauR_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewSrcFLam_lauR (s r : ℂ) : ℂ := (((960 : ℂ) * s + (4088 : ℂ) * s ^ (2 : ℕ) + (29435 / 4 : ℂ) * s ^ (3 : ℕ) + (115453 / 16 : ℂ) * s ^ (4 : ℕ) + (65057 / 16 : ℂ) * s ^ (5 : ℕ) + (1233 : ℂ) * s ^ (6 : ℕ) + (1125 / 8 : ℂ) * s ^ (7 : ℕ) + (-263 / 16 : ℂ) * s ^ (8 : ℕ) + (-87 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-5592 : ℂ) * s + (-35463 / 2 : ℂ) * s ^ (2 : ℕ) + (-35881 / 2 : ℂ) * s ^ (3 : ℕ) + (-46491 / 4 : ℂ) * s ^ (4 : ℕ) + (-42659 / 8 : ℂ) * s ^ (5 : ℕ) + (-2997 / 2 : ℂ) * s ^ (6 : ℕ) + (-186 : ℂ) * s ^ (7 : ℕ) + (15 : ℂ) * s ^ (8 : ℕ) + (63 / 8 : ℂ) * s ^ (9 : ℕ) + (3 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((2970 : ℂ) * s + (10731 : ℂ) * s ^ (2 : ℕ) + (33831 / 4 : ℂ) * s ^ (3 : ℕ) + (60361 / 16 : ℂ) * s ^ (4 : ℕ) + (18121 / 16 : ℂ) * s ^ (5 : ℕ) + (519 / 2 : ℂ) * s ^ (6 : ℕ) + (425 / 8 : ℂ) * s ^ (7 : ℕ) + (37 / 16 : ℂ) * s ^ (8 : ℕ) + (-39 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-3168 : ℂ) + (-1248 : ℂ) * s + (5695 / 2 : ℂ) * s ^ (2 : ℕ) + (2410 : ℂ) * s ^ (3 : ℕ) + (5391 / 8 : ℂ) * s ^ (4 : ℕ) + (539 / 4 : ℂ) * s ^ (5 : ℕ) + (13 / 2 : ℂ) * s ^ (6 : ℕ) + (-31 / 4 : ℂ) * s ^ (7 : ℕ) + (-7 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((4500 : ℂ) + (4206 : ℂ) * s + (226 : ℂ) * s ^ (2 : ℕ) + (-328 : ℂ) * s ^ (3 : ℕ) + (-85 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-1512 : ℂ) + (-1476 : ℂ) * s + (-201 : ℂ) * s ^ (2 : ℕ) + (42 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((180 : ℂ) + (180 : ℂ) * s + (40 : ℂ) * s ^ (2 : ℕ)))))))))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ))

theorem skewSrcF_lauR_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewSrcF_lauR s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = skewSrcFLam_lauR s r := by
  unfold skewSrcF_lauR
  rw [skewPieceSF_qtr0_lauR s r hr hf hs hs3 hs1, skewPieceSF_qtr1_lauR s r hr hf hs hs3 hs1, skewPieceSF_qtr2_lauR s r hr hf hs hs3 hs1, skewPieceSF_qt0_lauR s r hr hf hs hs3 hs1, skewPieceSF_qt1_lauR s r hr hf hs hs3 hs1, skewPieceSF_qt2_lauR s r hr hf hs hs3 hs1, skewPieceSF_qT0_lauR s r hr hf hs hs3 hs1, skewPieceSF_qT1_lauR s r hr hf hs hs3 hs1, skewPieceSF_qT2_lauR s r hr hf hs hs3 hs1, skewPieceSF_qT3_lauR s r hr hf hs hs3 hs1]
  unfold skewSrcFLam_lauR
  simp only [← add_div]
  ring

theorem skewPieceSF_qtr0_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr0_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-216 : ℂ) * s ^ (2 : ℕ) + (-4131 / 4 : ℂ) * s ^ (3 : ℕ) + (-16269 / 8 : ℂ) * s ^ (4 : ℕ) + (-17043 / 8 : ℂ) * s ^ (5 : ℕ) + (-10233 / 8 : ℂ) * s ^ (6 : ℕ) + (-3519 / 8 : ℂ) * s ^ (7 : ℕ) + (-321 / 4 : ℂ) * s ^ (8 : ℕ) + (-6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((288 : ℂ) * s + (2430 : ℂ) * s ^ (2 : ℕ) + (5572 : ℂ) * s ^ (3 : ℕ) + (5822 : ℂ) * s ^ (4 : ℕ) + (13309 / 4 : ℂ) * s ^ (5 : ℕ) + (4395 / 4 : ℂ) * s ^ (6 : ℕ) + (795 / 4 : ℂ) * s ^ (7 : ℕ) + (61 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-1884 : ℂ) * s + (-5968 : ℂ) * s ^ (2 : ℕ) + (-19009 / 4 : ℂ) * s ^ (3 : ℕ) + (-18447 / 8 : ℂ) * s ^ (4 : ℕ) + (-5019 / 8 : ℂ) * s ^ (5 : ℕ) + (-429 / 8 : ℂ) * s ^ (6 : ℕ) + (25 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((3048 : ℂ) * s + (1121 : ℂ) * s ^ (2 : ℕ) + (-575 / 2 : ℂ) * s ^ (3 : ℕ) + (-238 : ℂ) * s ^ (4 : ℕ) + (-159 / 2 : ℂ) * s ^ (5 : ℕ) + (-12 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((108 : ℂ) * s + (309 : ℂ) * s ^ (2 : ℕ) + (389 / 2 : ℂ) * s ^ (3 : ℕ) + (213 / 2 : ℂ) * s ^ (4 : ℕ) + (24 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-216 : ℂ) * s + (-36 : ℂ) * s ^ (2 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewQF_qtr0_lauI1_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr1_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr1_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((1350 : ℂ) * s ^ (2 : ℕ) + (21195 / 4 : ℂ) * s ^ (3 : ℕ) + (68433 / 8 : ℂ) * s ^ (4 : ℕ) + (59127 / 8 : ℂ) * s ^ (5 : ℕ) + (29733 / 8 : ℂ) * s ^ (6 : ℕ) + (8763 / 8 : ℂ) * s ^ (7 : ℕ) + (705 / 4 : ℂ) * s ^ (8 : ℕ) + (12 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-1080 : ℂ) * s + (-8037 : ℂ) * s ^ (2 : ℕ) + (-35355 / 2 : ℂ) * s ^ (3 : ℕ) + (-19942 : ℂ) * s ^ (4 : ℕ) + (-51985 / 4 : ℂ) * s ^ (5 : ℕ) + (-19555 / 4 : ℂ) * s ^ (6 : ℕ) + (-3937 / 4 : ℂ) * s ^ (7 : ℕ) + (-329 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((3312 : ℂ) * s + (13851 : ℂ) * s ^ (2 : ℕ) + (65239 / 4 : ℂ) * s ^ (3 : ℕ) + (89531 / 8 : ℂ) * s ^ (4 : ℕ) + (39391 / 8 : ℂ) * s ^ (5 : ℕ) + (9609 / 8 : ℂ) * s ^ (6 : ℕ) + (951 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-4248 : ℂ) * s + (-5841 : ℂ) * s ^ (2 : ℕ) + (-4093 / 2 : ℂ) * s ^ (3 : ℕ) + (-261 : ℂ) * s ^ (4 : ℕ) + (67 / 2 : ℂ) * s ^ (5 : ℕ) + (19 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((912 : ℂ) * s + (-719 : ℂ) * s ^ (2 : ℕ) + (-1405 / 2 : ℂ) * s ^ (3 : ℕ) + (-721 / 2 : ℂ) * s ^ (4 : ℕ) + (-80 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((432 : ℂ) * s + (72 : ℂ) * s ^ (2 : ℕ) + (-24 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewQF_qtr1_lauI1_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr2_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr2_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((-810 : ℂ) * s ^ (2 : ℕ) + (-3159 : ℂ) * s ^ (3 : ℕ) + (-5049 : ℂ) * s ^ (4 : ℕ) + (-4296 : ℂ) * s ^ (5 : ℕ) + (-2112 : ℂ) * s ^ (6 : ℕ) + (-603 : ℂ) * s ^ (7 : ℕ) + (-93 : ℂ) * s ^ (8 : ℕ) + (-6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((432 : ℂ) * s + (4275 : ℂ) * s ^ (2 : ℕ) + (22107 / 2 : ℂ) * s ^ (3 : ℕ) + (13802 : ℂ) * s ^ (4 : ℕ) + (9557 : ℂ) * s ^ (5 : ℕ) + (3731 : ℂ) * s ^ (6 : ℕ) + (1531 / 2 : ℂ) * s ^ (7 : ℕ) + (64 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-1368 : ℂ) * s + (-7593 : ℂ) * s ^ (2 : ℕ) + (-25173 / 2 : ℂ) * s ^ (3 : ℕ) + (-10688 : ℂ) * s ^ (4 : ℕ) + (-5379 : ℂ) * s ^ (5 : ℕ) + (-1447 : ℂ) * s ^ (6 : ℕ) + (-309 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((1488 : ℂ) * s + (5464 : ℂ) * s ^ (2 : ℕ) + (3288 : ℂ) * s ^ (3 : ℕ) + (1126 : ℂ) * s ^ (4 : ℕ) + (272 : ℂ) * s ^ (5 : ℕ) + (26 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-1008 : ℂ) * s + (384 : ℂ) * s ^ (2 : ℕ) + (528 : ℂ) * s ^ (3 : ℕ) + (276 : ℂ) * s ^ (4 : ℕ) + (60 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-216 : ℂ) * s + (-36 : ℂ) * s ^ (2 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewQF_qtr2_lauI1_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt0_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt0_lauI1 s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((9 / 2 : ℂ) * s ^ (3 : ℕ) + (-417 / 16 : ℂ) * s ^ (4 : ℕ) + (-861 / 8 : ℂ) * s ^ (5 : ℕ) + (-1077 / 8 : ℂ) * s ^ (6 : ℕ) + (-75 : ℂ) * s ^ (7 : ℕ) + (-309 / 16 : ℂ) * s ^ (8 : ℕ) + (-15 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-231 : ℂ) * s ^ (2 : ℕ) + (-2915 / 4 : ℂ) * s ^ (3 : ℕ) + (-2849 / 4 : ℂ) * s ^ (4 : ℕ) + (-1713 / 8 : ℂ) * s ^ (5 : ℕ) + (547 / 8 : ℂ) * s ^ (6 : ℕ) + (577 / 8 : ℂ) * s ^ (7 : ℕ) + (171 / 8 : ℂ) * s ^ (8 : ℕ) + (9 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-636 : ℂ) * s + (-611 : ℂ) * s ^ (2 : ℕ) + (517 / 2 : ℂ) * s ^ (3 : ℕ) + (9423 / 16 : ℂ) * s ^ (4 : ℕ) + (2397 / 8 : ℂ) * s ^ (5 : ℕ) + (549 / 8 : ℂ) * s ^ (6 : ℕ) + (15 / 4 : ℂ) * s ^ (7 : ℕ) + (-33 / 16 : ℂ) * s ^ (8 : ℕ) + (-3 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-648 : ℂ) + (174 : ℂ) * s + (694 : ℂ) * s ^ (2 : ℕ) + (1865 / 4 : ℂ) * s ^ (3 : ℕ) + (1399 / 8 : ℂ) * s ^ (4 : ℕ) + (225 / 8 : ℂ) * s ^ (5 : ℕ) + (-19 / 8 : ℂ) * s ^ (6 : ℕ) + (-7 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((588 : ℂ) + (460 : ℂ) * s + (175 : ℂ) * s ^ (2 : ℕ) + (13 / 2 : ℂ) * s ^ (3 : ℕ) + (-51 / 2 : ℂ) * s ^ (4 : ℕ) + (-6 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((96 : ℂ) + (14 : ℂ) * s + (-27 : ℂ) * s ^ (2 : ℕ) + (-7 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-36 : ℂ) + (-12 : ℂ) * s))))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewQF_qt0_lauI1_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt1_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt1_lauI1 s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-432 : ℂ) * s ^ (2 : ℕ) + (-2961 / 2 : ℂ) * s ^ (3 : ℕ) + (-7875 / 4 : ℂ) * s ^ (4 : ℕ) + (-5091 / 4 : ℂ) * s ^ (5 : ℕ) + (-1587 / 4 : ℂ) * s ^ (6 : ℕ) + (-153 / 4 : ℂ) * s ^ (7 : ℕ) + (15 / 2 : ℂ) * s ^ (8 : ℕ) + (3 / 2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-576 : ℂ) * s + (-408 : ℂ) * s ^ (2 : ℕ) + (1902 : ℂ) * s ^ (3 : ℕ) + (13093 / 4 : ℂ) * s ^ (4 : ℕ) + (4109 / 2 : ℂ) * s ^ (5 : ℕ) + (1129 / 2 : ℂ) * s ^ (6 : ℕ) + (41 : ℂ) * s ^ (7 : ℕ) + (-39 / 4 : ℂ) * s ^ (8 : ℕ) + (-3 / 2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((744 : ℂ) * s + (1400 : ℂ) * s ^ (2 : ℕ) + (-165 / 2 : ℂ) * s ^ (3 : ℕ) + (-1285 : ℂ) * s ^ (4 : ℕ) + (-3225 / 4 : ℂ) * s ^ (5 : ℕ) + (-705 / 4 : ℂ) * s ^ (6 : ℕ) + (-17 / 4 : ℂ) * s ^ (7 : ℕ) + (9 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-96 : ℂ) * s + (-566 : ℂ) * s ^ (2 : ℕ) + (-439 : ℂ) * s ^ (3 : ℕ) + (-213 / 2 : ℂ) * s ^ (4 : ℕ) + (11 / 2 : ℂ) * s ^ (5 : ℕ) + (17 / 2 : ℂ) * s ^ (6 : ℕ) + (3 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-72 : ℂ) * s + (-30 : ℂ) * s ^ (2 : ℕ) + (88 : ℂ) * s ^ (3 : ℕ) + (87 : ℂ) * s ^ (4 : ℕ) + (19 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((36 : ℂ) * s ^ (2 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewQF_qt1_lauI1_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt2_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt2_lauI1 s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((270 : ℂ) * s ^ (2 : ℕ) + (963 : ℂ) * s ^ (3 : ℕ) + (1362 : ℂ) * s ^ (4 : ℕ) + (978 : ℂ) * s ^ (5 : ℕ) + (378 : ℂ) * s ^ (6 : ℕ) + (75 : ℂ) * s ^ (7 : ℕ) + (6 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((216 : ℂ) * s + (-153 : ℂ) * s ^ (2 : ℕ) + (-3789 / 2 : ℂ) * s ^ (3 : ℕ) + (-5911 / 2 : ℂ) * s ^ (4 : ℕ) + (-3993 / 2 : ℂ) * s ^ (5 : ℕ) + (-1331 / 2 : ℂ) * s ^ (6 : ℕ) + (-105 : ℂ) * s ^ (7 : ℕ) + (-6 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-540 : ℂ) * s + (-663 : ℂ) * s ^ (2 : ℕ) + (796 : ℂ) * s ^ (3 : ℕ) + (1786 : ℂ) * s ^ (4 : ℕ) + (1122 : ℂ) * s ^ (5 : ℕ) + (301 : ℂ) * s ^ (6 : ℕ) + (30 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((264 : ℂ) * s + (583 : ℂ) * s ^ (2 : ℕ) + (477 / 2 : ℂ) * s ^ (3 : ℕ) + (-239 / 2 : ℂ) * s ^ (4 : ℕ) + (-177 / 2 : ℂ) * s ^ (5 : ℕ) + (-27 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((60 : ℂ) * s + (-19 : ℂ) * s ^ (2 : ℕ) + (-97 : ℂ) * s ^ (3 : ℕ) + (-73 : ℂ) * s ^ (4 : ℕ) + (-15 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-18 : ℂ) * s ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewQF_qt2_lauI1_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT0_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT0_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((-5 : ℂ) * s ^ (2 : ℕ) + (-113 / 4 : ℂ) * s ^ (3 : ℕ) + (-219 / 4 : ℂ) * s ^ (4 : ℕ) + (-189 / 4 : ℂ) * s ^ (5 : ℕ) + (-73 / 4 : ℂ) * s ^ (6 : ℕ) + (-5 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-108 : ℂ) * s + (-221 / 2 : ℂ) * s ^ (2 : ℕ) + (210 : ℂ) * s ^ (3 : ℕ) + (308 : ℂ) * s ^ (4 : ℕ) + (130 : ℂ) * s ^ (5 : ℕ) + (55 / 2 : ℂ) * s ^ (6 : ℕ) + (3 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((530 : ℂ) * s + (-88 : ℂ) * s ^ (2 : ℕ) + (-277 / 4 : ℂ) * s ^ (3 : ℕ) + (-11 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (5 : ℕ) + (-5 / 4 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-376 : ℂ) * s + (-397 / 2 : ℂ) * s ^ (2 : ℕ) + (-65 / 2 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-70 : ℂ) * s + (-18 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((24 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewQF_qT0_lauI1_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT1_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT1_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-576 : ℂ) * s + (-2078 : ℂ) * s ^ (2 : ℕ) + (-2991 : ℂ) * s ^ (3 : ℕ) + (-2202 : ℂ) * s ^ (4 : ℕ) + (-877 : ℂ) * s ^ (5 : ℕ) + (-178 : ℂ) * s ^ (6 : ℕ) + (-14 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((2616 : ℂ) * s + (6698 : ℂ) * s ^ (2 : ℕ) + (6292 : ℂ) * s ^ (3 : ℕ) + (2673 : ℂ) * s ^ (4 : ℕ) + (488 : ℂ) * s ^ (5 : ℕ) + (23 : ℂ) * s ^ (6 : ℕ) + (-2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-3832 : ℂ) * s + (-5654 : ℂ) * s ^ (2 : ℕ) + (-2483 : ℂ) * s ^ (3 : ℕ) + (-353 : ℂ) * s ^ (4 : ℕ) + (3 : ℂ) * s ^ (5 : ℕ) + (3 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((1752 : ℂ) * s + (422 : ℂ) * s ^ (2 : ℕ) + (-86 : ℂ) * s ^ (3 : ℕ) + (-30 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((184 : ℂ) * s + (276 : ℂ) * s ^ (2 : ℕ) + (68 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-144 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewQF_qT1_lauI1_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT2_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT2_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((1440 : ℂ) * s + (5086 : ℂ) * s ^ (2 : ℕ) + (7119 : ℂ) * s ^ (3 : ℕ) + (5066 : ℂ) * s ^ (4 : ℕ) + (1951 : ℂ) * s ^ (5 : ℕ) + (390 : ℂ) * s ^ (6 : ℕ) + (32 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-5168 : ℂ) * s + (-14910 : ℂ) * s ^ (2 : ℕ) + (-16288 : ℂ) * s ^ (3 : ℕ) + (-8448 : ℂ) * s ^ (4 : ℕ) + (-2108 : ℂ) * s ^ (5 : ℕ) + (-206 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((6508 : ℂ) * s + (13940 : ℂ) * s ^ (2 : ℕ) + (9677 : ℂ) * s ^ (3 : ℕ) + (2810 : ℂ) * s ^ (4 : ℕ) + (289 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-3056 : ℂ) * s + (-3012 : ℂ) * s ^ (2 : ℕ) + (-572 : ℂ) * s ^ (3 : ℕ) + (48 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((60 : ℂ) * s + (-684 : ℂ) * s ^ (2 : ℕ) + (-180 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((216 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewQF_qT2_lauI1_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT3_lauI1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT3_lauI1 s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((-720 : ℂ) * s + (-2568 : ℂ) * s ^ (2 : ℕ) + (-3632 : ℂ) * s ^ (3 : ℕ) + (-2608 : ℂ) * s ^ (4 : ℕ) + (-1008 : ℂ) * s ^ (5 : ℕ) + (-200 : ℂ) * s ^ (6 : ℕ) + (-16 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((2616 : ℂ) * s + (8180 : ℂ) * s ^ (2 : ℕ) + (9780 : ℂ) * s ^ (3 : ℕ) + (5580 : ℂ) * s ^ (4 : ℕ) + (1524 : ℂ) * s ^ (5 : ℕ) + (160 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-3432 : ℂ) * s + (-8804 : ℂ) * s ^ (2 : ℕ) + (-7836 : ℂ) * s ^ (3 : ℕ) + (-2812 : ℂ) * s ^ (4 : ℕ) + (-348 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((1800 : ℂ) * s + (3096 : ℂ) * s ^ (2 : ℕ) + (936 : ℂ) * s ^ (3 : ℕ) + (24 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-168 : ℂ) * s + (432 : ℂ) * s ^ (2 : ℕ) + (120 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-96 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [skewQF_qT3_lauI1_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewSrcFLam_lauI1 (s r : ℂ) : ℂ := (((144 : ℂ) * s + (597 : ℂ) * s ^ (2 : ℕ) + (4247 / 4 : ℂ) * s ^ (3 : ℕ) + (16639 / 16 : ℂ) * s ^ (4 : ℕ) + (4647 / 8 : ℂ) * s ^ (5 : ℕ) + (1327 / 8 : ℂ) * s ^ (6 : ℕ) + (55 / 4 : ℂ) * s ^ (7 : ℕ) + (-45 / 16 : ℂ) * s ^ (8 : ℕ) + (-3 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-764 : ℂ) * s + (-4533 / 2 : ℂ) * s ^ (2 : ℕ) + (-7117 / 4 : ℂ) * s ^ (3 : ℕ) + (-1199 / 2 : ℂ) * s ^ (4 : ℕ) + (-1873 / 8 : ℂ) * s ^ (5 : ℕ) + (-697 / 8 : ℂ) * s ^ (6 : ℕ) + (-87 / 8 : ℂ) * s ^ (7 : ℕ) + (21 / 8 : ℂ) * s ^ (8 : ℕ) + (3 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-598 : ℂ) * s + (-190 : ℂ) * s ^ (2 : ℕ) + (-3073 / 4 : ℂ) * s ^ (3 : ℕ) + (-17125 / 16 : ℂ) * s ^ (4 : ℕ) + (-4187 / 8 : ℂ) * s ^ (5 : ℕ) + (-835 / 8 : ℂ) * s ^ (6 : ℕ) + (-7 / 2 : ℂ) * s ^ (7 : ℕ) + (3 / 16 : ℂ) * s ^ (8 : ℕ) + (-3 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-648 : ℂ) + (750 : ℂ) * s + (3525 / 2 : ℂ) * s ^ (2 : ℕ) + (5861 / 4 : ℂ) * s ^ (3 : ℕ) + (4955 / 8 : ℂ) * s ^ (4 : ℕ) + (1397 / 8 : ℂ) * s ^ (5 : ℕ) + (205 / 8 : ℂ) * s ^ (6 : ℕ) + (5 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((588 : ℂ) + (466 : ℂ) * s + (106 : ℂ) * s ^ (2 : ℕ) + (43 / 2 : ℂ) * s ^ (3 : ℕ) + (21 / 2 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((96 : ℂ) + (14 : ℂ) * s + (-9 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-36 : ℂ) + (-12 : ℂ) * s))))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ))

theorem skewSrcF_lauI1_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewSrcF_lauI1 s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = skewSrcFLam_lauI1 s r := by
  unfold skewSrcF_lauI1
  rw [skewPieceSF_qtr0_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qtr1_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qtr2_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qt0_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qt1_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qt2_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qT0_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qT1_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qT2_lauI1 s r hr hf hs hs3 hs1, skewPieceSF_qT3_lauI1 s r hr hf hs hs3 hs1]
  unfold skewSrcFLam_lauI1
  simp only [← add_div]
  ring

theorem skewPieceSF_qtr0_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr0_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-324 : ℂ) * s ^ (2 : ℕ) + (-6129 / 4 : ℂ) * s ^ (3 : ℕ) + (-25533 / 8 : ℂ) * s ^ (4 : ℕ) + (-15435 / 4 : ℂ) * s ^ (5 : ℕ) + (-11871 / 4 : ℂ) * s ^ (6 : ℕ) + (-5907 / 4 : ℂ) * s ^ (7 : ℕ) + (-3669 / 8 : ℂ) * s ^ (8 : ℕ) + (-321 / 4 : ℂ) * s ^ (9 : ℕ) + (-6 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((432 : ℂ) * s + (3339 : ℂ) * s ^ (2 : ℕ) + (15153 / 2 : ℂ) * s ^ (3 : ℕ) + (8259 : ℂ) * s ^ (4 : ℕ) + (18327 / 4 : ℂ) * s ^ (5 : ℕ) + (2303 / 2 : ℂ) * s ^ (6 : ℕ) + (97 / 2 : ℂ) * s ^ (7 : ℕ) + (-51 / 2 : ℂ) * s ^ (8 : ℕ) + (-11 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-2448 : ℂ) * s + (-6042 : ℂ) * s ^ (2 : ℕ) + (-7523 / 4 : ℂ) * s ^ (3 : ℕ) + (26225 / 8 : ℂ) * s ^ (4 : ℕ) + (3552 : ℂ) * s ^ (5 : ℕ) + (7127 / 4 : ℂ) * s ^ (6 : ℕ) + (1903 / 4 : ℂ) * s ^ (7 : ℕ) + (409 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((1836 : ℂ) * s + (-5796 : ℂ) * s ^ (2 : ℕ) + (-8412 : ℂ) * s ^ (3 : ℕ) + (-10217 / 2 : ℂ) * s ^ (4 : ℕ) + (-3085 / 2 : ℂ) * s ^ (5 : ℕ) + (-403 / 2 : ℂ) * s ^ (6 : ℕ) + (-15 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((5184 : ℂ) * s + (3357 : ℂ) * s ^ (2 : ℕ) + (1941 / 2 : ℂ) * s ^ (3 : ℕ) + (516 : ℂ) * s ^ (4 : ℕ) + (321 / 2 : ℂ) * s ^ (5 : ℕ) + (12 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-972 : ℂ) * s + (-270 : ℂ) * s ^ (2 : ℕ) + (36 : ℂ) * s ^ (3 : ℕ) + (6 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qtr0_lauI3_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr1_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr1_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((2160 : ℂ) * s ^ (2 : ℕ) + (38421 / 4 : ℂ) * s ^ (3 : ℕ) + (145257 / 8 : ℂ) * s ^ (4 : ℕ) + (76587 / 4 : ℂ) * s ^ (5 : ℕ) + (49587 / 4 : ℂ) * s ^ (6 : ℕ) + (20319 / 4 : ℂ) * s ^ (7 : ℕ) + (10353 / 8 : ℂ) * s ^ (8 : ℕ) + (753 / 4 : ℂ) * s ^ (9 : ℕ) + (12 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-1728 : ℂ) * s + (-11952 : ℂ) * s ^ (2 : ℕ) + (-27825 : ℂ) * s ^ (3 : ℕ) + (-35017 : ℂ) * s ^ (4 : ℕ) + (-109301 / 4 : ℂ) * s ^ (5 : ℕ) + (-13604 : ℂ) * s ^ (6 : ℕ) + (-8431 / 2 : ℂ) * s ^ (7 : ℕ) + (-747 : ℂ) * s ^ (8 : ℕ) + (-233 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((3852 : ℂ) * s + (13869 : ℂ) * s ^ (2 : ℕ) + (51397 / 4 : ℂ) * s ^ (3 : ℕ) + (25319 / 8 : ℂ) * s ^ (4 : ℕ) + (-1602 : ℂ) * s ^ (5 : ℕ) + (-5103 / 4 : ℂ) * s ^ (6 : ℕ) + (-1369 / 4 : ℂ) * s ^ (7 : ℕ) + (-281 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-2196 : ℂ) * s + (7116 : ℂ) * s ^ (2 : ℕ) + (16737 : ℂ) * s ^ (3 : ℕ) + (15777 : ℂ) * s ^ (4 : ℕ) + (7803 : ℂ) * s ^ (5 : ℕ) + (2019 : ℂ) * s ^ (6 : ℕ) + (216 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-4860 : ℂ) * s + (-10971 : ℂ) * s ^ (2 : ℕ) + (-14325 / 2 : ℂ) * s ^ (3 : ℕ) + (-3342 : ℂ) * s ^ (4 : ℕ) + (-2049 / 2 : ℂ) * s ^ (5 : ℕ) + (-120 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((2916 : ℂ) * s + (1134 : ℂ) * s ^ (2 : ℕ) + (-54 : ℂ) * s ^ (3 : ℕ) + (-36 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qtr1_lauI3_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qtr2_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qtr2_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((-1620 : ℂ) * s ^ (2 : ℕ) + (-7128 : ℂ) * s ^ (3 : ℕ) + (-13257 : ℂ) * s ^ (4 : ℕ) + (-13641 : ℂ) * s ^ (5 : ℕ) + (-8520 : ℂ) * s ^ (6 : ℕ) + (-3318 : ℂ) * s ^ (7 : ℕ) + (-789 : ℂ) * s ^ (8 : ℕ) + (-105 : ℂ) * s ^ (9 : ℕ) + (-6 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((864 : ℂ) * s + (8037 : ℂ) * s ^ (2 : ℕ) + (45483 / 2 : ℂ) * s ^ (3 : ℕ) + (65855 / 2 : ℂ) * s ^ (4 : ℕ) + (28131 : ℂ) * s ^ (5 : ℕ) + (14718 : ℂ) * s ^ (6 : ℕ) + (9243 / 2 : ℂ) * s ^ (7 : ℕ) + (1595 / 2 : ℂ) * s ^ (8 : ℕ) + (58 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-2232 : ℂ) * s + (-11433 : ℂ) * s ^ (2 : ℕ) + (-39091 / 2 : ℂ) * s ^ (3 : ℕ) + (-35255 / 2 : ℂ) * s ^ (4 : ℕ) + (-10343 : ℂ) * s ^ (5 : ℕ) + (-4052 : ℂ) * s ^ (6 : ℕ) + (-1839 / 2 : ℂ) * s ^ (7 : ℕ) + (-175 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((1296 : ℂ) * s + (2808 : ℂ) * s ^ (2 : ℕ) + (-4176 : ℂ) * s ^ (3 : ℕ) + (-8442 : ℂ) * s ^ (4 : ℕ) + (-5358 : ℂ) * s ^ (5 : ℕ) + (-1518 : ℂ) * s ^ (6 : ℕ) + (-162 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((7560 : ℂ) * s ^ (2 : ℕ) + (7200 : ℂ) * s ^ (3 : ℕ) + (3900 : ℂ) * s ^ (4 : ℕ) + (1320 : ℂ) * s ^ (5 : ℕ) + (180 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-1944 : ℂ) * s + (-972 : ℂ) * s ^ (2 : ℕ) + (36 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qtr2_lauI3_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt0_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt0_lauI3 s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((-72 : ℂ) * s ^ (3 : ℕ) + (-4839 / 16 : ℂ) * s ^ (4 : ℕ) + (-8559 / 16 : ℂ) * s ^ (5 : ℕ) + (-522 : ℂ) * s ^ (6 : ℕ) + (-2457 / 8 : ℂ) * s ^ (7 : ℕ) + (-1755 / 16 : ℂ) * s ^ (8 : ℕ) + (-351 / 16 : ℂ) * s ^ (9 : ℕ) + (-15 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-570 : ℂ) * s ^ (2 : ℕ) + (-1621 : ℂ) * s ^ (3 : ℕ) + (-1689 : ℂ) * s ^ (4 : ℕ) + (-5413 / 8 : ℂ) * s ^ (5 : ℕ) + (149 / 2 : ℂ) * s ^ (6 : ℕ) + (381 / 2 : ℂ) * s ^ (7 : ℕ) + (365 / 4 : ℂ) * s ^ (8 : ℕ) + (177 / 8 : ℂ) * s ^ (9 : ℕ) + (9 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-1200 : ℂ) * s + (-1891 : ℂ) * s ^ (2 : ℕ) + (-803 : ℂ) * s ^ (3 : ℕ) + (7617 / 16 : ℂ) * s ^ (4 : ℕ) + (11669 / 16 : ℂ) * s ^ (5 : ℕ) + (753 / 2 : ℂ) * s ^ (6 : ℕ) + (887 / 8 : ℂ) * s ^ (7 : ℕ) + (285 / 16 : ℂ) * s ^ (8 : ℕ) + (-3 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-1008 : ℂ) + (-1032 : ℂ) * s + (827 : ℂ) * s ^ (2 : ℕ) + (2021 : ℂ) * s ^ (3 : ℕ) + (11879 / 8 : ℂ) * s ^ (4 : ℕ) + (1945 / 4 : ℂ) * s ^ (5 : ℕ) + (141 / 2 : ℂ) * s ^ (6 : ℕ) + (23 / 4 : ℂ) * s ^ (7 : ℕ) + (5 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-108 : ℂ) + (1692 : ℂ) * s + (1629 : ℂ) * s ^ (2 : ℕ) + (483 : ℂ) * s ^ (3 : ℕ) + (55 / 2 : ℂ) * s ^ (4 : ℕ) + (-4 : ℂ) * s ^ (5 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((1224 : ℂ) + (576 : ℂ) * s + (5 : ℂ) * s ^ (2 : ℕ) + (-8 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-108 : ℂ) + (-36 : ℂ) * s))))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qt0_lauI3_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt1_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt1_lauI3 s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-648 : ℂ) * s ^ (2 : ℕ) + (-5085 / 2 : ℂ) * s ^ (3 : ℕ) + (-16233 / 4 : ℂ) * s ^ (4 : ℕ) + (-6765 / 2 : ℂ) * s ^ (5 : ℕ) + (-1548 : ℂ) * s ^ (6 : ℕ) + (-699 / 2 : ℂ) * s ^ (7 : ℕ) + (-45 / 4 : ℂ) * s ^ (8 : ℕ) + (21 / 2 : ℂ) * s ^ (9 : ℕ) + (3 / 2 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-864 : ℂ) * s + (-1662 : ℂ) * s ^ (2 : ℕ) + (364 : ℂ) * s ^ (3 : ℕ) + (13171 / 4 : ℂ) * s ^ (4 : ℕ) + (13619 / 4 : ℂ) * s ^ (5 : ℕ) + (1605 : ℂ) * s ^ (6 : ℕ) + (693 / 2 : ℂ) * s ^ (7 : ℕ) + (23 / 4 : ℂ) * s ^ (8 : ℕ) + (-45 / 4 : ℂ) * s ^ (9 : ℕ) + (-3 / 2 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((288 : ℂ) * s + (2058 : ℂ) * s ^ (2 : ℕ) + (7431 / 2 : ℂ) * s ^ (3 : ℕ) + (2999 : ℂ) * s ^ (4 : ℕ) + (4747 / 4 : ℂ) * s ^ (5 : ℕ) + (208 : ℂ) * s ^ (6 : ℕ) + (7 : ℂ) * s ^ (7 : ℕ) + (1 : ℂ) * s ^ (8 : ℕ) + (3 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((1008 : ℂ) * s + (1080 : ℂ) * s ^ (2 : ℕ) + (-1495 : ℂ) * s ^ (3 : ℕ) + (-5317 / 2 : ℂ) * s ^ (4 : ℕ) + (-1393 : ℂ) * s ^ (5 : ℕ) + (-286 : ℂ) * s ^ (6 : ℕ) + (-4 : ℂ) * s ^ (7 : ℕ) + (9 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-432 : ℂ) * s + (-1044 : ℂ) * s ^ (2 : ℕ) + (-150 : ℂ) * s ^ (3 : ℕ) + (413 : ℂ) * s ^ (4 : ℕ) + (184 : ℂ) * s ^ (5 : ℕ) + (21 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((216 : ℂ) * s ^ (2 : ℕ) + (108 : ℂ) * s ^ (3 : ℕ) + (12 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qt1_lauI3_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qt2_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qt2_lauI3 s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((540 : ℂ) * s ^ (2 : ℕ) + (2196 : ℂ) * s ^ (3 : ℕ) + (3687 : ℂ) * s ^ (4 : ℕ) + (3318 : ℂ) * s ^ (5 : ℕ) + (1734 : ℂ) * s ^ (6 : ℕ) + (528 : ℂ) * s ^ (7 : ℕ) + (87 : ℂ) * s ^ (8 : ℕ) + (6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((432 : ℂ) * s + (225 : ℂ) * s ^ (2 : ℕ) + (-5667 / 2 : ℂ) * s ^ (3 : ℕ) + (-6265 : ℂ) * s ^ (4 : ℕ) + (-5867 : ℂ) * s ^ (5 : ℕ) + (-2921 : ℂ) * s ^ (6 : ℕ) + (-1595 / 2 : ℂ) * s ^ (7 : ℕ) + (-111 : ℂ) * s ^ (8 : ℕ) + (-6 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-828 : ℂ) * s + (-2109 : ℂ) * s ^ (2 : ℕ) + (-1436 : ℂ) * s ^ (3 : ℕ) + (820 : ℂ) * s ^ (4 : ℕ) + (1718 : ℂ) * s ^ (5 : ℕ) + (985 : ℂ) * s ^ (6 : ℕ) + (250 : ℂ) * s ^ (7 : ℕ) + (24 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-144 : ℂ) * s + (741 : ℂ) * s ^ (2 : ℕ) + (4783 / 2 : ℂ) * s ^ (3 : ℕ) + (2496 : ℂ) * s ^ (4 : ℕ) + (1161 : ℂ) * s ^ (5 : ℕ) + (247 : ℂ) * s ^ (6 : ℕ) + (39 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((540 : ℂ) * s + (765 : ℂ) * s ^ (2 : ℕ) + (-210 : ℂ) * s ^ (3 : ℕ) + (-720 : ℂ) * s ^ (4 : ℕ) + (-330 : ℂ) * s ^ (5 : ℕ) + (-45 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-162 : ℂ) * s ^ (2 : ℕ) + (-108 : ℂ) * s ^ (3 : ℕ) + (-18 : ℂ) * s ^ (4 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qt2_lauI3_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT0_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT0_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((-82 : ℂ) * s ^ (2 : ℕ) + (-1095 / 4 : ℂ) * s ^ (3 : ℕ) + (-717 / 2 : ℂ) * s ^ (4 : ℕ) + (-481 / 2 : ℂ) * s ^ (5 : ℕ) + (-93 : ℂ) * s ^ (6 : ℕ) + (-87 / 4 : ℂ) * s ^ (7 : ℕ) + (-5 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-168 : ℂ) * s + (143 / 2 : ℂ) * s ^ (2 : ℕ) + (1365 / 2 : ℂ) * s ^ (3 : ℕ) + (927 : ℂ) * s ^ (4 : ℕ) + (571 : ℂ) * s ^ (5 : ℕ) + (345 / 2 : ℂ) * s ^ (6 : ℕ) + (57 / 2 : ℂ) * s ^ (7 : ℕ) + (3 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((654 : ℂ) * s + (3 : ℂ) * s ^ (2 : ℕ) + (-471 / 4 : ℂ) * s ^ (3 : ℕ) + (649 / 2 : ℂ) * s ^ (4 : ℕ) + (349 / 2 : ℂ) * s ^ (5 : ℕ) + (25 : ℂ) * s ^ (6 : ℕ) + (5 / 4 : ℂ) * s ^ (7 : ℕ) + (-1 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((276 : ℂ) * s + (-1909 / 2 : ℂ) * s ^ (2 : ℕ) + (-445 : ℂ) * s ^ (3 : ℕ) + (-55 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) + (7 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-834 : ℂ) * s + (-298 : ℂ) * s ^ (2 : ℕ) + (-38 : ℂ) * s ^ (3 : ℕ) + (-6 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((72 : ℂ) * s))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qT0_lauI3_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT1_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT1_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-864 : ℂ) * s + (-3406 : ℂ) * s ^ (2 : ℕ) + (-5597 : ℂ) * s ^ (3 : ℕ) + (-5045 : ℂ) * s ^ (4 : ℕ) + (-2749 : ℂ) * s ^ (5 : ℕ) + (-919 : ℂ) * s ^ (6 : ℕ) + (-174 : ℂ) * s ^ (7 : ℕ) + (-14 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((3072 : ℂ) * s + (8350 : ℂ) * s ^ (2 : ℕ) + (8582 : ℂ) * s ^ (3 : ℕ) + (4083 : ℂ) * s ^ (4 : ℕ) + (765 : ℂ) * s ^ (5 : ℕ) + (-39 : ℂ) * s ^ (6 : ℕ) + (-27 : ℂ) * s ^ (7 : ℕ) + (-2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-1752 : ℂ) * s + (-330 : ℂ) * s ^ (2 : ℕ) + (3207 : ℂ) * s ^ (3 : ℕ) + (2958 : ℂ) * s ^ (4 : ℕ) + (956 : ℂ) * s ^ (5 : ℕ) + (112 : ℂ) * s ^ (6 : ℕ) + (1 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-3648 : ℂ) * s + (-7930 : ℂ) * s ^ (2 : ℕ) + (-4736 : ℂ) * s ^ (3 : ℕ) + (-968 : ℂ) * s ^ (4 : ℕ) + (-36 : ℂ) * s ^ (5 : ℕ) + (6 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((3912 : ℂ) * s + (2404 : ℂ) * s ^ (2 : ℕ) + (608 : ℂ) * s ^ (3 : ℕ) + (36 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-720 : ℂ) * s + (-96 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qT1_lauI3_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT2_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT2_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((2400 : ℂ) * s + (9690 : ℂ) * s ^ (2 : ℕ) + (16187 : ℂ) * s ^ (3 : ℕ) + (14573 : ℂ) * s ^ (4 : ℕ) + (7703 : ℂ) * s ^ (5 : ℕ) + (2417 : ℂ) * s ^ (6 : ℕ) + (422 : ℂ) * s ^ (7 : ℕ) + (32 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-6720 : ℂ) * s + (-22442 : ℂ) * s ^ (2 : ℕ) + (-30162 : ℂ) * s ^ (3 : ℕ) + (-21008 : ℂ) * s ^ (4 : ℕ) + (-8072 : ℂ) * s ^ (5 : ℕ) + (-1646 : ℂ) * s ^ (6 : ℕ) + (-142 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((3828 : ℂ) * s + (8272 : ℂ) * s ^ (2 : ℕ) + (5243 : ℂ) * s ^ (3 : ℕ) + (859 : ℂ) * s ^ (4 : ℕ) + (-259 : ℂ) * s ^ (5 : ℕ) + (-87 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((4416 : ℂ) * s + (13108 : ℂ) * s ^ (2 : ℕ) + (11324 : ℂ) * s ^ (3 : ℕ) + (4060 : ℂ) * s ^ (4 : ℕ) + (500 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-5436 : ℂ) * s + (-7728 : ℂ) * s ^ (2 : ℕ) + (-2904 : ℂ) * s ^ (3 : ℕ) + (-300 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((1512 : ℂ) * s + (360 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qT2_lauI3_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

theorem skewPieceSF_qT3_lauI3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewQF_qT3_lauI3 s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((-1440 : ℂ) * s + (-5856 : ℂ) * s ^ (2 : ℕ) + (-9832 : ℂ) * s ^ (3 : ℕ) + (-8848 : ℂ) * s ^ (4 : ℕ) + (-4624 : ℂ) * s ^ (5 : ℕ) + (-1408 : ℂ) * s ^ (6 : ℕ) + (-232 : ℂ) * s ^ (7 : ℕ) + (-16 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((4392 : ℂ) * s + (16020 : ℂ) * s ^ (2 : ℕ) + (23632 : ℂ) * s ^ (3 : ℕ) + (18056 : ℂ) * s ^ (4 : ℕ) + (7544 : ℂ) * s ^ (5 : ℕ) + (1636 : ℂ) * s ^ (6 : ℕ) + (144 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-3672 : ℂ) * s + (-11196 : ℂ) * s ^ (2 : ℕ) + (-12936 : ℂ) * s ^ (3 : ℕ) + (-7056 : ℂ) * s ^ (4 : ℕ) + (-1824 : ℂ) * s ^ (5 : ℕ) + (-180 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-936 : ℂ) * s + (-3552 : ℂ) * s ^ (2 : ℕ) + (-5184 : ℂ) * s ^ (3 : ℕ) + (-2592 : ℂ) * s ^ (4 : ℕ) + (-408 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((2520 : ℂ) * s + (5880 : ℂ) * s ^ (2 : ℕ) + (2760 : ℂ) * s ^ (3 : ℕ) + (360 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-864 : ℂ) * s + (-288 : ℂ) * s ^ (2 : ℕ)))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ)) := by
  rw [skewQF_qT3_lauI3_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  all_goals (try ring)

def skewSrcFLam_lauI3 (s r : ℂ) : ℂ := (((96 : ℂ) * s + (454 : ℂ) * s ^ (2 : ℕ) + (4043 / 4 : ℂ) * s ^ (3 : ℕ) + (21701 / 16 : ℂ) * s ^ (4 : ℕ) + (18193 / 16 : ℂ) * s ^ (5 : ℕ) + (570 : ℂ) * s ^ (6 : ℕ) + (1205 / 8 : ℂ) * s ^ (7 : ℕ) + (193 / 16 : ℂ) * s ^ (8 : ℕ) + (-39 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-288 : ℂ) * s + (-1167 / 2 : ℂ) * s ^ (2 : ℕ) + (1137 : ℂ) * s ^ (3 : ℕ) + (14265 / 4 : ℂ) * s ^ (4 : ℕ) + (24453 / 8 : ℂ) * s ^ (5 : ℕ) + (2295 / 2 : ℂ) * s ^ (6 : ℕ) + (395 / 2 : ℂ) * s ^ (7 : ℕ) + (12 : ℂ) * s ^ (8 : ℕ) + (15 / 8 : ℂ) * s ^ (9 : ℕ) + (3 / 4 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-3510 : ℂ) * s + (-8799 : ℂ) * s ^ (2 : ℕ) + (-46817 / 4 : ℂ) * s ^ (3 : ℕ) + (-156863 / 16 : ℂ) * s ^ (4 : ℕ) + (-91383 / 16 : ℂ) * s ^ (5 : ℕ) + (-4213 / 2 : ℂ) * s ^ (6 : ℕ) + (-3327 / 8 : ℂ) * s ^ (7 : ℕ) + (-467 / 16 : ℂ) * s ^ (8 : ℕ) + (9 / 16 : ℂ) * s ^ (9 : ℕ) + (-3 / 8 : ℂ) * s ^ (10 : ℕ)) + r * ((0 : ℂ) + r * (((-1008 : ℂ) + (876 : ℂ) * s + (14895 / 2 : ℂ) * s ^ (2 : ℕ) + (16051 / 2 : ℂ) * s ^ (3 : ℕ) + (31951 / 8 : ℂ) * s ^ (4 : ℕ) + (4847 / 4 : ℂ) * s ^ (5 : ℕ) + (681 / 2 : ℂ) * s ^ (6 : ℕ) + (271 / 4 : ℂ) * s ^ (7 : ℕ) + (41 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-108 : ℂ) + (2286 : ℂ) * s + (1554 : ℂ) * s ^ (2 : ℕ) + (1557 : ℂ) * s ^ (3 : ℕ) + (1769 / 2 : ℂ) * s ^ (4 : ℕ) + (306 : ℂ) * s ^ (5 : ℕ) + (97 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((1224 : ℂ) + (576 : ℂ) * s + (-73 : ℂ) * s ^ (2 : ℕ) + (-26 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-108 : ℂ) + (-36 : ℂ) * s))))))))))))) / (r ^ (8 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (3 : ℕ))

theorem skewSrcF_lauI3_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    skewSrcF_lauI3 s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = skewSrcFLam_lauI3 s r := by
  unfold skewSrcF_lauI3
  rw [skewPieceSF_qtr0_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qtr1_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qtr2_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qt0_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qt1_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qt2_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qT0_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qT1_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qT2_lauI3 s r hr hf hs hs3 hs1, skewPieceSF_qT3_lauI3 s r hr hf hs hs3 hs1]
  unfold skewSrcFLam_lauI3
  simp only [← add_div]
  ring

end
end RHTower.D4BMScalarStream
