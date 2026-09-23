import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorOnsetCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorBoundaryFlux
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The even-sector onset trace at the fundamental harmonic

At the fundamental harmonic `μ = (s+1)(s+2)` and with the Laurent coefficients at their actual
values, the time component of the symplectic current between the `−` mode and the `++` Laurent
responses is a rational function of `r` (`onsetCurrentSS_eq`, `onsetCurrentVV_eq`). Its coordinate
density `r²·(current)` is `N(s,r)/(r⁴(r²−1)·s(s+3))` with `N` even in `r` of degree six
(`onsetDensitySS_eq`; `N/(r⁴(r²−1)(s+3))`, degree four, for the vector–vector block): the density
has the simple horizon pole `1/(r²−1)` and is `O(1)` at the AdS boundary. Under `r = 1/u`,
`u = (1−z)^{1/2}`, `z = 1 − r⁻²`, the density times `dr/dz = 1/(2u³)` is the Laurent polynomial
`onsetLaurentSS s u` in `u` (`onsetDensitySS_substitution`), so the radial integral of the dressed
density `z^{(s−3)/2}·r²·(current)` over the exterior is the sum of the Euler integrals
`∫₀¹ z^{(s−5)/2}(1−z)^{(3−k)/2} dz`, `k = 0, 2, 4, 6`, each continued as the Gamma quotient
`contBeta`. The onset trace so defined (`onsetTraceSS`, `onsetTraceVV`) is the single transcendental
`Γ(1/2)·Γ((s−3)/2)/Γ((s−2)/2)` (with `Γ(1/2) = √π`) times an explicit rational function of `s`
(`onsetTraceSS_eq`, `onsetTraceVV_eq`): every half-integer Beta value reduces to `B((s−3)/2, 1/2)`
by the recursion `Γ(x+1) = xΓ(x)`, and no integer Beta value occurs, so the trace has no rational
part and no logarithmic term.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- Meromorphically continued Euler integral `∫₀¹ z^{a−1}(1−z)^{b−1} dz` as a Gamma quotient. -/
def contBeta (a b : ℂ) : ℂ := Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b)

/-- Where both exponents have positive real part, the continued Euler integral is the Beta integral. -/
theorem contBeta_eq_betaIntegral (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    contBeta a b = Complex.betaIntegral a b := by
  unfold contBeta
  rw [Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb]
  have h : Complex.Gamma (a + b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  field_simp

theorem gamma_three_half : Complex.Gamma (3 / 2) = (1 / 2 : ℂ) * Complex.Gamma (1 / 2) := by
  rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]

theorem gamma_five_half : Complex.Gamma (5 / 2) = (3 / 2 : ℂ) * ((1 / 2 : ℂ) * Complex.Gamma (1 / 2)) := by
  rw [show (5 / 2 : ℂ) = 3 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num), gamma_three_half]

theorem gamma_neg_half : Complex.Gamma (-1 / 2) = (-2 : ℂ) * Complex.Gamma (1 / 2) := by
  have h := Complex.Gamma_add_one (-1 / 2 : ℂ) (by norm_num)
  rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num] at h
  rw [h]; ring

theorem gamma_shift_three_half (s : ℂ) (hs2 : s - 2 ≠ 0) :
    Complex.Gamma ((s - 3) / 2 + 3 / 2) = ((s - 2) / 2) * Complex.Gamma ((s - 2) / 2) := by
  rw [show (s - 3) / 2 + 3 / 2 = (s - 2) / 2 + 1 by ring, Complex.Gamma_add_one _ (by
    intro h; apply hs2; linear_combination 2 * h)]

theorem gamma_shift_five_half (s : ℂ) (hs : s ≠ 0) (hs2 : s - 2 ≠ 0) :
    Complex.Gamma ((s - 3) / 2 + 5 / 2) = (s / 2) * (((s - 2) / 2) * Complex.Gamma ((s - 2) / 2)) := by
  rw [show (s - 3) / 2 + 5 / 2 = s / 2 + 1 by ring, Complex.Gamma_add_one _ (by
    intro h; apply hs; linear_combination 2 * h), show s / 2 = (s - 2) / 2 + 1 by ring,
    Complex.Gamma_add_one _ (by intro h; apply hs2; linear_combination 2 * h)]

theorem gamma_shift_neg_half (s : ℂ) (hs4 : s - 4 ≠ 0) :
    Complex.Gamma ((s - 3) / 2 + -1 / 2) = Complex.Gamma ((s - 2) / 2) / ((s - 4) / 2) := by
  have h := Complex.Gamma_add_one ((s - 4) / 2) (by intro h; apply hs4; linear_combination 2 * h)
  rw [show (s - 4) / 2 + 1 = (s - 2) / 2 by ring] at h
  rw [show (s - 3) / 2 + -1 / 2 = (s - 4) / 2 by ring, h]
  field_simp

theorem gamma_shift_one_half (s : ℂ) : Complex.Gamma ((s - 3) / 2 + 1 / 2) = Complex.Gamma ((s - 2) / 2) := by
  rw [show (s - 3) / 2 + 1 / 2 = (s - 2) / 2 by ring]

/-! ## Horner forms at the fundamental harmonic -/

theorem onsetCoeff_qtr0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCoeff_qtr0 s r ((s + 1) * (s + 2)) = (((-15 : ℂ) + (-39 / 2 : ℂ) * s + (-21 / 2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((56 : ℂ) + (-7 : ℂ) * s + (-7 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((11 : ℂ) + (9 / 2 : ℂ) * s + (3 / 2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (r * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3)) := by
  unfold onsetCoeff_qtr0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCoeff_qtr1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCoeff_qtr1 s r ((s + 1) * (s + 2)) = (((21 : ℂ) + (27 / 2 : ℂ) * s + (5 / 2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((-9 : ℂ) + (-1 / 2 : ℂ) * s + (1 / 2 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-8 : ℂ)))))) / ((r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3)) := by
  unfold onsetCoeff_qtr1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCoeff_qtr2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCoeff_qtr2 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((-3 : ℂ) + (-1 : ℂ) * s) + r * ((0 : ℂ) + r * ((-1 : ℂ))))) / (s ^ (3 : ℕ) * (s + 3)) := by
  unfold onsetCoeff_qtr2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCoeff_qt0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCoeff_qt0 s r ((s + 1) * (s + 2)) = (((11 : ℂ) * s + (43 / 2 : ℂ) * s ^ (2 : ℕ) + (13 : ℂ) * s ^ (3 : ℕ) + (5 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((72 : ℂ) + (-1 : ℂ) * s + (-13 / 2 : ℂ) * s ^ (2 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((20 : ℂ) + (6 : ℂ) * s) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (3 : ℕ) * (s + 3)) := by
  unfold onsetCoeff_qt0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCoeff_qt1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCoeff_qt1 s r ((s + 1) * (s + 2)) = (((30 : ℂ) + (14 : ℂ) * s + (-1 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-10 : ℂ)) + r * ((0 : ℂ) + r * ((-12 : ℂ)))))) / (r * (r ^ (2 : ℕ) - 1) * s ^ (3 : ℕ) * (s + 3)) := by
  unfold onsetCoeff_qt1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCoeff_qt2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCoeff_qt2 s r ((s + 1) * (s + 2)) = (((-6 : ℂ) + (-2 : ℂ) * s) + r * ((0 : ℂ) + r * ((-2 : ℂ)))) / (s ^ (3 : ℕ) * (s + 3)) := by
  unfold onsetCoeff_qt2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCoeff_qT0_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCoeff_qT0 s r ((s + 1) * (s + 2)) = (((31 : ℂ) * s + (53 / 2 : ℂ) * s ^ (2 : ℕ) + (9 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((72 : ℂ) + (-105 : ℂ) * s + (-76 : ℂ) * s ^ (2 : ℕ) + (-20 : ℂ) * s ^ (3 : ℕ) + (-3 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-52 : ℂ) + (-35 : ℂ) * s + (13 / 2 : ℂ) * s ^ (2 : ℕ) + (7 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-32 : ℂ) + (-3 : ℂ) * s + (-1 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((12 : ℂ)))))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3)) := by
  unfold onsetCoeff_qT0
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCoeff_qT1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCoeff_qT1 s r ((s + 1) * (s + 2)) = (((90 : ℂ) + (76 : ℂ) * s + (25 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-138 : ℂ) + (11 : ℂ) * s + (16 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * (((-28 : ℂ) + (-9 : ℂ) * s + (-3 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((36 : ℂ)))))))) / (r * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3)) := by
  unfold onsetCoeff_qT1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCoeff_qT2_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCoeff_qT2 s r ((s + 1) * (s + 2)) = (((-54 : ℂ) + (-31 : ℂ) * s + (-5 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * (((20 : ℂ) + (3 : ℂ) * s + (-1 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((18 : ℂ)))))) / ((r ^ (2 : ℕ) - 1) * s ^ (2 : ℕ) * (s + 3)) := by
  unfold onsetCoeff_qT2
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCoeff_qT3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCoeff_qT3 s r ((s + 1) * (s + 2)) = ((0 : ℂ) + r * (((6 : ℂ) + (2 : ℂ) * s) + r * ((0 : ℂ) + r * ((2 : ℂ))))) / (s ^ (2 : ℕ) * (s + 3)) := by
  unfold onsetCoeff_qT3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCurrent_lauR_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCurrent_lauR s r ((s + 1) * (s + 2)) = (((-91 / 2 : ℂ) * s + (69 / 4 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-9 / 4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-36 : ℂ) + (-19 / 2 : ℂ) * s + (53 / 4 : ℂ) * s ^ (2 : ℕ) + (7 / 2 : ℂ) * s ^ (3 : ℕ) + (3 / 4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-10 : ℂ) + (3 : ℂ) * s + (-1 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((6 : ℂ)))))))) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3)) := by
  unfold onsetCurrent_lauR
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCurrent_lauI1_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCurrent_lauI1 s r ((s + 1) * (s + 2)) = (((21 / 2 : ℂ) + (21 / 4 : ℂ) * s + (-15 / 2 : ℂ) * s ^ (2 : ℕ) + (-9 / 4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((39 / 2 : ℂ) + (105 / 4 : ℂ) * s + (15 / 2 : ℂ) * s ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (3 : ℕ)))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s * (s + 3)) := by
  unfold onsetCurrent_lauI1
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

theorem onsetCurrent_lauI3_lam (s r : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) : onsetCurrent_lauI3 s r ((s + 1) * (s + 2)) = (((-51 / 2 : ℂ) * s + (-139 / 4 : ℂ) * s ^ (2 : ℕ) + (-31 / 2 : ℂ) * s ^ (3 : ℕ) + (-9 / 4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((100 : ℂ) + (305 / 2 : ℂ) * s + (285 / 4 : ℂ) * s ^ (2 : ℕ) + (23 / 2 : ℂ) * s ^ (3 : ℕ) + (3 / 4 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((-54 : ℂ) + (-15 : ℂ) * s + (-3 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-6 : ℂ)))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s ^ (2 : ℕ) * (s + 3)) := by
  unfold onsetCurrent_lauI3
  have hμ : (2 : ℂ) - ((s + 1) * (s + 2)) ≠ 0 := by
    rw [show (2 : ℂ) - ((s + 1) * (s + 2)) = -(s * (s + 3)) by ring]; exact neg_ne_zero.mpr (mul_ne_zero hs hs3)
  have hres : ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) ≠ 0 := by
    rw [show ((s + 1) * (s + 2)) - (2 * s + 1) * (2 * s + 2) = -(3 * (s * (s + 1))) by ring]; exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (mul_ne_zero hs hs1))
  field_simp
  ring

/-! ## The SS source onset current at the fundamental harmonic -/

theorem onsetPieceSS_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qtr0 s r ((s + 1) * (s + 2)) * ssSourceTR s r ((s + 1) * (s + 2)) = (((-135 / 4 : ℂ) * s ^ (2 : ℕ) + (-279 / 2 : ℂ) * s ^ (3 : ℕ) + (-3897 / 16 : ℂ) * s ^ (4 : ℕ) + (-1881 / 8 : ℂ) * s ^ (5 : ℕ) + (-273 / 2 : ℂ) * s ^ (6 : ℕ) + (-381 / 8 : ℂ) * s ^ (7 : ℕ) + (-147 / 16 : ℂ) * s ^ (8 : ℕ) + (-3 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((45 : ℂ) * s + (357 : ℂ) * s ^ (2 : ℕ) + (717 : ℂ) * s ^ (3 : ℕ) + (5175 / 8 : ℂ) * s ^ (4 : ℕ) + (535 / 2 : ℂ) * s ^ (5 : ℕ) + (163 / 4 : ℂ) * s ^ (6 : ℕ) + (-3 / 2 : ℂ) * s ^ (7 : ℕ) + (-5 / 8 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-303 : ℂ) * s + (-3185 / 4 : ℂ) * s ^ (2 : ℕ) + (-765 / 2 : ℂ) * s ^ (3 : ℕ) + (-597 / 16 : ℂ) * s ^ (4 : ℕ) + (807 / 8 : ℂ) * s ^ (5 : ℕ) + (65 : ℂ) * s ^ (6 : ℕ) + (101 / 8 : ℂ) * s ^ (7 : ℕ) + (9 / 16 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((471 : ℂ) * s + (-146 : ℂ) * s ^ (2 : ℕ) + (-1289 / 4 : ℂ) * s ^ (3 : ℕ) + (-745 / 4 : ℂ) * s ^ (4 : ℕ) + (-285 / 4 : ℂ) * s ^ (5 : ℕ) + (-63 / 4 : ℂ) * s ^ (6 : ℕ) + (-3 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((135 : ℂ) * s + (195 : ℂ) * s ^ (2 : ℕ) + (443 / 4 : ℂ) * s ^ (3 : ℕ) + (54 : ℂ) * s ^ (4 : ℕ) + (45 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s + (-18 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qtr0_lam s r hs hs3 hs1, ssSourceTR_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceSS_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qtr1 s r ((s + 1) * (s + 2)) * ssSourceTR1 s r ((s + 1) * (s + 2)) = (((945 / 4 : ℂ) * s ^ (2 : ℕ) + (3663 / 4 : ℂ) * s ^ (3 : ℕ) + (23301 / 16 : ℂ) * s ^ (4 : ℕ) + (4947 / 4 : ℂ) * s ^ (5 : ℕ) + (1221 / 2 : ℂ) * s ^ (6 : ℕ) + (1413 / 8 : ℂ) * s ^ (7 : ℕ) + (447 / 16 : ℂ) * s ^ (8 : ℕ) + (15 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-189 : ℂ) * s + (-1404 : ℂ) * s ^ (2 : ℕ) + (-3039 : ℂ) * s ^ (3 : ℕ) + (-26787 / 8 : ℂ) * s ^ (4 : ℕ) + (-16837 / 8 : ℂ) * s ^ (5 : ℕ) + (-2989 / 4 : ℂ) * s ^ (6 : ℕ) + (-543 / 4 : ℂ) * s ^ (7 : ℕ) + (-67 / 8 : ℂ) * s ^ (8 : ℕ) + (3 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((585 : ℂ) * s + (9447 / 4 : ℂ) * s ^ (2 : ℕ) + (10197 / 4 : ℂ) * s ^ (3 : ℕ) + (24729 / 16 : ℂ) * s ^ (4 : ℕ) + (4473 / 8 : ℂ) * s ^ (5 : ℕ) + (84 : ℂ) * s ^ (6 : ℕ) + (-51 / 8 : ℂ) * s ^ (7 : ℕ) + (-37 / 16 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-711 : ℂ) * s + (-714 : ℂ) * s ^ (2 : ℕ) + (909 / 4 : ℂ) * s ^ (3 : ℕ) + (1703 / 4 : ℂ) * s ^ (4 : ℕ) + (849 / 4 : ℂ) * s ^ (5 : ℕ) + (181 / 4 : ℂ) * s ^ (6 : ℕ) + (5 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((51 : ℂ) * s + (-562 : ℂ) * s ^ (2 : ℕ) + (-1459 / 4 : ℂ) * s ^ (3 : ℕ) + (-175 : ℂ) * s ^ (4 : ℕ) + (-157 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((216 : ℂ) * s + (36 : ℂ) * s ^ (2 : ℕ) + (-12 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qtr1_lam s r hs hs3 hs1, ssSourceTR1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceSS_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qtr2 s r ((s + 1) * (s + 2)) * ssSourceTR2 s r ((s + 1) * (s + 2)) = (((-405 / 2 : ℂ) * s ^ (2 : ℕ) + (-3159 / 4 : ℂ) * s ^ (3 : ℕ) + (-5049 / 4 : ℂ) * s ^ (4 : ℕ) + (-1074 : ℂ) * s ^ (5 : ℕ) + (-528 : ℂ) * s ^ (6 : ℕ) + (-603 / 4 : ℂ) * s ^ (7 : ℕ) + (-93 / 4 : ℂ) * s ^ (8 : ℕ) + (-3 / 2 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((108 : ℂ) * s + (1035 : ℂ) * s ^ (2 : ℕ) + (2643 : ℂ) * s ^ (3 : ℕ) + (13121 / 4 : ℂ) * s ^ (4 : ℕ) + (2267 : ℂ) * s ^ (5 : ℕ) + (1771 / 2 : ℂ) * s ^ (6 : ℕ) + (182 : ℂ) * s ^ (7 : ℕ) + (61 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-324 : ℂ) * s + (-3441 / 2 : ℂ) * s ^ (2 : ℕ) + (-10901 / 4 : ℂ) * s ^ (3 : ℕ) + (-2209 : ℂ) * s ^ (4 : ℕ) + (-2161 / 2 : ℂ) * s ^ (5 : ℕ) + (-573 / 2 : ℂ) * s ^ (6 : ℕ) + (-121 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((312 : ℂ) * s + (1040 : ℂ) * s ^ (2 : ℕ) + (336 : ℂ) * s ^ (3 : ℕ) + (-79 : ℂ) * s ^ (4 : ℕ) + (-80 : ℂ) * s ^ (5 : ℕ) + (-17 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-180 : ℂ) * s + (354 : ℂ) * s ^ (2 : ℕ) + (264 : ℂ) * s ^ (3 : ℕ) + (132 : ℂ) * s ^ (4 : ℕ) + (30 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-108 : ℂ) * s + (-18 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qtr2_lam s r hs hs3 hs1, ssSourceTR2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceSS_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qt0 s r ((s + 1) * (s + 2)) * ssSourceT s r ((s + 1) * (s + 2)) = (((-99 / 16 : ℂ) * s ^ (3 : ℕ) + (-849 / 32 : ℂ) * s ^ (4 : ℕ) + (-1467 / 32 : ℂ) * s ^ (5 : ℕ) + (-651 / 16 : ℂ) * s ^ (6 : ℕ) + (-39 / 2 : ℂ) * s ^ (7 : ℕ) + (-153 / 32 : ℂ) * s ^ (8 : ℕ) + (-15 / 32 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-57 : ℂ) * s ^ (2 : ℕ) + (-535 / 4 : ℂ) * s ^ (3 : ℕ) + (-681 / 8 : ℂ) * s ^ (4 : ℕ) + (77 / 4 : ℂ) * s ^ (5 : ℕ) + (48 : ℂ) * s ^ (6 : ℕ) + (107 / 4 : ℂ) * s ^ (7 : ℕ) + (57 / 8 : ℂ) * s ^ (8 : ℕ) + (3 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-249 / 2 : ℂ) * s + (-161 / 2 : ℂ) * s ^ (2 : ℕ) + (1169 / 16 : ℂ) * s ^ (3 : ℕ) + (2901 / 32 : ℂ) * s ^ (4 : ℕ) + (835 / 32 : ℂ) * s ^ (5 : ℕ) + (-85 / 16 : ℂ) * s ^ (6 : ℕ) + (-55 / 8 : ℂ) * s ^ (7 : ℕ) + (-75 / 32 : ℂ) * s ^ (8 : ℕ) + (-9 / 32 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-108 : ℂ) + (60 : ℂ) * s + (241 / 2 : ℂ) * s ^ (2 : ℕ) + (647 / 8 : ℂ) * s ^ (3 : ℕ) + (71 / 2 : ℂ) * s ^ (4 : ℕ) + (7 / 2 : ℂ) * s ^ (5 : ℕ) + (-2 : ℂ) * s ^ (6 : ℕ) + (-3 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((78 : ℂ) + (127 / 2 : ℂ) * s + (29 : ℂ) * s ^ (2 : ℕ) + (-11 : ℂ) * s ^ (3 : ℕ) + (-29 / 2 : ℂ) * s ^ (4 : ℕ) + (-3 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((48 : ℂ) + (7 : ℂ) * s + (-12 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-18 : ℂ) + (-6 : ℂ) * s))))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qt0_lam s r hs hs3 hs1, ssSourceT_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceSS_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qt1 s r ((s + 1) * (s + 2)) * ssSourceT1 s r ((s + 1) * (s + 2)) = (((-135 / 2 : ℂ) * s ^ (2 : ℕ) + (-891 / 4 : ℂ) * s ^ (3 : ℕ) + (-1113 / 4 : ℂ) * s ^ (4 : ℕ) + (-1275 / 8 : ℂ) * s ^ (5 : ℕ) + (-141 / 4 : ℂ) * s ^ (6 : ℕ) + (15 / 4 : ℂ) * s ^ (7 : ℕ) + (3 : ℂ) * s ^ (8 : ℕ) + (3 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-90 : ℂ) * s + (-99 / 2 : ℂ) * s ^ (2 : ℕ) + (623 / 2 : ℂ) * s ^ (3 : ℕ) + (1909 / 4 : ℂ) * s ^ (4 : ℕ) + (2037 / 8 : ℂ) * s ^ (5 : ℕ) + (44 : ℂ) * s ^ (6 : ℕ) + (-31 / 4 : ℂ) * s ^ (7 : ℕ) + (-15 / 4 : ℂ) * s ^ (8 : ℕ) + (-3 / 8 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((120 : ℂ) * s + (443 / 2 : ℂ) * s ^ (2 : ℕ) + (5 / 4 : ℂ) * s ^ (3 : ℕ) + (-299 / 2 : ℂ) * s ^ (4 : ℕ) + (-293 / 4 : ℂ) * s ^ (5 : ℕ) + (-19 / 4 : ℂ) * s ^ (6 : ℕ) + (4 : ℂ) * s ^ (7 : ℕ) + (3 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((6 : ℂ) * s + (-161 / 2 : ℂ) * s ^ (2 : ℕ) + (-122 : ℂ) * s ^ (3 : ℕ) + (-177 / 2 : ℂ) * s ^ (4 : ℕ) + (-31 : ℂ) * s ^ (5 : ℕ) + (-4 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-36 : ℂ) * s + (-42 : ℂ) * s ^ (2 : ℕ) + (26 : ℂ) * s ^ (3 : ℕ) + (39 : ℂ) * s ^ (4 : ℕ) + (9 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((18 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qt1_lam s r hs hs3 hs1, ssSourceT1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceSS_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qt2 s r ((s + 1) * (s + 2)) * ssSourceT2 s r ((s + 1) * (s + 2)) = (((135 / 2 : ℂ) * s ^ (2 : ℕ) + (963 / 4 : ℂ) * s ^ (3 : ℕ) + (681 / 2 : ℂ) * s ^ (4 : ℕ) + (489 / 2 : ℂ) * s ^ (5 : ℕ) + (189 / 2 : ℂ) * s ^ (6 : ℕ) + (75 / 4 : ℂ) * s ^ (7 : ℕ) + (3 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((54 : ℂ) * s + (-27 : ℂ) * s ^ (2 : ℕ) + (-1749 / 4 : ℂ) * s ^ (3 : ℕ) + (-2777 / 4 : ℂ) * s ^ (4 : ℕ) + (-1893 / 4 : ℂ) * s ^ (5 : ℕ) + (-637 / 4 : ℂ) * s ^ (6 : ℕ) + (-51 / 2 : ℂ) * s ^ (7 : ℕ) + (-3 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-126 : ℂ) * s + (-177 : ℂ) * s ^ (2 : ℕ) + (471 / 4 : ℂ) * s ^ (3 : ℕ) + (343 : ℂ) * s ^ (4 : ℕ) + (455 / 2 : ℂ) * s ^ (5 : ℕ) + (64 : ℂ) * s ^ (6 : ℕ) + (27 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((42 : ℂ) * s + (128 : ℂ) * s ^ (2 : ℕ) + (449 / 4 : ℂ) * s ^ (3 : ℕ) + (177 / 4 : ℂ) * s ^ (4 : ℕ) + (35 / 4 : ℂ) * s ^ (5 : ℕ) + (3 / 4 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((30 : ℂ) * s + (35 / 2 : ℂ) * s ^ (2 : ℕ) + (-61 / 2 : ℂ) * s ^ (3 : ℕ) + (-67 / 2 : ℂ) * s ^ (4 : ℕ) + (-15 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-9 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ)))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qt2_lam s r hs hs3 hs1, ssSourceT2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceSS_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qT0 s r ((s + 1) * (s + 2)) * ssSourceTF s r ((s + 1) * (s + 2)) = (((-31 / 4 : ℂ) * s ^ (2 : ℕ) + (-177 / 8 : ℂ) * s ^ (3 : ℕ) + (-93 / 4 : ℂ) * s ^ (4 : ℕ) + (-23 / 2 : ℂ) * s ^ (5 : ℕ) + (-3 : ℂ) * s ^ (6 : ℕ) + (-3 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-18 : ℂ) * s + (85 / 4 : ℂ) * s ^ (2 : ℕ) + (80 : ℂ) * s ^ (3 : ℕ) + (313 / 4 : ℂ) * s ^ (4 : ℕ) + (125 / 4 : ℂ) * s ^ (5 : ℕ) + (13 / 2 : ℂ) * s ^ (6 : ℕ) + (3 / 4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((85 : ℂ) * s + (-281 / 4 : ℂ) * s ^ (2 : ℕ) + (-377 / 8 : ℂ) * s ^ (3 : ℕ) + (-65 / 4 : ℂ) * s ^ (4 : ℕ) + (-17 / 2 : ℂ) * s ^ (5 : ℕ) + (-5 / 2 : ℂ) * s ^ (6 : ℕ) + (-3 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-44 : ℂ) * s + (-73 / 4 : ℂ) * s ^ (2 : ℕ) + (65 / 4 : ℂ) * s ^ (3 : ℕ) + (33 / 4 : ℂ) * s ^ (4 : ℕ) + (7 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-35 : ℂ) * s + (-9 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((12 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qT0_lam s r hs hs3 hs1, ssSourceTF_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceSS_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qT1 s r ((s + 1) * (s + 2)) * ssSourceTF1 s r ((s + 1) * (s + 2)) = (((-90 : ℂ) * s + (-301 : ℂ) * s ^ (2 : ℕ) + (-395 : ℂ) * s ^ (3 : ℕ) + (-525 / 2 : ℂ) * s ^ (4 : ℕ) + (-191 / 2 : ℂ) * s ^ (5 : ℕ) + (-37 / 2 : ℂ) * s ^ (6 : ℕ) + (-3 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((408 : ℂ) * s + (922 : ℂ) * s ^ (2 : ℕ) + (1403 / 2 : ℂ) * s ^ (3 : ℕ) + (191 : ℂ) * s ^ (4 : ℕ) + (-3 : ℂ) * s ^ (5 : ℕ) + (-7 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-566 : ℂ) * s + (-592 : ℂ) * s ^ (2 : ℕ) + (-29 / 2 : ℂ) * s ^ (3 : ℕ) + (223 / 2 : ℂ) * s ^ (4 : ℕ) + (61 / 2 : ℂ) * s ^ (5 : ℕ) + (5 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((156 : ℂ) * s + (-251 : ℂ) * s ^ (2 : ℕ) + (-177 : ℂ) * s ^ (3 : ℕ) + (-41 : ℂ) * s ^ (4 : ℕ) + (-3 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((164 : ℂ) * s + (162 : ℂ) * s ^ (2 : ℕ) + (42 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qT1_lam s r hs hs3 hs1, ssSourceTF1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceSS_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qT2 s r ((s + 1) * (s + 2)) * ssSourceTF2 s r ((s + 1) * (s + 2)) = (((270 : ℂ) * s + (938 : ℂ) * s ^ (2 : ℕ) + (2569 / 2 : ℂ) * s ^ (3 : ℕ) + (1777 / 2 : ℂ) * s ^ (4 : ℕ) + (661 / 2 : ℂ) * s ^ (5 : ℕ) + (127 / 2 : ℂ) * s ^ (6 : ℕ) + (5 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-964 : ℂ) * s + (-2718 : ℂ) * s ^ (2 : ℕ) + (-2869 : ℂ) * s ^ (3 : ℕ) + (-1410 : ℂ) * s ^ (4 : ℕ) + (-320 : ℂ) * s ^ (5 : ℕ) + (-24 : ℂ) * s ^ (6 : ℕ) + (1 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((1148 : ℂ) * s + (2320 : ℂ) * s ^ (2 : ℕ) + (2839 / 2 : ℂ) * s ^ (3 : ℕ) + (615 / 2 : ℂ) * s ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (5 : ℕ) + (-11 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-376 : ℂ) * s + (-78 : ℂ) * s ^ (2 : ℕ) + (265 : ℂ) * s ^ (3 : ℕ) + (108 : ℂ) * s ^ (4 : ℕ) + (5 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((-186 : ℂ) * s + (-414 : ℂ) * s ^ (2 : ℕ) + (-96 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((108 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qT2_lam s r hs hs3 hs1, ssSourceTF2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceSS_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qT3 s r ((s + 1) * (s + 2)) * ssSourceTF3 s r ((s + 1) * (s + 2)) = (((-180 : ℂ) * s + (-642 : ℂ) * s ^ (2 : ℕ) + (-908 : ℂ) * s ^ (3 : ℕ) + (-652 : ℂ) * s ^ (4 : ℕ) + (-252 : ℂ) * s ^ (5 : ℕ) + (-50 : ℂ) * s ^ (6 : ℕ) + (-4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((624 : ℂ) * s + (1948 : ℂ) * s ^ (2 : ℕ) + (2326 : ℂ) * s ^ (3 : ℕ) + (1326 : ℂ) * s ^ (4 : ℕ) + (362 : ℂ) * s ^ (5 : ℕ) + (38 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-744 : ℂ) * s + (-1882 : ℂ) * s ^ (2 : ℕ) + (-1638 : ℂ) * s ^ (3 : ℕ) + (-566 : ℂ) * s ^ (4 : ℕ) + (-66 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((288 : ℂ) * s + (408 : ℂ) * s ^ (2 : ℕ) + (-24 : ℂ) * s ^ (3 : ℕ) + (-48 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * (((60 : ℂ) * s + (264 : ℂ) * s ^ (2 : ℕ) + (60 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-48 : ℂ) * s))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qT3_lam s r hs hs3 hs1, ssSourceTF3_lam s r hs hs3 hs1]
  field_simp
  ring

/-- The source-only onset current of the SS harmonic sources at the fundamental harmonic. -/
def onsetSrcCurrentSS (s r : ℂ) : ℂ := (((-51 / 4 : ℂ) * s ^ (2 : ℕ) + (-677 / 16 : ℂ) * s ^ (3 : ℕ) + (-2017 / 32 : ℂ) * s ^ (4 : ℕ) + (-1971 / 32 : ℂ) * s ^ (5 : ℕ) + (-695 / 16 : ℂ) * s ^ (6 : ℕ) + (-157 / 8 : ℂ) * s ^ (7 : ℕ) + (-153 / 32 : ℂ) * s ^ (8 : ℕ) + (-15 / 32 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-22 : ℂ) * s + (111 / 4 : ℂ) * s ^ (2 : ℕ) + (300 : ℂ) * s ^ (3 : ℕ) + (3695 / 8 : ℂ) * s ^ (4 : ℕ) + (1203 / 4 : ℂ) * s ^ (5 : ℕ) + (501 / 4 : ℂ) * s ^ (6 : ℕ) + (79 / 2 : ℂ) * s ^ (7 : ℕ) + (65 / 8 : ℂ) * s ^ (8 : ℕ) + (3 / 4 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-499 / 2 : ℂ) * s + (-1661 / 4 : ℂ) * s ^ (2 : ℕ) + (-10345 / 16 : ℂ) * s ^ (3 : ℕ) + (-18555 / 32 : ℂ) * s ^ (4 : ℕ) + (-9141 / 32 : ℂ) * s ^ (5 : ℕ) + (-1425 / 16 : ℂ) * s ^ (6 : ℕ) + (-41 / 2 : ℂ) * s ^ (7 : ℕ) + (-107 / 32 : ℂ) * s ^ (8 : ℕ) + (-9 / 32 : ℂ) * s ^ (9 : ℕ)) + r * ((0 : ℂ) + r * (((-108 : ℂ) + (204 : ℂ) * s + (1635 / 4 : ℂ) * s ^ (2 : ℕ) + (3139 / 8 : ℂ) * s ^ (3 : ℕ) + (179 : ℂ) * s ^ (4 : ℕ) + (46 : ℂ) * s ^ (5 : ℕ) + (29 / 4 : ℂ) * s ^ (6 : ℕ) + (5 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((78 : ℂ) + (133 / 2 : ℂ) * s + (-11 / 2 : ℂ) * s ^ (2 : ℕ) + (-7 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((48 : ℂ) + (7 : ℂ) * s + (-3 : ℂ) * s ^ (2 : ℕ)) + r * ((0 : ℂ) + r * ((-18 : ℂ) + (-6 : ℂ) * s))))))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s ^ (2 : ℕ) * (s + 3) ^ (2 : ℕ))

theorem onsetSrcCurrentSS_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetSrcCurrent s r ((s + 1) * (s + 2)) (ssSourceTR s r ((s + 1) * (s + 2))) (ssSourceTR1 s r ((s + 1) * (s + 2))) (ssSourceTR2 s r ((s + 1) * (s + 2))) (ssSourceT s r ((s + 1) * (s + 2))) (ssSourceT1 s r ((s + 1) * (s + 2))) (ssSourceT2 s r ((s + 1) * (s + 2))) (ssSourceTF s r ((s + 1) * (s + 2))) (ssSourceTF1 s r ((s + 1) * (s + 2))) (ssSourceTF2 s r ((s + 1) * (s + 2))) (ssSourceTF3 s r ((s + 1) * (s + 2))) = onsetSrcCurrentSS s r := by
  unfold onsetSrcCurrent
  rw [onsetPieceSS_qtr0 s r hr hf hs hs3 hs1, onsetPieceSS_qtr1 s r hr hf hs hs3 hs1, onsetPieceSS_qtr2 s r hr hf hs hs3 hs1, onsetPieceSS_qt0 s r hr hf hs hs3 hs1, onsetPieceSS_qt1 s r hr hf hs hs3 hs1, onsetPieceSS_qt2 s r hr hf hs hs3 hs1, onsetPieceSS_qT0 s r hr hf hs hs3 hs1, onsetPieceSS_qT1 s r hr hf hs hs3 hs1, onsetPieceSS_qT2 s r hr hf hs hs3 hs1, onsetPieceSS_qT3 s r hr hf hs hs3 hs1]
  unfold onsetSrcCurrentSS
  simp only [← add_div]
  ring

/-! ## The SS `++` Laurent response against the `−` mode -/

/-- The onset current with the SS Laurent coefficients at their actual values. -/
theorem onsetCurrentSS_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCurrentSS s r ((s + 1) * (s + 2)) (laurentMasterA s ((s + 1) * (s + 2))) (laurentMasterB s ((s + 1) * (s + 2))) = (((27 / 8 : ℂ) * s ^ (2 : ℕ) + (129 / 16 : ℂ) * s ^ (3 : ℕ) + (11 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (5 : ℕ) + (-7 / 8 : ℂ) * s ^ (6 : ℕ) + (-3 / 16 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-3 : ℂ) + (-29 / 2 : ℂ) * s + (-157 / 8 : ℂ) * s ^ (2 : ℕ) + (-11 / 2 : ℂ) * s ^ (3 : ℕ) + (7 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((7 / 2 : ℂ) * s + (5 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-1 : ℂ) * s))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) * s * (s + 3)) := by
  unfold onsetCurrentSS
  rw [onsetSrcCurrentSS_eq s r hr hf hs hs3 hs1, ssLaurentA_lam s hs hs3 hs1, ssLaurentB_lam s hs hs3, onsetCurrent_lauR_lam s r hs hs3 hs1, onsetCurrent_lauI1_lam s r hs hs3 hs1, onsetCurrent_lauI3_lam s r hs hs3 hs1]
  unfold onsetSrcCurrentSS
  field_simp
  ring

/-- Coordinate density `r²·(onset current)` of the SS block: numerator even in `r`, simple horizon pole. -/
def onsetDensitySS (s r : ℂ) : ℂ := (((27 / 8 : ℂ) * s ^ (2 : ℕ) + (129 / 16 : ℂ) * s ^ (3 : ℕ) + (11 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (5 : ℕ) + (-7 / 8 : ℂ) * s ^ (6 : ℕ) + (-3 / 16 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-3 : ℂ) + (-29 / 2 : ℂ) * s + (-157 / 8 : ℂ) * s ^ (2 : ℕ) + (-11 / 2 : ℂ) * s ^ (3 : ℕ) + (7 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((7 / 2 : ℂ) * s + (5 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ)) + r * ((0 : ℂ) + r * ((-1 : ℂ) * s))))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) * s * (s + 3))

theorem onsetDensitySS_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    r ^ (2 : ℕ) * onsetCurrentSS s r ((s + 1) * (s + 2)) (laurentMasterA s ((s + 1) * (s + 2))) (laurentMasterB s ((s + 1) * (s + 2))) = onsetDensitySS s r := by
  rw [onsetCurrentSS_eq s r hr hf hs hs3 hs1]
  unfold onsetDensitySS
  field_simp
  all_goals (try ring)

/-- The SS onset density in the boundary variable `u = 1/r`: a Laurent polynomial. -/
def onsetLaurentSS (s u : ℂ) : ℂ := (((27 / 8 : ℂ) * s ^ (2 : ℕ) + (129 / 16 : ℂ) * s ^ (3 : ℕ) + (11 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (5 : ℕ) + (-7 / 8 : ℂ) * s ^ (6 : ℕ) + (-3 / 16 : ℂ) * s ^ (7 : ℕ)) / (2 * s * (s + 3))) * u ^ (3 : ℕ) + (((-3 : ℂ) + (-29 / 2 : ℂ) * s + (-157 / 8 : ℂ) * s ^ (2 : ℕ) + (-11 / 2 : ℂ) * s ^ (3 : ℕ) + (7 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (5 : ℕ)) / (2 * s * (s + 3))) * u + (((7 / 2 : ℂ) * s + (5 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ)) / (2 * s * (s + 3))) * u⁻¹ + (((-1 : ℂ) * s) / (2 * s * (s + 3))) * (u ^ (3 : ℕ))⁻¹

theorem onsetDensitySS_substitution (s u : ℂ) (hu : u ≠ 0) (hu1 : 1 - u ^ (2 : ℕ) ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    (1 - u ^ (2 : ℕ)) * onsetDensitySS s (1 / u) * (1 / (2 * u ^ (3 : ℕ))) = onsetLaurentSS s u := by
  have hr : (1 / u : ℂ) ≠ 0 := one_div_ne_zero hu
  have hf : (1 / u : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
    rw [show (1 / u : ℂ) ^ (2 : ℕ) - 1 = (1 - u ^ (2 : ℕ)) / u ^ (2 : ℕ) by field_simp]
    exact div_ne_zero hu1 (pow_ne_zero _ hu)
  unfold onsetDensitySS onsetLaurentSS
  field_simp
  ring

/-- The continued onset trace of the SS block: the Euler integrals of the dressed density
`z^{(s−3)/2}·onsetDensitySS`, termwise as Gamma quotients. -/
def onsetTraceSS (s : ℂ) : ℂ := (((27 / 8 : ℂ) * s ^ (2 : ℕ) + (129 / 16 : ℂ) * s ^ (3 : ℕ) + (11 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (5 : ℕ) + (-7 / 8 : ℂ) * s ^ (6 : ℕ) + (-3 / 16 : ℂ) * s ^ (7 : ℕ)) / (2 * s * (s + 3))) * contBeta ((s - 3) / 2) (5 / 2) + (((-3 : ℂ) + (-29 / 2 : ℂ) * s + (-157 / 8 : ℂ) * s ^ (2 : ℕ) + (-11 / 2 : ℂ) * s ^ (3 : ℕ) + (7 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (5 : ℕ)) / (2 * s * (s + 3))) * contBeta ((s - 3) / 2) (3 / 2) + (((7 / 2 : ℂ) * s + (5 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ)) / (2 * s * (s + 3))) * contBeta ((s - 3) / 2) (1 / 2) + (((-1 : ℂ) * s) / (2 * s * (s + 3))) * contBeta ((s - 3) / 2) (-1 / 2)

/-- Rational part of the SS onset trace relative to `Γ(1/2)·Γ((s−3)/2)/Γ((s−2)/2)` (with `Γ(1/2) = √π`). -/
def onsetRationalSS (s : ℂ) : ℂ := (((-3 / 2 : ℂ) + (-27 / 16 : ℂ) * s + (-47 / 32 : ℂ) * s ^ (2 : ℕ) + (27 / 4 : ℂ) * s ^ (3 : ℕ) + (7 / 8 : ℂ) * s ^ (4 : ℕ) + (-19 / 16 : ℂ) * s ^ (5 : ℕ) + (-9 / 32 : ℂ) * s ^ (6 : ℕ)) / (s * (s - 2) * (s + 3)))

theorem onsetTraceSS_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs2 : s - 2 ≠ 0) (hs4 : s - 4 ≠ 0)
    (hG : Complex.Gamma ((s - 2) / 2) ≠ 0) :
    onsetTraceSS s = Complex.Gamma (1 / 2) * Complex.Gamma ((s - 3) / 2) / Complex.Gamma ((s - 2) / 2) * onsetRationalSS s := by
  unfold onsetTraceSS onsetRationalSS contBeta
  rw [gamma_five_half, gamma_three_half, gamma_neg_half]
  rw [gamma_shift_five_half s hs hs2, gamma_shift_three_half s hs2, gamma_shift_one_half s, gamma_shift_neg_half s hs4]
  have hsq : Complex.Gamma (1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  generalize hG1 : Complex.Gamma ((s - 3) / 2) = G1
  generalize hG2 : Complex.Gamma ((s - 2) / 2) = G2 at hG ⊢
  generalize hSP : Complex.Gamma (1 / 2) = SP at hsq ⊢
  field_simp
  ring

/-! ## The VV source onset current at the fundamental harmonic -/

theorem onsetPieceVV_qtr0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qtr0 s r ((s + 1) * (s + 2)) * vvSourceTR s r ((s + 1) * (s + 2)) = (((-45 : ℂ) + (-141 : ℂ) * s + (-735 / 4 : ℂ) * s ^ (2 : ℕ) + (-519 / 4 : ℂ) * s ^ (3 : ℕ) + (-209 / 4 : ℂ) * s ^ (4 : ℕ) + (-45 / 4 : ℂ) * s ^ (5 : ℕ) + (-1 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((168 : ℂ) + (197 : ℂ) * s + (-347 / 2 : ℂ) * s ^ (2 : ℕ) + (-399 : ℂ) * s ^ (3 : ℕ) + (-284 : ℂ) * s ^ (4 : ℕ) + (-108 : ℂ) * s ^ (5 : ℕ) + (-45 / 2 : ℂ) * s ^ (6 : ℕ) + (-2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((33 : ℂ) + (410 : ℂ) * s + (2545 / 4 : ℂ) * s ^ (2 : ℕ) + (977 / 4 : ℂ) * s ^ (3 : ℕ) + (-225 / 4 : ℂ) * s ^ (4 : ℕ) + (-193 / 4 : ℂ) * s ^ (5 : ℕ) + (-7 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-36 : ℂ) + (112 : ℂ) * s ^ (2 : ℕ) + (237 / 2 : ℂ) * s ^ (3 : ℕ) + (109 / 2 : ℂ) * s ^ (4 : ℕ) + (27 / 2 : ℂ) * s ^ (5 : ℕ) + (3 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-72 : ℂ) * s + (-132 : ℂ) * s ^ (2 : ℕ) + (-72 : ℂ) * s ^ (3 : ℕ) + (-12 : ℂ) * s ^ (4 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qtr0_lam s r hs hs3 hs1, vvSourceTR_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceVV_qtr1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qtr1 s r ((s + 1) * (s + 2)) * vvSourceTR1 s r ((s + 1) * (s + 2)) = (((315 : ℂ) + (906 : ℂ) * s + (4143 / 4 : ℂ) * s ^ (2 : ℕ) + (2453 / 4 : ℂ) * s ^ (3 : ℕ) + (803 / 4 : ℂ) * s ^ (4 : ℕ) + (139 / 4 : ℂ) * s ^ (5 : ℕ) + (5 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-576 : ℂ) + (-1023 : ℂ) * s + (-137 / 2 : ℂ) * s ^ (2 : ℕ) + (1933 / 2 : ℂ) * s ^ (3 : ℕ) + (1735 / 2 : ℂ) * s ^ (4 : ℕ) + (679 / 2 : ℂ) * s ^ (5 : ℕ) + (65 : ℂ) * s ^ (6 : ℕ) + (5 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((69 : ℂ) + (-703 : ℂ) * s + (-7937 / 4 : ℂ) * s ^ (2 : ℕ) + (-7465 / 4 : ℂ) * s ^ (3 : ℕ) + (-3187 / 4 : ℂ) * s ^ (4 : ℕ) + (-599 / 4 : ℂ) * s ^ (5 : ℕ) + (-6 : ℂ) * s ^ (6 : ℕ) + (1 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((168 : ℂ) + (434 : ℂ) * s + (318 : ℂ) * s ^ (2 : ℕ) + (-19 / 2 : ℂ) * s ^ (3 : ℕ) + (-175 / 2 : ℂ) * s ^ (4 : ℕ) + (-57 / 2 : ℂ) * s ^ (5 : ℕ) + (-5 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((240 : ℂ) * s + (440 : ℂ) * s ^ (2 : ℕ) + (240 : ℂ) * s ^ (3 : ℕ) + (40 : ℂ) * s ^ (4 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qtr1_lam s r hs hs3 hs1, vvSourceTR1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceVV_qtr2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qtr2 s r ((s + 1) * (s + 2)) * vvSourceTR2 s r ((s + 1) * (s + 2)) = (((-270 : ℂ) + (-783 : ℂ) * s + (-900 : ℂ) * s ^ (2 : ℕ) + (-532 : ℂ) * s ^ (3 : ℕ) + (-172 : ℂ) * s ^ (4 : ℕ) + (-29 : ℂ) * s ^ (5 : ℕ) + (-2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((612 : ℂ) + (1380 : ℂ) * s + (851 : ℂ) * s ^ (2 : ℕ) + (-225 : ℂ) * s ^ (3 : ℕ) + (-501 : ℂ) * s ^ (4 : ℕ) + (-239 : ℂ) * s ^ (5 : ℕ) + (-50 : ℂ) * s ^ (6 : ℕ) + (-4 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-270 : ℂ) + (-21 : ℂ) * s + (1187 : ℂ) * s ^ (2 : ℕ) + (1639 : ℂ) * s ^ (3 : ℕ) + (909 : ℂ) * s ^ (4 : ℕ) + (230 : ℂ) * s ^ (5 : ℕ) + (22 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-168 : ℂ) + (-644 : ℂ) * s + (-808 : ℂ) * s ^ (2 : ℕ) + (-408 : ℂ) * s ^ (3 : ℕ) + (-80 : ℂ) * s ^ (4 : ℕ) + (-4 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-180 : ℂ) * s + (-330 : ℂ) * s ^ (2 : ℕ) + (-180 : ℂ) * s ^ (3 : ℕ) + (-30 : ℂ) * s ^ (4 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qtr2_lam s r hs hs3 hs1, vvSourceTR2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceVV_qt0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qt0 s r ((s + 1) * (s + 2)) * vvSourceT s r ((s + 1) * (s + 2)) = (((-99 / 2 : ℂ) * s + (-375 / 2 : ℂ) * s ^ (2 : ℕ) + (-2283 / 8 : ℂ) * s ^ (3 : ℕ) + (-447 / 2 : ℂ) * s ^ (4 : ℕ) + (-381 / 4 : ℂ) * s ^ (5 : ℕ) + (-21 : ℂ) * s ^ (6 : ℕ) + (-15 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-324 : ℂ) + (-540 : ℂ) * s + (-99 : ℂ) * s ^ (2 : ℕ) + (312 : ℂ) * s ^ (3 : ℕ) + (603 / 2 : ℂ) * s ^ (4 : ℕ) + (135 : ℂ) * s ^ (5 : ℕ) + (63 / 2 : ℂ) * s ^ (6 : ℕ) + (3 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((234 : ℂ) + (795 / 2 : ℂ) * s + (147 : ℂ) * s ^ (2 : ℕ) + (-549 / 8 : ℂ) * s ^ (3 : ℕ) + (-165 / 2 : ℂ) * s ^ (4 : ℕ) + (-159 / 4 : ℂ) * s ^ (5 : ℕ) + (-21 / 2 : ℂ) * s ^ (6 : ℕ) + (-9 / 8 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((144 : ℂ) + (291 : ℂ) * s + (387 / 2 : ℂ) * s ^ (2 : ℕ) + (51 : ℂ) * s ^ (3 : ℕ) + (9 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-54 : ℂ) + (-99 : ℂ) * s + (-54 : ℂ) * s ^ (2 : ℕ) + (-9 : ℂ) * s ^ (3 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qt0_lam s r hs hs3 hs1, vvSourceT_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceVV_qt1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qt1 s r ((s + 1) * (s + 2)) * vvSourceT1 s r ((s + 1) * (s + 2)) = (((-540 : ℂ) + (-1512 : ℂ) * s + (-1605 : ℂ) * s ^ (2 : ℕ) + (-783 : ℂ) * s ^ (3 : ℕ) + (-273 / 2 : ℂ) * s ^ (4 : ℕ) + (51 / 2 : ℂ) * s ^ (5 : ℕ) + (27 / 2 : ℂ) * s ^ (6 : ℕ) + (3 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((1260 : ℂ) + (3174 : ℂ) * s + (2934 : ℂ) * s ^ (2 : ℕ) + (1194 : ℂ) * s ^ (3 : ℕ) + (285 / 2 : ℂ) * s ^ (4 : ℕ) + (-93 / 2 : ℂ) * s ^ (5 : ℕ) + (-33 / 2 : ℂ) * s ^ (6 : ℕ) + (-3 / 2 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-684 : ℂ) + (-1488 : ℂ) * s + (-1095 : ℂ) * s ^ (2 : ℕ) + (-297 : ℂ) * s ^ (3 : ℕ) + (12 : ℂ) * s ^ (4 : ℕ) + (21 : ℂ) * s ^ (5 : ℕ) + (3 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-252 : ℂ) + (-570 : ℂ) * s + (-450 : ℂ) * s ^ (2 : ℕ) + (-150 : ℂ) * s ^ (3 : ℕ) + (-18 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((216 : ℂ) + (396 : ℂ) * s + (216 : ℂ) * s ^ (2 : ℕ) + (36 : ℂ) * s ^ (3 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qt1_lam s r hs hs3 hs1, vvSourceT1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceVV_qt2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qt2 s r ((s + 1) * (s + 2)) * vvSourceT2 s r ((s + 1) * (s + 2)) = (((540 : ℂ) + (1656 : ℂ) * s + (2031 : ℂ) * s ^ (2 : ℕ) + (1287 : ℂ) * s ^ (3 : ℕ) + (447 : ℂ) * s ^ (4 : ℕ) + (81 : ℂ) * s ^ (5 : ℕ) + (6 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-1440 : ℂ) + (-4098 : ℂ) * s + (-4545 : ℂ) * s ^ (2 : ℕ) + (-2526 : ℂ) * s ^ (3 : ℕ) + (-741 : ℂ) * s ^ (4 : ℕ) + (-108 : ℂ) * s ^ (5 : ℕ) + (-6 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((1080 : ℂ) + (2754 : ℂ) * s + (2661 : ℂ) * s ^ (2 : ℕ) + (1251 : ℂ) * s ^ (3 : ℕ) + (291 : ℂ) * s ^ (4 : ℕ) + (27 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * (((18 : ℂ) * s + (33 : ℂ) * s ^ (2 : ℕ) + (18 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-180 : ℂ) + (-330 : ℂ) * s + (-180 : ℂ) * s ^ (2 : ℕ) + (-30 : ℂ) * s ^ (3 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qt2_lam s r hs hs3 hs1, vvSourceT2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceVV_qT0 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qT0 s r ((s + 1) * (s + 2)) * vvSourceTF s r ((s + 1) * (s + 2)) = (((341 : ℂ) * s + (1175 : ℂ) * s ^ (2 : ℕ) + (6703 / 4 : ℂ) * s ^ (3 : ℕ) + (5203 / 4 : ℂ) * s ^ (4 : ℕ) + (606 : ℂ) * s ^ (5 : ℕ) + (174 : ℂ) * s ^ (6 : ℕ) + (117 / 4 : ℂ) * s ^ (7 : ℕ) + (9 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((792 : ℂ) + (897 : ℂ) * s + (-3841 / 2 : ℂ) * s ^ (2 : ℕ) + (-8825 / 2 : ℂ) * s ^ (3 : ℕ) + (-7223 / 2 : ℂ) * s ^ (4 : ℕ) + (-1571 : ℂ) * s ^ (5 : ℕ) + (-807 / 2 : ℂ) * s ^ (6 : ℕ) + (-123 / 2 : ℂ) * s ^ (7 : ℕ) + (-9 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-572 : ℂ) + (-1867 : ℂ) * s + (-2304 : ℂ) * s ^ (2 : ℕ) + (-4845 / 4 : ℂ) * s ^ (3 : ℕ) + (-229 / 4 : ℂ) * s ^ (4 : ℕ) + (244 : ℂ) * s ^ (5 : ℕ) + (123 : ℂ) * s ^ (6 : ℕ) + (105 / 4 : ℂ) * s ^ (7 : ℕ) + (9 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-352 : ℂ) + (-945 : ℂ) * s + (-1889 / 2 : ℂ) * s ^ (2 : ℕ) + (-444 : ℂ) * s ^ (3 : ℕ) + (-106 : ℂ) * s ^ (4 : ℕ) + (-15 : ℂ) * s ^ (5 : ℕ) + (-3 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((132 : ℂ) + (342 : ℂ) * s + (318 : ℂ) * s ^ (2 : ℕ) + (126 : ℂ) * s ^ (3 : ℕ) + (18 : ℂ) * s ^ (4 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qT0_lam s r hs hs3 hs1, vvSourceTF_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceVV_qT1 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qT1 s r ((s + 1) * (s + 2)) * vvSourceTF1 s r ((s + 1) * (s + 2)) = (((3960 : ℂ) + (15584 : ℂ) * s + (26106 : ℂ) * s ^ (2 : ℕ) + (24470 : ℂ) * s ^ (3 : ℕ) + (14133 : ℂ) * s ^ (4 : ℕ) + (5186 : ℂ) * s ^ (5 : ℕ) + (1188 : ℂ) * s ^ (6 : ℕ) + (156 : ℂ) * s ^ (7 : ℕ) + (9 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-10032 : ℂ) + (-31888 : ℂ) * s + (-39598 : ℂ) * s ^ (2 : ℕ) + (-23915 : ℂ) * s ^ (3 : ℕ) + (-6661 : ℂ) * s ^ (4 : ℕ) + (-258 : ℂ) * s ^ (5 : ℕ) + (284 : ℂ) * s ^ (6 : ℕ) + (57 : ℂ) * s ^ (7 : ℕ) + (3 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((4840 : ℂ) + (11044 : ℂ) * s + (6750 : ℂ) * s ^ (2 : ℕ) + (-1773 : ℂ) * s ^ (3 : ℕ) + (-3544 : ℂ) * s ^ (4 : ℕ) + (-1456 : ℂ) * s ^ (5 : ℕ) + (-246 : ℂ) * s ^ (6 : ℕ) + (-15 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((2816 : ℂ) + (8484 : ℂ) * s + (9994 : ℂ) * s ^ (2 : ℕ) + (5892 : ℂ) * s ^ (3 : ℕ) + (1836 : ℂ) * s ^ (4 : ℕ) + (288 : ℂ) * s ^ (5 : ℕ) + (18 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-1584 : ℂ) + (-4104 : ℂ) * s + (-3816 : ℂ) * s ^ (2 : ℕ) + (-1512 : ℂ) * s ^ (3 : ℕ) + (-216 : ℂ) * s ^ (4 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qT1_lam s r hs hs3 hs1, vvSourceTF1_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceVV_qT2 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qT2 s r ((s + 1) * (s + 2)) * vvSourceTF2 s r ((s + 1) * (s + 2)) = (((-11880 : ℂ) + (-48292 : ℂ) * s + (-83606 : ℂ) * s ^ (2 : ℕ) + (-80791 : ℂ) * s ^ (3 : ℕ) + (-47816 : ℂ) * s ^ (4 : ℕ) + (-17806 : ℂ) * s ^ (5 : ℕ) + (-4088 : ℂ) * s ^ (6 : ℕ) + (-531 : ℂ) * s ^ (7 : ℕ) + (-30 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((28160 : ℂ) + (104288 : ℂ) * s + (159964 : ℂ) * s ^ (2 : ℕ) + (131882 : ℂ) * s ^ (3 : ℕ) + (63058 : ℂ) * s ^ (4 : ℕ) + (17372 : ℂ) * s ^ (5 : ℕ) + (2480 : ℂ) * s ^ (6 : ℕ) + (114 : ℂ) * s ^ (7 : ℕ) + (-6 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-16720 : ℂ) + (-52736 : ℂ) * s + (-65270 : ℂ) * s ^ (2 : ℕ) + (-39941 : ℂ) * s ^ (3 : ℕ) + (-12072 : ℂ) * s ^ (4 : ℕ) + (-1268 : ℂ) * s ^ (5 : ℕ) + (150 : ℂ) * s ^ (6 : ℕ) + (33 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((-3520 : ℂ) + (-12816 : ℂ) * s + (-18276 : ℂ) * s ^ (2 : ℕ) + (-12834 : ℂ) * s ^ (3 : ℕ) + (-4538 : ℂ) * s ^ (4 : ℕ) + (-714 : ℂ) * s ^ (5 : ℕ) + (-30 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((3960 : ℂ) + (10260 : ℂ) * s + (9540 : ℂ) * s ^ (2 : ℕ) + (3780 : ℂ) * s ^ (3 : ℕ) + (540 : ℂ) * s ^ (4 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qT2_lam s r hs hs3 hs1, vvSourceTF2_lam s r hs hs3 hs1]
  field_simp
  ring

theorem onsetPieceVV_qT3 (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCoeff_qT3 s r ((s + 1) * (s + 2)) * vvSourceTF3 s r ((s + 1) * (s + 2)) = (((7920 : ℂ) + (32928 : ℂ) * s + (58444 : ℂ) * s ^ (2 : ℕ) + (57996 : ℂ) * s ^ (3 : ℕ) + (35272 : ℂ) * s ^ (4 : ℕ) + (13488 : ℂ) * s ^ (5 : ℕ) + (3172 : ℂ) * s ^ (6 : ℕ) + (420 : ℂ) * s ^ (7 : ℕ) + (24 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-21120 : ℂ) + (-82352 : ℂ) * s + (-134352 : ℂ) * s ^ (2 : ℕ) + (-119180 : ℂ) * s ^ (3 : ℕ) + (-62208 : ℂ) * s ^ (4 : ℕ) + (-19136 : ℂ) * s ^ (5 : ℕ) + (-3216 : ℂ) * s ^ (6 : ℕ) + (-228 : ℂ) * s ^ (7 : ℕ)) + r * ((0 : ℂ) + r * (((15840 : ℂ) + (55560 : ℂ) * s + (78684 : ℂ) * s ^ (2 : ℕ) + (57624 : ℂ) * s ^ (3 : ℕ) + (23016 : ℂ) * s ^ (4 : ℕ) + (4752 : ℂ) * s ^ (5 : ℕ) + (396 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((2112 : ℂ) * s + (5472 : ℂ) * s ^ (2 : ℕ) + (5088 : ℂ) * s ^ (3 : ℕ) + (2016 : ℂ) * s ^ (4 : ℕ) + (288 : ℂ) * s ^ (5 : ℕ)) + r * ((0 : ℂ) + r * ((-2640 : ℂ) + (-6840 : ℂ) * s + (-6360 : ℂ) * s ^ (2 : ℕ) + (-2520 : ℂ) * s ^ (3 : ℕ) + (-360 : ℂ) * s ^ (4 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ)) := by
  rw [onsetCoeff_qT3_lam s r hs hs3 hs1, vvSourceTF3_lam s r hs hs3 hs1]
  field_simp
  ring

/-- The source-only onset current of the VV harmonic sources at the fundamental harmonic. -/
def onsetSrcCurrentVV (s r : ℂ) : ℂ := (((1275 / 2 : ℂ) * s + (4619 / 2 : ℂ) * s ^ (2 : ℕ) + (28167 / 8 : ℂ) * s ^ (3 : ℕ) + (11813 / 4 : ℂ) * s ^ (4 : ℕ) + (5919 / 4 : ℂ) * s ^ (5 : ℕ) + (444 : ℂ) * s ^ (6 : ℕ) + (591 / 8 : ℂ) * s ^ (7 : ℕ) + (21 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-2500 : ℂ) + (-9965 : ℂ) * s + (-34015 / 2 : ℂ) * s ^ (2 : ℕ) + (-16303 : ℂ) * s ^ (3 : ℕ) + (-9637 : ℂ) * s ^ (4 : ℕ) + (-3620 : ℂ) * s ^ (5 : ℕ) + (-854 : ℂ) * s ^ (6 : ℕ) + (-118 : ℂ) * s ^ (7 : ℕ) + (-15 / 2 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((3850 : ℂ) + (26701 / 2 : ℂ) * s + (19412 : ℂ) * s ^ (2 : ℕ) + (124809 / 8 : ℂ) * s ^ (3 : ℕ) + (30477 / 4 : ℂ) * s ^ (4 : ℕ) + (9249 / 4 : ℂ) * s ^ (5 : ℕ) + (849 / 2 : ℂ) * s ^ (6 : ℕ) + (353 / 8 : ℂ) * s ^ (7 : ℕ) + (9 / 4 : ℂ) * s ^ (8 : ℕ)) + r * ((0 : ℂ) + r * (((-1200 : ℂ) + (-3636 : ℂ) * s + (-4356 : ℂ) * s ^ (2 : ℕ) + (-2678 : ℂ) * s ^ (3 : ℕ) + (-1831 / 2 : ℂ) * s ^ (4 : ℕ) + (-172 : ℂ) * s ^ (5 : ℕ) + (-29 / 2 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * ((-150 : ℂ) + (-387 : ℂ) * s + (-358 : ℂ) * s ^ (2 : ℕ) + (-141 : ℂ) * s ^ (3 : ℕ) + (-20 : ℂ) * s ^ (4 : ℕ)))))))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ) * s * (s + 3) ^ (2 : ℕ))

theorem onsetSrcCurrentVV_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetSrcCurrent s r ((s + 1) * (s + 2)) (vvSourceTR s r ((s + 1) * (s + 2))) (vvSourceTR1 s r ((s + 1) * (s + 2))) (vvSourceTR2 s r ((s + 1) * (s + 2))) (vvSourceT s r ((s + 1) * (s + 2))) (vvSourceT1 s r ((s + 1) * (s + 2))) (vvSourceT2 s r ((s + 1) * (s + 2))) (vvSourceTF s r ((s + 1) * (s + 2))) (vvSourceTF1 s r ((s + 1) * (s + 2))) (vvSourceTF2 s r ((s + 1) * (s + 2))) (vvSourceTF3 s r ((s + 1) * (s + 2))) = onsetSrcCurrentVV s r := by
  unfold onsetSrcCurrent
  rw [onsetPieceVV_qtr0 s r hr hf hs hs3 hs1, onsetPieceVV_qtr1 s r hr hf hs hs3 hs1, onsetPieceVV_qtr2 s r hr hf hs hs3 hs1, onsetPieceVV_qt0 s r hr hf hs hs3 hs1, onsetPieceVV_qt1 s r hr hf hs hs3 hs1, onsetPieceVV_qt2 s r hr hf hs hs3 hs1, onsetPieceVV_qT0 s r hr hf hs hs3 hs1, onsetPieceVV_qT1 s r hr hf hs hs3 hs1, onsetPieceVV_qT2 s r hr hf hs hs3 hs1, onsetPieceVV_qT3 s r hr hf hs hs3 hs1]
  unfold onsetSrcCurrentVV
  simp only [← add_div]
  ring

/-! ## The VV `++` Laurent response against the `−` mode -/

/-- The onset current with the VV Laurent coefficients at their actual values. -/
theorem onsetCurrentVV_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    onsetCurrentVV s r ((s + 1) * (s + 2)) (vvLaurentMasterA s ((s + 1) * (s + 2))) (vvLaurentMasterB s ((s + 1) * (s + 2))) = (((51 / 2 : ℂ) * s + (271 / 4 : ℂ) * s ^ (2 : ℕ) + (137 / 2 : ℂ) * s ^ (3 : ℕ) + (67 / 2 : ℂ) * s ^ (4 : ℕ) + (8 : ℂ) * s ^ (5 : ℕ) + (3 / 4 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-132 : ℂ) + (-242 : ℂ) * s + (-151 : ℂ) * s ^ (2 : ℕ) + (-95 / 2 : ℂ) * s ^ (3 : ℕ) + (-13 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-22 : ℂ) + (-30 : ℂ) * s + (-8 : ℂ) * s ^ (2 : ℕ)))))) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) * (s + 3)) := by
  unfold onsetCurrentVV
  rw [onsetSrcCurrentVV_eq s r hr hf hs hs3 hs1, vvLaurentA_lam s hs hs3 hs1, vvLaurentB_lam s hs hs3, onsetCurrent_lauI1_lam s r hs hs3 hs1, onsetCurrent_lauI3_lam s r hs hs3 hs1]
  unfold onsetSrcCurrentVV
  field_simp
  ring

/-- Coordinate density `r²·(onset current)` of the VV block: numerator even in `r`, simple horizon pole. -/
def onsetDensityVV (s r : ℂ) : ℂ := (((51 / 2 : ℂ) * s + (271 / 4 : ℂ) * s ^ (2 : ℕ) + (137 / 2 : ℂ) * s ^ (3 : ℕ) + (67 / 2 : ℂ) * s ^ (4 : ℕ) + (8 : ℂ) * s ^ (5 : ℕ) + (3 / 4 : ℂ) * s ^ (6 : ℕ)) + r * ((0 : ℂ) + r * (((-132 : ℂ) + (-242 : ℂ) * s + (-151 : ℂ) * s ^ (2 : ℕ) + (-95 / 2 : ℂ) * s ^ (3 : ℕ) + (-13 / 2 : ℂ) * s ^ (4 : ℕ)) + r * ((0 : ℂ) + r * ((-22 : ℂ) + (-30 : ℂ) * s + (-8 : ℂ) * s ^ (2 : ℕ)))))) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) * (s + 3))

theorem onsetDensityVV_eq (s r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    r ^ (2 : ℕ) * onsetCurrentVV s r ((s + 1) * (s + 2)) (vvLaurentMasterA s ((s + 1) * (s + 2))) (vvLaurentMasterB s ((s + 1) * (s + 2))) = onsetDensityVV s r := by
  rw [onsetCurrentVV_eq s r hr hf hs hs3 hs1]
  unfold onsetDensityVV
  field_simp
  all_goals (try ring)

/-- The VV onset density in the boundary variable `u = 1/r`: a Laurent polynomial. -/
def onsetLaurentVV (s u : ℂ) : ℂ := (((51 / 2 : ℂ) * s + (271 / 4 : ℂ) * s ^ (2 : ℕ) + (137 / 2 : ℂ) * s ^ (3 : ℕ) + (67 / 2 : ℂ) * s ^ (4 : ℕ) + (8 : ℂ) * s ^ (5 : ℕ) + (3 / 4 : ℂ) * s ^ (6 : ℕ)) / (2 * (s + 3))) * u ^ (3 : ℕ) + (((-132 : ℂ) + (-242 : ℂ) * s + (-151 : ℂ) * s ^ (2 : ℕ) + (-95 / 2 : ℂ) * s ^ (3 : ℕ) + (-13 / 2 : ℂ) * s ^ (4 : ℕ)) / (2 * (s + 3))) * u + (((-22 : ℂ) + (-30 : ℂ) * s + (-8 : ℂ) * s ^ (2 : ℕ)) / (2 * (s + 3))) * u⁻¹

theorem onsetDensityVV_substitution (s u : ℂ) (hu : u ≠ 0) (hu1 : 1 - u ^ (2 : ℕ) ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    (1 - u ^ (2 : ℕ)) * onsetDensityVV s (1 / u) * (1 / (2 * u ^ (3 : ℕ))) = onsetLaurentVV s u := by
  have hr : (1 / u : ℂ) ≠ 0 := one_div_ne_zero hu
  have hf : (1 / u : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
    rw [show (1 / u : ℂ) ^ (2 : ℕ) - 1 = (1 - u ^ (2 : ℕ)) / u ^ (2 : ℕ) by field_simp]
    exact div_ne_zero hu1 (pow_ne_zero _ hu)
  unfold onsetDensityVV onsetLaurentVV
  field_simp
  ring

/-- The continued onset trace of the VV block: the Euler integrals of the dressed density
`z^{(s−3)/2}·onsetDensityVV`, termwise as Gamma quotients. -/
def onsetTraceVV (s : ℂ) : ℂ := (((51 / 2 : ℂ) * s + (271 / 4 : ℂ) * s ^ (2 : ℕ) + (137 / 2 : ℂ) * s ^ (3 : ℕ) + (67 / 2 : ℂ) * s ^ (4 : ℕ) + (8 : ℂ) * s ^ (5 : ℕ) + (3 / 4 : ℂ) * s ^ (6 : ℕ)) / (2 * (s + 3))) * contBeta ((s - 3) / 2) (5 / 2) + (((-132 : ℂ) + (-242 : ℂ) * s + (-151 : ℂ) * s ^ (2 : ℕ) + (-95 / 2 : ℂ) * s ^ (3 : ℕ) + (-13 / 2 : ℂ) * s ^ (4 : ℕ)) / (2 * (s + 3))) * contBeta ((s - 3) / 2) (3 / 2) + (((-22 : ℂ) + (-30 : ℂ) * s + (-8 : ℂ) * s ^ (2 : ℕ)) / (2 * (s + 3))) * contBeta ((s - 3) / 2) (1 / 2)

/-- Rational part of the VV onset trace relative to `Γ(1/2)·Γ((s−3)/2)/Γ((s−2)/2)` (with `Γ(1/2) = √π`). -/
def onsetRationalVV (s : ℂ) : ℂ := (((-23 / 4 : ℂ) + (-3 / 8 : ℂ) * s + (81 / 4 : ℂ) * s ^ (2 : ℕ) + (45 / 2 : ℂ) * s ^ (3 : ℕ) + (35 / 4 : ℂ) * s ^ (4 : ℕ) + (9 / 8 : ℂ) * s ^ (5 : ℕ)) / ((s - 2) * (s + 3)))

theorem onsetTraceVV_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs2 : s - 2 ≠ 0) (hs4 : s - 4 ≠ 0)
    (hG : Complex.Gamma ((s - 2) / 2) ≠ 0) :
    onsetTraceVV s = Complex.Gamma (1 / 2) * Complex.Gamma ((s - 3) / 2) / Complex.Gamma ((s - 2) / 2) * onsetRationalVV s := by
  unfold onsetTraceVV onsetRationalVV contBeta
  rw [gamma_five_half, gamma_three_half]
  rw [gamma_shift_five_half s hs hs2, gamma_shift_three_half s hs2, gamma_shift_one_half s]
  have hsq : Complex.Gamma (1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  generalize hG1 : Complex.Gamma ((s - 3) / 2) = G1
  generalize hG2 : Complex.Gamma ((s - 2) / 2) = G2 at hG ⊢
  generalize hSP : Complex.Gamma (1 / 2) = SP at hsq ⊢
  field_simp
  ring

end
end RHTower.D4BMScalarStream
