import GaloisForLFunctions.RHTower.GammaHorizontalLogShift
import GaloisForLFunctions.RHTower.ZetaChiHardyPhase
import GaloisForLFunctions.RHTower.BourgainPhasePerturbation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Complex MeasureTheory Filter Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem conj_exp_div_exp (z : ℂ) :
    (starRingEnd ℂ) (Complex.exp z) / Complex.exp z =
      bourgainOscillation (-2 * z.im) := by
  rw [← Complex.exp_conj, ← Complex.exp_sub]
  unfold bourgainOscillation
  congr 1
  apply Complex.ext <;> simp
  ring

/-- The critical chi factor is its elementary pi phase times an ordinary
Gamma conjugate ratio. -/
theorem zetaChi_line_eq_pi_phase_gamma_ratio (t : ℝ) :
    zetaChi (linePt t) = bourgainOscillation (t * Real.log Real.pi) *
      ((starRingEnd ℂ) (Complex.Gamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * I)) /
        Complex.Gamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * I)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [zetaChi, one_sub_linePt, Gammaℝ_conj, Gammaℝ_def,
    Complex.cpow_def_of_ne_zero hp, map_mul, mul_div_mul_comm,
    conj_exp_div_exp]
  have hs : linePt t / 2 = (1 / 4 : ℂ) + (t / 2 : ℝ) * I := by
    unfold linePt
    push_cast
    ring
  rw [hs, ← Complex.ofReal_log Real.pi_pos.le]
  congr 2
  simp [linePt]
  ring


private theorem conjugate_ratio_mul (a b : ℂ) :
    (starRingEnd ℂ) (a * b) / (a * b) =
      ((starRingEnd ℂ) a / a) * ((starRingEnd ℂ) b / b) := by
  rw [map_mul, mul_div_mul_comm]

private theorem conjugate_ratio_div (a b : ℂ) :
    (starRingEnd ℂ) (a / b) / (a / b) =
      ((starRingEnd ℂ) a / a) / ((starRingEnd ℂ) b / b) := by
  simp only [map_div₀]
  ring

/-- Exact doubling law for the physical chi phase. Its correction is the
literal difference of two horizontal logarithmic Gamma shifts. -/
theorem zetaChi_line_double_phase (t : ℝ) :
    zetaChi (linePt (2 * t)) = zetaChi (linePt t) ^ 2 *
      bourgainOscillation (-2 * t * Real.log 2) *
      bourgainOscillation (-2 * ((gammaHorizontalLogShift (1 / 4) (1 / 2) (t / 2)).im -
        (gammaHorizontalLogShift (1 / 4) (1 / 4) t).im)) := by
  let z : ℂ := 1 / 4 + (t / 2 : ℝ) * I
  let w : ℂ := 1 / 4 + (t : ℂ) * I
  let A : ℂ := Complex.Gamma z
  let B : ℂ := Complex.Gamma w
  let U := gammaHorizontalLogShift (1 / 4) (1 / 2) (t / 2)
  let V := gammaHorizontalLogShift (1 / 4) (1 / 4) t
  let K : ℂ := (Real.log 2 : ℂ) * (1 - 2 * z)
  have hA : Complex.Gamma (z + 1 / 2) = A * Complex.exp U := by
    have h := Gamma_horizontal_eq_exp_logShift (σ := 1 / 4) (lam := 1 / 2)
      (by norm_num) (by norm_num) (t / 2)
    have he : z + 1 / 2 = (((1 / 4 + 1 / 2 : ℝ) : ℂ) + (t / 2 : ℝ) * I) := by
      dsimp only [z]
      push_cast
      ring
    rw [he]
    simpa [A, U, z] using h
  have hB : Complex.Gamma (2 * z) = B * Complex.exp V := by
    have h := Gamma_horizontal_eq_exp_logShift (σ := 1 / 4) (lam := 1 / 4)
      (by norm_num) (by norm_num) t
    have he : 2 * z = (((1 / 4 + 1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) := by
      dsimp only [z]
      push_cast
      ring
    rw [he]
    simpa [B, V, w] using h
  have hdup := Complex.Gamma_mul_Gamma_add_half z
  rw [hA, hB, Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)] at hdup
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog] at hdup
  have hD : Complex.exp V * Complex.exp K * (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hBeq : B = A ^ 2 * Complex.exp U /
      (Complex.exp V * Complex.exp K * (Real.sqrt Real.pi : ℂ)) := by
    apply (eq_div_iff hD).2
    dsimp only [A, K]
    linear_combination -hdup
  have hq : (starRingEnd ℂ) B / B =
      ((starRingEnd ℂ) A / A) ^ 2 *
      bourgainOscillation (-2 * U.im) /
        (bourgainOscillation (-2 * V.im) * bourgainOscillation (-2 * K.im)) := by
    rw [hBeq, conjugate_ratio_div, conjugate_ratio_mul,
      conjugate_ratio_mul, conjugate_ratio_mul]
    simp only [map_pow, div_pow, conj_exp_div_exp, Complex.conj_ofReal]
    have hp : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
    rw [div_self hp, mul_one]
  have hK : K.im = -t * Real.log 2 := by
    have he : K = ((Real.log 2 / 2 : ℝ) : ℂ) - ((t * Real.log 2 : ℝ) : ℂ) * I := by
      dsimp only [K, z]
      push_cast
      ring
    rw [he]
    simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
      zero_mul, add_zero, zero_sub]
    ring
  rw [hK] at hq
  have h2 : (2 * t) / 2 = t := by ring
  rw [zetaChi_line_eq_pi_phase_gamma_ratio, h2]
  change bourgainOscillation (2 * t * Real.log Real.pi) *
    ((starRingEnd ℂ) B / B) = _
  rw [hq, zetaChi_line_eq_pi_phase_gamma_ratio]
  change bourgainOscillation (2 * t * Real.log Real.pi) *
    (((starRingEnd ℂ) A / A) ^ 2 * bourgainOscillation (-2 * U.im) /
      (bourgainOscillation (-2 * V.im) * bourgainOscillation (-2 * (-t * Real.log 2)))) =
    (bourgainOscillation (t * Real.log Real.pi) * ((starRingEnd ℂ) A / A)) ^ 2 *
      bourgainOscillation (-2 * t * Real.log 2) * bourgainOscillation (-2 * (U.im - V.im))
  have hephase : bourgainOscillation (2 * t * Real.log Real.pi) *
      bourgainOscillation (-2 * U.im) /
        (bourgainOscillation (-2 * V.im) * bourgainOscillation (-2 * (-t * Real.log 2))) =
      bourgainOscillation (t * Real.log Real.pi) ^ 2 *
        bourgainOscillation (-2 * t * Real.log 2) *
        bourgainOscillation (-2 * (U.im - V.im)) := by
    unfold bourgainOscillation
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub,
      ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ((starRingEnd ℂ) A / A) ^ 2 *
        (bourgainOscillation (2 * t * Real.log Real.pi) * bourgainOscillation (-2 * U.im) /
          (bourgainOscillation (-2 * V.im) * bourgainOscillation (-2 * (-t * Real.log 2)))) := by ring
    _ = ((starRingEnd ℂ) A / A) ^ 2 *
        (bourgainOscillation (t * Real.log Real.pi) ^ 2 *
          bourgainOscillation (-2 * t * Real.log 2) *
          bourgainOscillation (-2 * (U.im - V.im))) := by rw [hephase]
    _ = _ := by ring



end RHTower
