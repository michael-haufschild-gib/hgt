import GaloisForLFunctions.RHTower.XiCTaylorThetaTailTelescope
import GaloisForLFunctions.RHTower.XiCTaylorOrientedCoefficientCurrent

open Complex Real Polynomial

namespace RHTower

noncomputable section

def evenMagnitudeLift (B : Polynomial ℝ) : Polynomial ℂ :=
  (B.map (algebraMap ℝ ℂ)).comp (-(X ^ 2))

theorem evenMagnitudeLift_eval (B : Polynomial ℝ) (z : ℂ) :
    (evenMagnitudeLift B).eval z = B.eval₂ (algebraMap ℝ ℂ) (-z ^ 2) := by
  simp [evenMagnitudeLift, Polynomial.aeval_def]

theorem xiCTaylorPolynomial_oddCutoff_eq_evenMagnitudeLift (d : ℕ) :
    xiCTaylorPolynomial (2 * d + 1) =
      evenMagnitudeLift (xiCTaylorEvenMagnitudePolynomial d) := by
  apply Polynomial.funext
  intro z
  rw [xiCTaylorPolynomial_eval, evenMagnitudeLift_eval,
    xiCTaylorApprox_oddCutoff_eq_evenMagnitude_eval]

theorem orientedPolynomialCurrent_monomial
    (a : ℝ) (m : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (C (a : ℂ) * X ^ m) z =
      -(m : ℝ) * a ^ 2 * Complex.normSq z ^ (m - 1) * z.im := by
  cases m with
  | zero => simp [orientedPolynomialCurrent]
  | succ k =>
      unfold orientedPolynomialCurrent
      simp only [derivative_mul, derivative_C, zero_mul, derivative_X_pow,
        eval_mul, eval_C, eval_pow, eval_X, zero_add,
        map_mul, map_pow, Nat.cast_succ, Nat.succ_sub_one]
      have hpow : z ^ k * (starRingEnd ℂ z) ^ k = (Complex.normSq z : ℂ) ^ k := by
        rw [← mul_pow, Complex.mul_conj]
      rw [pow_succ]
      rw [Complex.conj_ofReal]
      rw [show (↑a * ((↑k + 1) * z ^ k)) *
          (↑a * ((starRingEnd ℂ) z ^ k * (starRingEnd ℂ) z)) =
          (((((k : ℝ) + 1) * a ^ 2 * Complex.normSq z ^ k : ℝ) : ℂ) *
            (starRingEnd ℂ z)) by
        rw [show (↑a * ((↑k + 1) * z ^ k)) *
            (↑a * ((starRingEnd ℂ) z ^ k * (starRingEnd ℂ) z)) =
            ((↑k + 1) * (↑a * ↑a)) *
              (z ^ k * (starRingEnd ℂ z) ^ k) * (starRingEnd ℂ z) by ring,
          hpow]
        push_cast
        ring]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.conj_im, zero_mul]
      ring

theorem orientedPolynomialCurrent_monomial_nonpos
    (a : ℝ) (m : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    orientedPolynomialCurrent (C (a : ℂ) * X ^ m) z ≤ 0 := by
  rw [orientedPolynomialCurrent_monomial]
  have hprod : 0 ≤ (m : ℝ) * a ^ 2 * Complex.normSq z ^ (m - 1) * z.im := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg a))
      (pow_nonneg (Complex.normSq_nonneg z) _)) hz
  linarith

theorem orientedPolynomialCurrent_sub_exact
    (U E : Polynomial ℂ) (z : ℂ) :
    orientedPolynomialCurrent (U - E) z =
      orientedPolynomialCurrent U z -
        (U.derivative.eval z * (starRingEnd ℂ) (E.eval z)).im -
        (E.derivative.eval z * (starRingEnd ℂ) (U.eval z)).im +
        orientedPolynomialCurrent E z := by
  simp only [orientedPolynomialCurrent, eval_sub, map_sub]
  simp only [sub_mul, mul_sub, Complex.sub_im]
  ring

theorem orientedPolynomialCurrent_sub_le
    (U E : Polynomial ℂ) (z : ℂ)
    (hE : orientedPolynomialCurrent E z ≤ 0) :
    orientedPolynomialCurrent (U - E) z ≤
      orientedPolynomialCurrent U z +
        ‖U.derivative.eval z‖ * ‖E.eval z‖ +
        ‖E.derivative.eval z‖ * ‖U.eval z‖ := by
  rw [orientedPolynomialCurrent_sub_exact]
  have hUE : -(U.derivative.eval z * (starRingEnd ℂ) (E.eval z)).im ≤
      ‖U.derivative.eval z‖ * ‖E.eval z‖ := by
    calc
      -(U.derivative.eval z * (starRingEnd ℂ) (E.eval z)).im ≤
          |(U.derivative.eval z * (starRingEnd ℂ) (E.eval z)).im| :=
        neg_le_abs _
      _ ≤ ‖U.derivative.eval z * (starRingEnd ℂ) (E.eval z)‖ :=
        Complex.abs_im_le_norm _
      _ = ‖U.derivative.eval z‖ * ‖E.eval z‖ := by simp
  have hEU : -(E.derivative.eval z * (starRingEnd ℂ) (U.eval z)).im ≤
      ‖E.derivative.eval z‖ * ‖U.eval z‖ := by
    calc
      -(E.derivative.eval z * (starRingEnd ℂ) (U.eval z)).im ≤
          |(E.derivative.eval z * (starRingEnd ℂ) (U.eval z)).im| :=
        neg_le_abs _
      _ ≤ ‖E.derivative.eval z * (starRingEnd ℂ) (U.eval z)‖ :=
        Complex.abs_im_le_norm _
      _ = ‖E.derivative.eval z‖ * ‖U.eval z‖ := by simp
  linarith

/-- The source-side theta-tail core after the even coordinate `w = -z²`. -/
def xiCTaylorThetaTailCorePolynomial (d : ℕ) : Polynomial ℂ :=
  evenMagnitudeLift
    (C (1 / 2) + (X - C (1 / 4)) * thetaCuspTailEvenPolynomial d)

/-- The one top coefficient omitted from the theta-tail core. -/
def xiCTaylorThetaTailTopDefectPolynomial (d : ℕ) : Polynomial ℂ :=
  C ((((-1 : ℝ) ^ (d + 1) *
      ((1 / 4 : ℝ) * thetaCuspTailEvenCoefficient (d + 1)) : ℝ) : ℂ)) *
    X ^ (2 * (d + 1))

theorem evenMagnitudeLift_topDefect (d : ℕ) :
    evenMagnitudeLift
        (C ((1 / 4 : ℝ) * thetaCuspTailEvenCoefficient (d + 1)) * X ^ (d + 1)) =
      xiCTaylorThetaTailTopDefectPolynomial d := by
  apply Polynomial.funext
  intro z
  simp only [evenMagnitudeLift_eval, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    xiCTaylorThetaTailTopDefectPolynomial, eval_mul, eval_C, eval_pow, eval_X]
  push_cast
  rw [neg_pow, ← pow_mul]
  ring_nf
  ac_rfl

/-- Exact source-side splitting of the canonical odd-cutoff Xi Taylor polynomial. -/
theorem xiCTaylorPolynomial_oddCutoff_succ_eq_thetaTailCore_sub_topDefect (d : ℕ) :
    xiCTaylorPolynomial (2 * (d + 1) + 1) =
      xiCTaylorThetaTailCorePolynomial d - xiCTaylorThetaTailTopDefectPolynomial d := by
  apply Polynomial.funext
  intro z
  rw [xiCTaylorPolynomial_eval,
    xiCTaylorApprox_oddCutoff_eq_evenMagnitude_eval]
  rw [eval_sub, xiCTaylorThetaTailCorePolynomial, evenMagnitudeLift_eval]
  rw [xiCTaylorEvenMagnitudePolynomial_succ, eval₂_sub]
  congr 1
  rw [← evenMagnitudeLift_topDefect d, evenMagnitudeLift_eval]

theorem xiCTaylorThetaTailTopDefect_current_nonpos
    (d : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    orientedPolynomialCurrent (xiCTaylorThetaTailTopDefectPolynomial d) z ≤ 0 := by
  exact orientedPolynomialCurrent_monomial_nonpos
    (((-1 : ℝ) ^ (d + 1)) *
      ((1 / 4 : ℝ) * thetaCuspTailEvenCoefficient (d + 1)))
    (2 * (d + 1)) hz

/-- The explicit top defect has favorable current; only its two cross-interference terms can
increase the current of the canonical Taylor section. -/
theorem xiCTaylor_orientedCurrent_le_thetaTailCore_add_interference
    (d : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    orientedPolynomialCurrent (xiCTaylorPolynomial (2 * (d + 1) + 1)) z ≤
      orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z +
        ‖(xiCTaylorThetaTailCorePolynomial d).derivative.eval z‖ *
          ‖(xiCTaylorThetaTailTopDefectPolynomial d).eval z‖ +
        ‖(xiCTaylorThetaTailTopDefectPolynomial d).derivative.eval z‖ *
          ‖(xiCTaylorThetaTailCorePolynomial d).eval z‖ := by
  rw [xiCTaylorPolynomial_oddCutoff_succ_eq_thetaTailCore_sub_topDefect]
  exact orientedPolynomialCurrent_sub_le _ _ _
    (xiCTaylorThetaTailTopDefect_current_nonpos d hz)

end
end RHTower
