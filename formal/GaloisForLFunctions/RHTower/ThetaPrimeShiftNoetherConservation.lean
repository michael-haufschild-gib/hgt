import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherCurrent
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Conservation of the complete arithmetic shift current

Superexponential theta decay controls each prime link uniformly in its
observation point. Both its current and its derivative have a summable
von Mangoldt Dirichlet-series majorant. Consequently the full current is
the actual differentiated sum of all prime-power link currents.

The completed theta source equation conserves the prime current corrected
by Gamma/pole exchange and the multiplication channel. No positive-energy
or critical-line condition is used in this conservation law.
-/

open MeasureTheory

noncomputable section

namespace RHTower.ThetaSourceWard

private def primeShiftMajorant (n : ℕ) : ℝ :=
  ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 + 1) n‖

private theorem summable_primeShiftMajorant : Summable primeShiftMajorant := by
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := 1 / 2 + 1) (by norm_num)).norm

private theorem primeShiftMajorant_eq (n : ℕ) :
    ‖primeCoefficient n‖ * Real.exp (-Real.log n) = primeShiftMajorant n := by
  have h := congrArg norm (primeCoefficient_laplace (1 : ℂ) n)
  simpa only [norm_mul, Complex.norm_exp, neg_mul, one_mul,
    Complex.neg_re, Complex.ofReal_re, primeShiftMajorant] using h

private theorem exp_link_length_bound (l : ℝ) :
    Real.exp (-2 * |l|) * |l| ≤ Real.exp (-l) := by
  have h := Real.mul_exp_neg_le_exp_neg_one |l|
  have he : Real.exp (-1) ≤ (1 : ℝ) := Real.exp_le_one_iff.mpr (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left (h.trans he) (Real.exp_pos (-|l|)).le
  have heq : Real.exp (-|l|) * (|l| * Real.exp (-|l|)) =
      Real.exp (-2 * |l|) * |l| := by
    calc
      _ = (Real.exp (-|l|) * Real.exp (-|l|)) * |l| := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  rw [heq, mul_one] at hmul
  exact hmul.trans (Real.exp_le_exp.mpr (neg_le_neg (le_abs_self l)))

private theorem exists_primeShift_uniform_bounds (S T : ThetaSource) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n x, ‖primeShiftNoetherCurrent S T n x‖ ≤ C * primeShiftMajorant n) ∧
      (∀ n x, ‖(T.k x : ℂ) * primeSourceTerm S n x -
          (S.k x : ℂ) * primeSourceTerm T n (-x)‖ ≤ 2 * C * primeShiftMajorant n) := by
  obtain ⟨A, hA, hS⟩ := S.norm_le (M := 2)
  obtain ⟨B, hB, hT⟩ := T.norm_le (M := 2)
  have hAB : 0 < A * B := mul_pos hA hB
  have hlink (n : ℕ) (y : ℝ) :
      ‖primeShiftLinkDensity S T n y‖ ≤ A * B * Real.exp (-2 * |Real.log n|) := by
    have ht : |Real.log n| ≤ |y| + |y - Real.log n| := by
      calc
        _ = |y + -(y - Real.log n)| := by congr 1; ring
        _ ≤ |y| + |-(y - Real.log n)| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    have he : Real.exp (-(2 * |y|)) * Real.exp (-(2 * |y - Real.log n|)) ≤
        Real.exp (-2 * |Real.log n|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    rw [primeShiftLinkDensity, norm_mul]
    calc
      _ ≤ (A * Real.exp (-(2 * |y|))) *
          (B * Real.exp (-(2 * |y - Real.log n|))) :=
        mul_le_mul (hS y) (hT (y - Real.log n)) (norm_nonneg _)
          (mul_nonneg hA.le (Real.exp_pos _).le)
      _ = A * B * (Real.exp (-(2 * |y|)) *
          Real.exp (-(2 * |y - Real.log n|))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he hAB.le
  refine ⟨A * B, hAB, ?_, ?_⟩
  · intro n x
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x) (b := x + Real.log n) (fun y _ => hlink n y)
    simp only [add_sub_cancel_left] at hi
    rw [primeShiftNoetherCurrent, norm_mul]
    calc
      _ ≤ ‖primeCoefficient n‖ *
          ((A * B * Real.exp (-2 * |Real.log n|)) * |Real.log n|) :=
        mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ = (A * B * ‖primeCoefficient n‖) *
          (Real.exp (-2 * |Real.log n|) * |Real.log n|) := by ring
      _ ≤ (A * B * ‖primeCoefficient n‖) * Real.exp (-Real.log n) :=
        mul_le_mul_of_nonneg_left (exp_link_length_bound _)
          (mul_nonneg hAB.le (norm_nonneg _))
      _ = A * B * primeShiftMajorant n := by
        rw [mul_assoc, primeShiftMajorant_eq]
  · intro n x
    have ht : T.k (-x + Real.log n) = T.k (x - Real.log n) := by
      rw [← T.even' (x - Real.log n)]
      congr 1
      ring
    have hrewrite : (T.k x : ℂ) * primeSourceTerm S n x -
        (S.k x : ℂ) * primeSourceTerm T n (-x) =
      primeCoefficient n * (primeShiftLinkDensity S T n (x + Real.log n) -
        primeShiftLinkDensity S T n x) := by
      simp only [primeSourceTerm, primeShiftLinkDensity, add_sub_cancel_right, ht]
      ring
    have he : Real.exp (-2 * |Real.log n|) ≤ Real.exp (-Real.log n) := by
      apply Real.exp_le_exp.mpr
      have := le_abs_self (Real.log n)
      have := abs_nonneg (Real.log n)
      linarith
    rw [hrewrite, norm_mul]
    calc
      _ ≤ ‖primeCoefficient n‖ *
          (‖primeShiftLinkDensity S T n (x + Real.log n)‖ +
            ‖primeShiftLinkDensity S T n x‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖primeCoefficient n‖ *
          (2 * (A * B * Real.exp (-2 * |Real.log n|))) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        linarith [hlink n (x + Real.log n), hlink n x]
      _ = (2 * (A * B) * ‖primeCoefficient n‖) * Real.exp (-2 * |Real.log n|) := by ring
      _ ≤ (2 * (A * B) * ‖primeCoefficient n‖) * Real.exp (-Real.log n) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = 2 * (A * B) * primeShiftMajorant n := by
        rw [mul_assoc, primeShiftMajorant_eq]

/-- Every arithmetic link current is included in an absolutely convergent sum. -/
theorem summable_primeShiftNoetherCurrent (S T : ThetaSource) (x : ℝ) :
    Summable (fun n => primeShiftNoetherCurrent S T n x) := by
  obtain ⟨C, _, hb, _⟩ := exists_primeShift_uniform_bounds S T
  exact Summable.of_norm_bounded (summable_primeShiftMajorant.mul_left C) (fun n => hb n x)

/-- One summable majorant controls every observation point, including boundary limits. -/
theorem exists_summable_primeShiftNoetherCurrent_bound (S T : ThetaSource) :
    ∃ b : ℕ → ℝ, Summable b ∧ ∀ n x, ‖primeShiftNoetherCurrent S T n x‖ ≤ b n := by
  obtain ⟨C, _, hb, _⟩ := exists_primeShift_uniform_bounds S T
  exact ⟨fun n => C * primeShiftMajorant n, summable_primeShiftMajorant.mul_left C, hb⟩

def fullPrimeShiftNoetherCurrent (S T : ThetaSource) (x : ℝ) : ℂ :=
  ∑' n : ℕ, primeShiftNoetherCurrent S T n x

/-- The full arithmetic current has its literal source/adjoint divergence. -/
theorem hasDerivAt_fullPrimeShiftNoetherCurrent (S T : ThetaSource) (x : ℝ) :
    HasDerivAt (fullPrimeShiftNoetherCurrent S T) (fullPrimeShiftWardDivergence S T x) x := by
  obtain ⟨C, _, _, hb⟩ := exists_primeShift_uniform_bounds S T
  rw [fullPrimeShiftWardDivergence_eq_tsum]
  exact hasDerivAt_tsum (summable_primeShiftMajorant.mul_left (2 * C))
    (hasDerivAt_primeShiftNoetherCurrent S T) hb (summable_primeShiftNoetherCurrent S T 0) x

theorem continuous_fullPrimeShiftWardDivergence (S T : ThetaSource) :
    Continuous (fullPrimeShiftWardDivergence S T) := by
  exact ((Complex.continuous_ofReal.comp T.cont).mul (fullPrimeSource_continuous S)).sub
    ((Complex.continuous_ofReal.comp S.cont).mul
      ((fullPrimeSource_continuous T).comp continuous_neg))

/-- The complete prime current's change equals its exact arithmetic exchange integral. -/
theorem fullPrimeShiftNoetherCurrent_sub (S T : ThetaSource) (x : ℝ) :
    fullPrimeShiftNoetherCurrent S T x - fullPrimeShiftNoetherCurrent S T 0 =
      ∫ y in (0 : ℝ)..x, fullPrimeShiftWardDivergence S T y := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_fullPrimeShiftNoetherCurrent S T y)
    ((continuous_fullPrimeShiftWardDivergence S T).intervalIntegrable 0 x)

/-- Prime, Gamma/pole, and multiplication channels carry one conserved arithmetic current. -/
theorem completeTheta_primeShiftNoether_conservation (x : ℝ) :
    fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x -
      (∫ y in (0 : ℝ)..x,
        (thetaCuspFullSource y : ℂ) *
          (thetaArchimedeanShiftSource y - thetaArchimedeanShiftSource (-y)) -
            2 * (y : ℂ) * (thetaCuspFullSource y : ℂ) ^ 2) =
      fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource 0 := by
  have h := fullPrimeShiftNoetherCurrent_sub thetaCuspTiltSource thetaCuspTiltSource x
  simp only [completeTheta_primeShiftWard_balance] at h
  exact sub_eq_iff_eq_add.mpr (sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _))

end RHTower.ThetaSourceWard
