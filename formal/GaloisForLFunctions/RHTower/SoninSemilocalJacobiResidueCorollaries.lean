import GaloisForLFunctions.RHTower.SoninSemilocalFinitePrimeMeasure
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace RHTower

def semilocalFinitePrimeActualGradingGroundDefect
    {n : ℕ} (k : ℕ) (p : Fin (n + 1) → ℕ) : ℝ :=
  -((2 * k : ℕ) : ℝ) * semilocalFinitePrimeActualEvenJacobiMoment k p

theorem semilocalFinitePrimeActualGradingGroundDefect_eq_seriesDefect
    {n k : ℕ} (hk : 0 < k)
    (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    semilocalFinitePrimeActualGradingGroundDefect k p =
      semilocalFinitePrimeGradingGroundDefect k p := by
  unfold semilocalFinitePrimeActualGradingGroundDefect
  rw [semilocalFinitePrimeActualEvenJacobiMoment_eq_seriesMoment hk p hprime]
  rfl

/-- Equation (2) on the actual normalized Euler-weighted Gamma integral. -/
theorem semilocalFinitePrimeActualGradingGroundDefect_signed_pos
    {n k : ℕ} (hk : 0 < k)
    (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    0 < (-1 : ℝ) ^ (k + 1) *
      semilocalFinitePrimeActualGradingGroundDefect k p := by
  rw [semilocalFinitePrimeActualGradingGroundDefect_eq_seriesDefect hk p hprime]
  exact semilocalFinitePrimeGradingGroundDefect_signed_pos hk p hp hprime

def semilocalFinitePrimeActualProlateGroundDefect
    {n : ℕ} (lambda : ℝ) (k : ℕ) (p : Fin (n + 1) → ℕ) : ℝ :=
  lambda ^ 2 * semilocalFinitePrimeActualGradingGroundDefect k p

theorem semilocalFinitePrimeActualProlateGroundDefect_eq_seriesDefect
    {n k : ℕ} (hk : 0 < k) (lambda : ℝ)
    (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    semilocalFinitePrimeActualProlateGroundDefect lambda k p =
      semilocalFinitePrimeProlateGroundDefect lambda k p := by
  unfold semilocalFinitePrimeActualProlateGroundDefect
  rw [semilocalFinitePrimeActualGradingGroundDefect_eq_seriesDefect hk p hprime]
  rfl

/-- Equation (3): every positive prolate parameter preserves the actual defect sign. -/
theorem semilocalFinitePrimeActualProlateGroundDefect_signed_pos
    {n k : ℕ} {lambda : ℝ} (hlambda : 0 < lambda) (hk : 0 < k)
    (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    0 < (-1 : ℝ) ^ (k + 1) *
      semilocalFinitePrimeActualProlateGroundDefect lambda k p := by
  rw [semilocalFinitePrimeActualProlateGroundDefect_eq_seriesDefect hk lambda p hprime]
  exact semilocalFinitePrimeProlateGroundDefect_signed_pos
    hlambda hk p hp hprime

def semilocalFinitePrimeNormalizedSecondMoment
    {n : ℕ} (p : Fin (n + 1) → ℕ) : ℝ :=
  (∫ s : ℝ, s ^ 2 * semilocalFinitePrimeEulerDensity p s
      ∂semilocalArchimedeanGammaMeasure) /
    (∫ s : ℝ, semilocalFinitePrimeEulerDensity p s
      ∂semilocalArchimedeanGammaMeasure)

theorem semilocalPrimePoissonFactor_ne_zero
    {p : ℕ} (hp : p.Prime) (s : ℝ) :
    1 - (semilocalPrimePoissonRatio p : ℂ) *
        semilocalPrimePhase p s ≠ 0 := by
  intro hzero
  have hone : (semilocalPrimePoissonRatio p : ℂ) *
      semilocalPrimePhase p s = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm hone
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (semilocalPrimePoissonRatio_pos hp).le,
    norm_semilocalPrimePhase, mul_one, norm_one] at hnorm
  linarith [semilocalPrimePoissonRatio_lt_one hp]

theorem semilocalFinitePrimeEulerDensity_pos
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    0 < semilocalFinitePrimeEulerDensity p s := by
  unfold semilocalFinitePrimeEulerDensity
  apply Finset.prod_pos
  intro i _hi
  exact inv_pos.mpr (Complex.normSq_pos.mpr
    (semilocalPrimePoissonFactor_ne_zero (hprime i) s))

theorem continuous_semilocalPrimePhase (p : ℕ) :
    Continuous (semilocalPrimePhase p) := by
  unfold semilocalPrimePhase
  fun_prop

theorem continuous_semilocalFinitePrimeEulerDensity
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) :
    Continuous (semilocalFinitePrimeEulerDensity p) := by
  unfold semilocalFinitePrimeEulerDensity
  apply continuous_finsetProd
  intro i _hi
  apply Continuous.inv₀
  · exact Complex.continuous_normSq.comp
      (continuous_const.sub
        (continuous_const.mul (continuous_semilocalPrimePhase (p i))))
  · intro s
    exact (Complex.normSq_pos.mpr
      (semilocalPrimePoissonFactor_ne_zero (hprime i) s)).ne'

theorem summable_semilocalFinitePrimePoissonFrequencyTerm
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    Summable fun m : Fin n → ℤ =>
      (semilocalFinitePrimePoissonWeight p m : ℂ) *
        Complex.exp
          (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) * Complex.I) := by
  exact (summable_semilocalFinitePrimePoissonFourierTerm p hprime s).congr
    (fun m => semilocalFinitePrimePoissonFourierTerm_eq_weight_mul_exp p s m)

theorem semilocalFinitePrimeEulerDensity_le_poissonBound
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    semilocalFinitePrimeEulerDensity p s ≤
      semilocalFinitePrimePoissonPrefactor p *
        ∑' m : Fin n → ℤ, semilocalFinitePrimePoissonWeight p m := by
  have hseries :=
    semilocalFinitePrimeEulerDensity_eq_poissonSeries_complex p hprime s
  have hnorm := congrArg norm hseries
  rw [Complex.norm_real,
    Real.norm_of_nonneg (semilocalFinitePrimeEulerDensity_pos p hprime s).le,
    norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (semilocalFinitePrimePoissonPrefactor_pos p hprime).le]
    at hnorm
  have hsum := summable_semilocalFinitePrimePoissonFrequencyTerm p hprime s
  have hsumNorm : Summable fun m : Fin n → ℤ =>
      ‖(semilocalFinitePrimePoissonWeight p m : ℂ) *
        Complex.exp
          (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) * Complex.I)‖ := by
    apply (summable_norm_semilocalFinitePrimePoissonFourierTerm p hprime s).congr
    intro m
    rw [semilocalFinitePrimePoissonFourierTerm_eq_weight_mul_exp]
  calc
    semilocalFinitePrimeEulerDensity p s =
        semilocalFinitePrimePoissonPrefactor p *
          ‖∑' m : Fin n → ℤ,
            (semilocalFinitePrimePoissonWeight p m : ℂ) *
              Complex.exp
                (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) *
                  Complex.I)‖ := hnorm
    _ ≤ semilocalFinitePrimePoissonPrefactor p *
        ∑' m : Fin n → ℤ,
          ‖(semilocalFinitePrimePoissonWeight p m : ℂ) *
            Complex.exp
              (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) *
                Complex.I)‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsumNorm)
        (semilocalFinitePrimePoissonPrefactor_pos p hprime).le
    _ = semilocalFinitePrimePoissonPrefactor p *
        ∑' m : Fin n → ℤ, semilocalFinitePrimePoissonWeight p m := by
      congr 1
      apply tsum_congr
      intro m
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (semilocalFinitePrimePoissonWeight_pos p hprime m).le,
        Complex.norm_exp]
      simp

theorem integrable_eval_mul_semilocalFinitePrimeEulerDensity
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (q : ℝ[X]) :
    Integrable (fun s : ℝ => q.eval s * semilocalFinitePrimeEulerDensity p s)
      semilocalArchimedeanGammaMeasure := by
  have hqC := integrable_coe_eval_semilocalArchimedeanGammaMeasure q
  have hq : Integrable (fun s : ℝ => q.eval s)
      semilocalArchimedeanGammaMeasure := by
    simpa using hqC.re
  apply hq.mul_bdd
  · exact (continuous_semilocalFinitePrimeEulerDensity p hprime).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs,
      abs_of_pos (semilocalFinitePrimeEulerDensity_pos p hprime s)]
    exact semilocalFinitePrimeEulerDensity_le_poissonBound p hprime s

theorem integral_sq_mul_semilocalFinitePrimeEulerDensity_pos
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) :
    0 < ∫ s : ℝ, s ^ 2 * semilocalFinitePrimeEulerDensity p s
      ∂semilocalArchimedeanGammaMeasure := by
  have hsq : Integrable (fun s : ℝ => s ^ 2 * semilocalFinitePrimeEulerDensity p s)
      semilocalArchimedeanGammaMeasure := by
    apply (integrable_eval_mul_semilocalFinitePrimeEulerDensity p hprime (X ^ 2)).congr
    filter_upwards with s
    simp
  have hvol := hsq
  rw [semilocalArchimedeanGammaMeasure,
    integrable_withDensity_iff_integrable_smul
      continuous_semilocalArchimedeanGammaDensityNNReal.measurable] at hvol
  have hvol' : Integrable (fun s : ℝ =>
      semilocalArchimedeanGammaDensity s *
        (s ^ 2 * semilocalFinitePrimeEulerDensity p s)) volume := by
    apply hvol.congr
    filter_upwards with s
    change semilocalArchimedeanGammaDensity s *
        (s ^ 2 * semilocalFinitePrimeEulerDensity p s) = _
    rfl
  have hdensityPos (s : ℝ) : 0 < semilocalArchimedeanGammaDensity s := by
    unfold semilocalArchimedeanGammaDensity
    apply mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    apply Complex.normSq_pos.mpr
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
  have hposVol : 0 < ∫ s : ℝ,
      semilocalArchimedeanGammaDensity s *
        (s ^ 2 * semilocalFinitePrimeEulerDensity p s) := by
    apply integral_pos_of_integrable_nonneg_nonzero
      ((continuous_semilocalArchimedeanGammaDensity.mul
        ((continuous_id.pow 2).mul
          (continuous_semilocalFinitePrimeEulerDensity p hprime))))
      hvol'
    · intro s
      exact mul_nonneg (hdensityPos s).le
        (mul_nonneg (sq_nonneg s)
          (semilocalFinitePrimeEulerDensity_pos p hprime s).le)
    · exact ne_of_gt (mul_pos (hdensityPos 1)
        (mul_pos (by norm_num)
          (semilocalFinitePrimeEulerDensity_pos p hprime 1)))
  rw [semilocalArchimedeanGammaMeasure,
    integral_withDensity_eq_integral_smul
      continuous_semilocalArchimedeanGammaDensityNNReal.measurable]
  simpa [NNReal.smul_def, mul_assoc] using! hposVol

theorem semilocalFinitePrimeNormalizedSecondMoment_pos
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    0 < semilocalFinitePrimeNormalizedSecondMoment p := by
  unfold semilocalFinitePrimeNormalizedSecondMoment
  exact div_pos (integral_sq_mul_semilocalFinitePrimeEulerDensity_pos p hprime)
    (integral_semilocalFinitePrimeEulerDensity_pos p hprime)

theorem semilocalFinitePrimeJacobiTwoIntegral_recurrence
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    semilocalArchimedeanJacobiCoefficient 0 *
        semilocalArchimedeanJacobiCoefficient 1 *
          (∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial 2).eval s *
            semilocalFinitePrimeEulerDensity p s
              ∂semilocalArchimedeanGammaMeasure) =
      (∫ s : ℝ, s ^ 2 * semilocalFinitePrimeEulerDensity p s
        ∂semilocalArchimedeanGammaMeasure) -
      semilocalArchimedeanJacobiCoefficient 0 ^ 2 *
        (∫ s : ℝ, semilocalFinitePrimeEulerDensity p s
          ∂semilocalArchimedeanGammaMeasure) := by
  have hp2 := integrable_eval_mul_semilocalFinitePrimeEulerDensity p hprime
    (semilocalArchimedeanJacobiPolynomial 2)
  have hsq : Integrable (fun s : ℝ => s ^ 2 * semilocalFinitePrimeEulerDensity p s)
      semilocalArchimedeanGammaMeasure := by
    apply (integrable_eval_mul_semilocalFinitePrimeEulerDensity p hprime (X ^ 2)).congr
    filter_upwards with s
    simp
  have hG : Integrable (semilocalFinitePrimeEulerDensity p)
      semilocalArchimedeanGammaMeasure := by
    apply (integrable_eval_mul_semilocalFinitePrimeEulerDensity p hprime (1 : ℝ[X])).congr
    filter_upwards with s
    simp
  rw [← integral_const_mul]
  rw [← integral_const_mul]
  rw [← integral_sub hsq (hG.const_mul
    (semilocalArchimedeanJacobiCoefficient 0 ^ 2))]
  apply integral_congr_ae
  filter_upwards with s
  rw [← mul_assoc,
    semilocalArchimedeanJacobiPolynomial_two_recurrence]
  ring

theorem semilocalFinitePrimeActualMoment_one_recurrence
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    semilocalArchimedeanJacobiCoefficient 0 *
        semilocalArchimedeanJacobiCoefficient 1 *
          semilocalFinitePrimeActualEvenJacobiMoment 1 p =
      semilocalFinitePrimeNormalizedSecondMoment p -
        semilocalArchimedeanJacobiCoefficient 0 ^ 2 := by
  have hrec := semilocalFinitePrimeJacobiTwoIntegral_recurrence p hprime
  have hD : (∫ s : ℝ, semilocalFinitePrimeEulerDensity p s
      ∂semilocalArchimedeanGammaMeasure) ≠ 0 :=
    (integral_semilocalFinitePrimeEulerDensity_pos p hprime).ne'
  unfold semilocalFinitePrimeActualEvenJacobiMoment
    semilocalFinitePrimeNormalizedSecondMoment
  norm_num
  field_simp [hD]
  nlinarith

/-- Equation (4): the normalized first Jacobi coefficient contracts strictly below `1/2`. -/
theorem semilocalFinitePrimeNormalizedSecondMoment_lt_half
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    semilocalFinitePrimeNormalizedSecondMoment p < 1 / 2 := by
  have hmom := semilocalFinitePrimeActualEvenJacobiMoment_signed_pos
    (k := 1) (by norm_num) p hp hprime
  norm_num at hmom
  have hrec := semilocalFinitePrimeActualMoment_one_recurrence p hprime
  have hprod : 0 < semilocalArchimedeanJacobiCoefficient 0 *
      semilocalArchimedeanJacobiCoefficient 1 :=
    mul_pos (semilocalArchimedeanJacobiCoefficient_pos 0)
      (semilocalArchimedeanJacobiCoefficient_pos 1)
  have hsq0 := semilocalArchimedeanJacobiCoefficient_sq 0
  norm_num at hsq0
  nlinarith

theorem semilocalFinitePrimeNormalizedSecondMoment_bounds
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    0 < semilocalFinitePrimeNormalizedSecondMoment p ∧
      semilocalFinitePrimeNormalizedSecondMoment p < 1 / 2 :=
  ⟨semilocalFinitePrimeNormalizedSecondMoment_pos p hprime,
    semilocalFinitePrimeNormalizedSecondMoment_lt_half p hp hprime⟩

theorem semilocalArchimedeanJacobiCoefficient_zero_mul_one :
    semilocalArchimedeanJacobiCoefficient 0 *
        semilocalArchimedeanJacobiCoefficient 1 =
      Real.sqrt (3 / 2) := by
  have hsq0 := semilocalArchimedeanJacobiCoefficient_sq 0
  have hsq1 := semilocalArchimedeanJacobiCoefficient_sq 1
  norm_num at hsq0 hsq1
  have hleft : 0 ≤ semilocalArchimedeanJacobiCoefficient 0 *
      semilocalArchimedeanJacobiCoefficient 1 :=
    (mul_pos (semilocalArchimedeanJacobiCoefficient_pos 0)
      (semilocalArchimedeanJacobiCoefficient_pos 1)).le
  have hright : 0 ≤ Real.sqrt (3 / 2) := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := by
    rw [Real.sq_sqrt]
    norm_num
  nlinarith [sq_nonneg
    (semilocalArchimedeanJacobiCoefficient 0 *
      semilocalArchimedeanJacobiCoefficient 1)]

/-- Equation (5): the first grading residue has the stated explicit positive value. -/
theorem semilocalFinitePrimeActualGradingGroundDefect_one_eq_explicitResidue
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    semilocalFinitePrimeActualGradingGroundDefect 1 p =
      2 * (1 / 2 - semilocalFinitePrimeNormalizedSecondMoment p) /
        Real.sqrt (3 / 2) ∧
      0 < semilocalFinitePrimeActualGradingGroundDefect 1 p := by
  have hrec := semilocalFinitePrimeActualMoment_one_recurrence p hprime
  have hprod := semilocalArchimedeanJacobiCoefficient_zero_mul_one
  have hcoeff : semilocalArchimedeanJacobiCoefficient 0 *
      semilocalArchimedeanJacobiCoefficient 1 ≠ 0 :=
    mul_ne_zero (semilocalArchimedeanJacobiCoefficient_pos 0).ne'
      (semilocalArchimedeanJacobiCoefficient_pos 1).ne'
  have hsq0 := semilocalArchimedeanJacobiCoefficient_sq 0
  norm_num at hsq0
  constructor
  · unfold semilocalFinitePrimeActualGradingGroundDefect
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [← hprod]
    apply (eq_div_iff hcoeff).2
    nlinarith
  · have hsign := semilocalFinitePrimeActualGradingGroundDefect_signed_pos
      (k := 1) (by norm_num) p hp hprime
    norm_num at hsign ⊢
    exact hsign

end RHTower
