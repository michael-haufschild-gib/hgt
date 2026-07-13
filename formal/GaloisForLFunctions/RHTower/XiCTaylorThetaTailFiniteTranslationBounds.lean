import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailRapidDecay
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedFeedback
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Rapid moments for the finite translation edge

The raw theta tail decays at every prescribed natural exponential rate.  Consequently its
moments, after division by the Taylor factorial, have any fixed geometric rate.  Choosing that
rate above the bounded spectral fibre is the quantitative input for controlling logarithmic
translation edges whose displacement is only logarithmic in the Taylor degree.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Absolute raw-tail moments at an arbitrary natural exponential rate. -/
theorem integral_abs_pow_mul_thetaCuspTailDerivative_zero_le_nat_rate
    (m p : ℕ) (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0,
      |x ^ m * thetaCuspTailDerivative 0 x|) ≤
        thetaCuspTailNatExpConstant p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
  let C : ℝ := thetaCuspTailNatExpConstant p
  have hf : IntegrableOn
      (fun x : ℝ => |x ^ m * thetaCuspTailDerivative 0 x|) (Ioi 0) := by
    simpa only [Real.norm_eq_abs] using
      (integrableOn_pow_mul_thetaCuspTailDerivative m 0).norm
  have hbase : IntegrableOn
      (fun x : ℝ => x ^ m * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_pow_mul_exp_nat_neg m p hp]
    positivity
  have hg : IntegrableOn
      (fun x : ℝ => C * (x ^ m * Real.exp (-(p : ℝ) * x))) (Ioi 0) :=
    hbase.const_mul C
  calc
    (∫ x : ℝ in Ioi 0, |x ^ m * thetaCuspTailDerivative 0 x|) ≤
        ∫ x : ℝ in Ioi 0,
          C * (x ^ m * Real.exp (-(p : ℝ) * x)) := by
      apply MeasureTheory.integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have htail := abs_thetaCuspTailDerivative_zero_le_nat_exp_neg p hx0
      rw [abs_mul, abs_pow, abs_of_nonneg hx0]
      calc
        x ^ m * |thetaCuspTailDerivative 0 x| ≤
            x ^ m * (C * Real.exp (-(p : ℝ) * x)) :=
          mul_le_mul_of_nonneg_left htail (pow_nonneg hx0 _)
        _ = C * (x ^ m * Real.exp (-(p : ℝ) * x)) := by ring
    _ = thetaCuspTailNatExpConstant p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
      rw [integral_const_mul, integral_pow_mul_exp_nat_neg m p hp]

/-- Normalizing by the Taylor factorial leaves a freely prescribed geometric moment rate. -/
theorem integral_abs_pow_mul_thetaCuspTailDerivative_zero_div_factorial_le_nat_rate
    (m p : ℕ) (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0,
      |x ^ m * thetaCuspTailDerivative 0 x|) /
        (m.factorial : ℝ) ≤
      thetaCuspTailNatExpConstant p / (p : ℝ) ^ (m + 1) := by
  have h := integral_abs_pow_mul_thetaCuspTailDerivative_zero_le_nat_rate m p hp
  have hfac : (0 : ℝ) < m.factorial := by positivity
  rw [div_le_iff₀ hfac]
  calc
    (∫ x : ℝ in Ioi 0, |x ^ m * thetaCuspTailDerivative 0 x|) ≤
        thetaCuspTailNatExpConstant p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := h
    _ = (thetaCuspTailNatExpConstant p / (p : ℝ) ^ (m + 1)) *
          (m.factorial : ℝ) := by ring

/-- Exact shifted gamma moment.  This is the analytic reason a logarithmic source translation
costs an exponential in the shift but retains geometric decay in the Taylor cutoff. -/
theorem integral_add_pow_mul_exp_nat_neg
    (N p : ℕ) (hp : 0 < p) (a : ℝ) :
    (∫ x : ℝ in Ioi 0, (x + a) ^ N * Real.exp (-(p : ℝ) * x)) =
      ∑ m ∈ Finset.range (N + 1),
        (N.choose m : ℝ) * a ^ (N - m) *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
  have hInt (m : ℕ) : IntegrableOn
      (fun x : ℝ => ((N.choose m : ℝ) * a ^ (N - m)) *
        (x ^ m * Real.exp (-(p : ℝ) * x))) (Ioi 0) := by
    have hb : IntegrableOn
        (fun x : ℝ => x ^ m * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
      apply Integrable.of_integral_ne_zero
      rw [integral_pow_mul_exp_nat_neg m p hp]
      positivity
    exact hb.const_mul _
  rw [show (fun x : ℝ => (x + a) ^ N * Real.exp (-(p : ℝ) * x)) =
      fun x : ℝ => ∑ m ∈ Finset.range (N + 1),
        ((N.choose m : ℝ) * a ^ (N - m)) *
          (x ^ m * Real.exp (-(p : ℝ) * x)) by
    funext x
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _hm
    ring]
  rw [MeasureTheory.integral_finsetSum _ (fun m _hm => hInt m)]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [MeasureTheory.integral_const_mul, integral_pow_mul_exp_nat_neg m p hp]

/-- The finite shifted gamma-moment sum is exactly a truncated exponential. -/
theorem shifted_gamma_moment_sum_eq
    (N p : ℕ) (hp : 0 < p) (a : ℝ) :
    (∑ m ∈ Finset.range (N + 1),
        (N.choose m : ℝ) * a ^ (N - m) *
          (m.factorial / (p : ℝ) ^ (m + 1))) =
      (N.factorial / (p : ℝ) ^ (N + 1)) *
        ∑ j ∈ Finset.range (N + 1),
          (((p : ℝ) * a) ^ j / j.factorial) := by
  rw [← Finset.sum_range_reflect
    (fun j : ℕ => (((p : ℝ) * a) ^ j / j.factorial)) (N + 1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmle : m ≤ N := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  rw [show N + 1 - 1 - m = N - m by omega]
  have hfacNat := Nat.choose_mul_factorial_mul_factorial hmle
  have hfac : (N.choose m : ℝ) * m.factorial * (N - m).factorial =
      N.factorial := by exact_mod_cast hfacNat
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hmf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hsubf : (((N - m).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hpR, hmf, hsubf]
  rw [mul_pow]
  rw [show N + 1 = (m + 1) + (N - m) by omega, pow_add]
  rw [← hfac]
  ring

/-- Upper bound for the shifted gamma moment by the full exponential series. -/
theorem shifted_gamma_moment_sum_le
    (N p : ℕ) (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) :
    (∑ m ∈ Finset.range (N + 1),
        (N.choose m : ℝ) * a ^ (N - m) *
          (m.factorial / (p : ℝ) ^ (m + 1))) ≤
      (N.factorial / (p : ℝ) ^ (N + 1)) * Real.exp ((p : ℝ) * a) := by
  rw [shifted_gamma_moment_sum_eq N p hp a]
  gcongr
  exact Real.sum_le_exp_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) _

/-- Integrability of the shifted polynomial-exponential gamma envelope. -/
theorem integrableOn_add_pow_mul_exp_nat_neg
    (N p : ℕ) (hp : 0 < p) (a : ℝ) :
    IntegrableOn (fun x : ℝ =>
      (x + a) ^ N * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
  have hInt (m : ℕ) : IntegrableOn
      (fun x : ℝ => ((N.choose m : ℝ) * a ^ (N - m)) *
        (x ^ m * Real.exp (-(p : ℝ) * x))) (Ioi 0) := by
    have hb : IntegrableOn
        (fun x : ℝ => x ^ m * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
      apply Integrable.of_integral_ne_zero
      rw [integral_pow_mul_exp_nat_neg m p hp]
      positivity
    exact hb.const_mul _
  rw [show (fun x : ℝ => (x + a) ^ N * Real.exp (-(p : ℝ) * x)) =
      fun x : ℝ => ∑ m ∈ Finset.range (N + 1),
        ((N.choose m : ℝ) * a ^ (N - m)) *
          (x ^ m * Real.exp (-(p : ℝ) * x)) by
    funext x
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _hm
    ring]
  exact MeasureTheory.integrable_finsetSum _ (fun m _hm => hInt m)

/-- Global factorial Taylor remainder for the real exponential.  The standard library estimate
used below controls the complex remainder by the corresponding real tail; this lemma retains the
factorial which is essential when the remainder is integrated against high source moments. -/
theorem real_exp_sub_sum_le_factorial_tail
    (r : ℝ) (hr : 0 ≤ r) (N : ℕ) :
    Real.exp r - ∑ m ∈ Finset.range N, r ^ m / m.factorial ≤
      (r ^ N / N.factorial) * Real.exp r := by
  have hs : Summable (fun m : ℕ => r ^ m / m.factorial) :=
    NormedSpace.expSeries_div_summable r
  have hsum : (∑' m : ℕ, r ^ m / m.factorial) = Real.exp r := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp r).tsum_eq
  have hsplit := hs.sum_add_tsum_nat_add N
  have htail : Real.exp r - ∑ m ∈ Finset.range N, r ^ m / m.factorial =
      ∑' j : ℕ, r ^ (j + N) / (j + N).factorial := by
    rw [← hsum]
    linarith
  rw [htail]
  have hfac (j : ℕ) :
      (N.factorial : ℝ) * j.factorial ≤ (j + N).factorial := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) <|
      (Nat.factorial_mul_factorial_dvd_factorial_add N j) |>.trans (by
        rw [Nat.add_comm])
  have hterm (j : ℕ) :
      r ^ (j + N) / (j + N).factorial ≤
        (r ^ N / N.factorial) * (r ^ j / j.factorial) := by
    have hnum : r ^ (j + N) = r ^ N * r ^ j := by
      rw [Nat.add_comm, pow_add]
    rw [hnum]
    have hden : (0 : ℝ) < (N.factorial : ℝ) * j.factorial := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have hinv : (((j + N).factorial : ℝ))⁻¹ ≤
        (((N.factorial : ℝ) * j.factorial))⁻¹ :=
      inv_anti₀ hden (hfac j)
    calc
      r ^ N * r ^ j * (((j + N).factorial : ℝ))⁻¹ ≤
          r ^ N * r ^ j * (((N.factorial : ℝ) * j.factorial))⁻¹ := by
            gcongr
      _ = (r ^ N * (N.factorial : ℝ)⁻¹) *
          (r ^ j * (j.factorial : ℝ)⁻¹) := by
            rw [mul_inv_rev]
            ring
  calc
    (∑' j : ℕ, r ^ (j + N) / (j + N).factorial) ≤
        ∑' j : ℕ, (r ^ N / N.factorial) * (r ^ j / j.factorial) := by
      exact ((summable_nat_add_iff N).2 hs).tsum_le_tsum hterm (hs.mul_left _)
    _ = (r ^ N / N.factorial) * ∑' j : ℕ, r ^ j / j.factorial := by
      rw [tsum_mul_left]
    _ = _ := by rw [hsum]

/-- Global factorial remainder for the complex exponential. -/
theorem norm_complex_exp_sub_sum_le_factorial_tail (w : ℂ) (N : ℕ) :
    ‖Complex.exp w - ∑ m ∈ Finset.range N, w ^ m / m.factorial‖ ≤
      (‖w‖ ^ N / N.factorial) * Real.exp ‖w‖ := by
  calc
    _ ≤ Real.exp ‖w‖ - ∑ m ∈ Finset.range N, ‖w‖ ^ m / m.factorial :=
      Complex.norm_exp_sub_sum_le_exp_norm_sub_sum w N
    _ ≤ _ := real_exp_sub_sum_le_factorial_tail ‖w‖ (norm_nonneg _) N

/-- Evaluation of the diagonal phase polynomial as one contiguous exponential Taylor section. -/
theorem eval_finitePositivePhasePolynomial_eq_sum
    (d : ℕ) (z : ℂ) (x : ℝ) :
    (finitePositivePhasePolynomial d x).eval z =
      ∑ m ∈ Finset.range (2 * d + 1),
        (((x : ℂ) * I * z) ^ m) / m.factorial := by
  rw [finitePositivePhasePolynomial_eq_taylor]
  unfold finitePositivePhaseTaylorPolynomial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro m _hm
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [mul_pow]
  ring

/-- Factorial remainder of the finite positive phase, uniform in the source coordinate. -/
theorem norm_exp_sub_eval_finitePositivePhasePolynomial_le
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * I * z) -
        (finitePositivePhasePolynomial d x).eval z‖ ≤
      (‖(x : ℂ) * I * z‖ ^ (2 * d + 1) /
          (2 * d + 1).factorial) *
        Real.exp ‖(x : ℂ) * I * z‖ := by
  rw [eval_finitePositivePhasePolynomial_eq_sum]
  exact norm_complex_exp_sub_sum_le_factorial_tail
    ((x : ℂ) * I * z) (2 * d + 1)

/-- The spectral derivative of the common-cutoff phase section is the preceding exponential
Taylor section multiplied by its source frequency. -/
theorem eval_derivative_finitePositivePhasePolynomial_eq_sum
    (d : ℕ) (z : ℂ) (x : ℝ) :
    (finitePositivePhasePolynomial d x).derivative.eval z =
      ((x : ℂ) * I) * ∑ m ∈ Finset.range (2 * d),
        (((x : ℂ) * I * z) ^ m) / m.factorial := by
  rw [finitePositivePhasePolynomial_eq_taylor]
  unfold finitePositivePhaseTaylorPolynomial
  rw [show 2 * d + 1 = 2 * d + 1 by rfl, Finset.sum_range_succ']
  simp only [derivative_add, derivative_sum, derivative_C_mul, derivative_X_pow,
    mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, derivative_one,
    add_zero]
  rw [Polynomial.eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [show m + 1 - 1 = m by omega, Nat.factorial_succ]
  push_cast
  have hmne : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp [hmne]
  ring

/-- The exact complex exponential is dominated by the exponential of the full complex norm. -/
theorem norm_complex_exp_le_exp_norm (w : ℂ) :
    ‖Complex.exp w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (re_le_norm w)

/-- A common-cutoff phase section is bounded by the full exponential series, uniformly in the
Taylor degree. -/
theorem norm_eval_finitePositivePhasePolynomial_le_exp_norm
    (d : ℕ) (x : ℝ) (z : ℂ) :
    ‖(finitePositivePhasePolynomial d x).eval z‖ ≤
      Real.exp ‖(x : ℂ) * I * z‖ := by
  rw [eval_finitePositivePhasePolynomial_eq_sum]
  calc
    ‖∑ m ∈ Finset.range (2 * d + 1),
        ((x : ℂ) * I * z) ^ m / m.factorial‖ ≤
        ∑ m ∈ Finset.range (2 * d + 1),
          ‖((x : ℂ) * I * z) ^ m / m.factorial‖ := norm_sum_le _ _
    _ = ∑ m ∈ Finset.range (2 * d + 1),
        ‖(x : ℂ) * I * z‖ ^ m / m.factorial := by
      apply Finset.sum_congr rfl
      intro m _hm
      simp only [norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ Real.exp ‖(x : ℂ) * I * z‖ :=
      Real.sum_le_exp_of_nonneg (norm_nonneg _) _

/-- The derivative of a common-cutoff phase section has the corresponding degree-free exponential
envelope with one source-frequency factor. -/
theorem norm_eval_derivative_finitePositivePhasePolynomial_le_exp_norm
    (d : ℕ) (x : ℝ) (z : ℂ) :
    ‖(finitePositivePhasePolynomial d x).derivative.eval z‖ ≤
      ‖(x : ℂ) * I‖ * Real.exp ‖(x : ℂ) * I * z‖ := by
  rw [eval_derivative_finitePositivePhasePolynomial_eq_sum, norm_mul]
  gcongr
  calc
    ‖∑ m ∈ Finset.range (2 * d),
        ((x : ℂ) * I * z) ^ m / m.factorial‖ ≤
        ∑ m ∈ Finset.range (2 * d),
          ‖((x : ℂ) * I * z) ^ m / m.factorial‖ := norm_sum_le _ _
    _ = ∑ m ∈ Finset.range (2 * d),
        ‖(x : ℂ) * I * z‖ ^ m / m.factorial := by
      apply Finset.sum_congr rfl
      intro m _hm
      simp only [norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ Real.exp ‖(x : ℂ) * I * z‖ :=
      Real.sum_le_exp_of_nonneg (norm_nonneg _) _

/-- Factorial remainder for the spectral derivative of the positive phase section. -/
theorem norm_exp_derivative_sub_eval_derivative_finitePositivePhasePolynomial_le
    (d : ℕ) (x : ℝ) (z : ℂ) :
    ‖((x : ℂ) * I) * Complex.exp ((x : ℂ) * I * z) -
        (finitePositivePhasePolynomial d x).derivative.eval z‖ ≤
      ‖(x : ℂ) * I‖ *
        ((‖(x : ℂ) * I * z‖ ^ (2 * d) / (2 * d).factorial) *
          Real.exp ‖(x : ℂ) * I * z‖) := by
  rw [eval_derivative_finitePositivePhasePolynomial_eq_sum]
  rw [show ((x : ℂ) * I) * Complex.exp ((x : ℂ) * I * z) -
      (x : ℂ) * I * ∑ m ∈ Finset.range (2 * d),
        ((x : ℂ) * I * z) ^ m / m.factorial =
      ((x : ℂ) * I) * (Complex.exp ((x : ℂ) * I * z) -
        ∑ m ∈ Finset.range (2 * d),
          ((x : ℂ) * I * z) ^ m / m.factorial) by ring,
    norm_mul]
  gcongr
  exact norm_complex_exp_sub_sum_le_factorial_tail
    ((x : ℂ) * I * z) (2 * d)

/-- Exact evaluated form of the positive phase translation edge. -/
theorem eval_finitePositivePhaseTranslationTopEdge
    (d : ℕ) (x a : ℝ) (z : ℂ) :
    (finitePositivePhaseTranslationTopEdge d x a).eval z =
      (finitePositivePhasePolynomial d x).eval z *
          (finitePositivePhasePolynomial d a).eval z -
        (finitePositivePhasePolynomial d (x + a)).eval z := by
  rw [finitePositivePhaseTranslationTopEdge_eq_mul_sub, eval_sub, eval_mul]

/-- The phase translation edge is a three-point factorial remainder.  The exact exponential
addition law cancels before the triangle inequality, so no leading phase term survives. -/
theorem norm_eval_finitePositivePhaseTranslationTopEdge_le
    (d : ℕ) (x a : ℝ) (z : ℂ) :
    ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      (‖(x : ℂ) * I * z‖ ^ (2 * d + 1) / (2 * d + 1).factorial) *
          Real.exp ‖(x : ℂ) * I * z‖ *
          Real.exp ‖(a : ℂ) * I * z‖ +
        Real.exp ‖(x : ℂ) * I * z‖ *
          ((‖(a : ℂ) * I * z‖ ^ (2 * d + 1) / (2 * d + 1).factorial) *
            Real.exp ‖(a : ℂ) * I * z‖) +
        (‖((x + a : ℝ) : ℂ) * I * z‖ ^ (2 * d + 1) /
            (2 * d + 1).factorial) *
          Real.exp ‖((x + a : ℝ) : ℂ) * I * z‖ := by
  let Px := (finitePositivePhasePolynomial d x).eval z
  let Pa := (finitePositivePhasePolynomial d a).eval z
  let Ps := (finitePositivePhasePolynomial d (x + a)).eval z
  let wx : ℂ := (x : ℂ) * I * z
  let wa : ℂ := (a : ℂ) * I * z
  let ws : ℂ := ((x + a : ℝ) : ℂ) * I * z
  have hsum : wx + wa = ws := by
    dsimp [wx, wa, ws]
    push_cast
    ring
  have hexp : Complex.exp wx * Complex.exp wa = Complex.exp ws := by
    rw [← Complex.exp_add, hsum]
  have halg : Px * Pa - Ps =
      (Px - Complex.exp wx) * Pa +
        Complex.exp wx * (Pa - Complex.exp wa) +
          (Complex.exp ws - Ps) := by
    rw [← hexp]
    ring
  rw [eval_finitePositivePhaseTranslationTopEdge]
  change ‖Px * Pa - Ps‖ ≤ _
  rw [halg]
  calc
    ‖(Px - Complex.exp wx) * Pa +
        Complex.exp wx * (Pa - Complex.exp wa) +
          (Complex.exp ws - Ps)‖ ≤
        ‖(Px - Complex.exp wx) * Pa‖ +
          ‖Complex.exp wx * (Pa - Complex.exp wa)‖ +
            ‖Complex.exp ws - Ps‖ := by
      calc
        _ ≤ ‖(Px - Complex.exp wx) * Pa +
              Complex.exp wx * (Pa - Complex.exp wa)‖ +
              ‖Complex.exp ws - Ps‖ := norm_add_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_add_le _ _
    _ = ‖Px - Complex.exp wx‖ * ‖Pa‖ +
          ‖Complex.exp wx‖ * ‖Pa - Complex.exp wa‖ +
            ‖Complex.exp ws - Ps‖ := by rw [norm_mul, norm_mul]
    _ ≤
        (‖wx‖ ^ (2 * d + 1) / (2 * d + 1).factorial) * Real.exp ‖wx‖ *
            Real.exp ‖wa‖ +
          Real.exp ‖wx‖ *
            ((‖wa‖ ^ (2 * d + 1) / (2 * d + 1).factorial) * Real.exp ‖wa‖) +
          (‖ws‖ ^ (2 * d + 1) / (2 * d + 1).factorial) * Real.exp ‖ws‖ := by
      gcongr
      · simpa only [Px, wx, norm_sub_rev] using
          norm_exp_sub_eval_finitePositivePhasePolynomial_le d z x
      · simpa only [Pa, wa] using
          norm_eval_finitePositivePhasePolynomial_le_exp_norm d a z
      · exact norm_complex_exp_le_exp_norm wx
      · simpa only [Pa, wa, norm_sub_rev] using
          norm_exp_sub_eval_finitePositivePhasePolynomial_le d z a
      · simpa only [Ps, ws] using
          norm_exp_sub_eval_finitePositivePhasePolynomial_le d z (x + a)
    _ = _ := by rfl

/-- Exact evaluated derivative of the positive phase translation edge. -/
theorem eval_derivative_finitePositivePhaseTranslationTopEdge
    (d : ℕ) (x a : ℝ) (z : ℂ) :
    (finitePositivePhaseTranslationTopEdge d x a).derivative.eval z =
      (finitePositivePhasePolynomial d x).derivative.eval z *
          (finitePositivePhasePolynomial d a).eval z +
        (finitePositivePhasePolynomial d x).eval z *
          (finitePositivePhasePolynomial d a).derivative.eval z -
        (finitePositivePhasePolynomial d (x + a)).derivative.eval z := by
  rw [finitePositivePhaseTranslationTopEdge_derivative_eq, eval_sub, eval_add,
    eval_mul, eval_mul]

/-- The spectral derivative of the phase translation edge has the same factorial suppression.
The five displayed terms are precisely the two value remainders, the two derivative remainders,
and the summed-source derivative remainder after the exact exponential derivative cancels. -/
theorem norm_eval_derivative_finitePositivePhaseTranslationTopEdge_le
    (d : ℕ) (x a : ℝ) (z : ℂ) :
    ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      (‖(x : ℂ) * I‖ *
          ((‖(x : ℂ) * I * z‖ ^ (2 * d) / (2 * d).factorial) *
            Real.exp ‖(x : ℂ) * I * z‖)) *
          Real.exp ‖(a : ℂ) * I * z‖ +
        ‖(x : ℂ) * I‖ * Real.exp ‖(x : ℂ) * I * z‖ *
          ((‖(a : ℂ) * I * z‖ ^ (2 * d + 1) / (2 * d + 1).factorial) *
            Real.exp ‖(a : ℂ) * I * z‖) +
        ((‖(x : ℂ) * I * z‖ ^ (2 * d + 1) / (2 * d + 1).factorial) *
          Real.exp ‖(x : ℂ) * I * z‖) *
          (‖(a : ℂ) * I‖ * Real.exp ‖(a : ℂ) * I * z‖) +
        Real.exp ‖(x : ℂ) * I * z‖ *
          (‖(a : ℂ) * I‖ *
            ((‖(a : ℂ) * I * z‖ ^ (2 * d) / (2 * d).factorial) *
              Real.exp ‖(a : ℂ) * I * z‖)) +
        ‖((x + a : ℝ) : ℂ) * I‖ *
          ((‖((x + a : ℝ) : ℂ) * I * z‖ ^ (2 * d) / (2 * d).factorial) *
            Real.exp ‖((x + a : ℝ) : ℂ) * I * z‖) := by
  let Px := (finitePositivePhasePolynomial d x).eval z
  let Pa := (finitePositivePhasePolynomial d a).eval z
  let Dx := (finitePositivePhasePolynomial d x).derivative.eval z
  let Da := (finitePositivePhasePolynomial d a).derivative.eval z
  let Ds := (finitePositivePhasePolynomial d (x + a)).derivative.eval z
  let cx : ℂ := (x : ℂ) * I
  let ca : ℂ := (a : ℂ) * I
  let cs : ℂ := ((x + a : ℝ) : ℂ) * I
  let wx : ℂ := cx * z
  let wa : ℂ := ca * z
  let ws : ℂ := cs * z
  have hsum : wx + wa = ws := by
    dsimp [wx, wa, ws, cx, ca, cs]
    push_cast
    ring
  have hcoeff : cx + ca = cs := by
    dsimp [cx, ca, cs]
    push_cast
    ring
  have hexp : Complex.exp wx * Complex.exp wa = Complex.exp ws := by
    rw [← Complex.exp_add, hsum]
  have halg : Dx * Pa + Px * Da - Ds =
      (Dx - cx * Complex.exp wx) * Pa +
        (cx * Complex.exp wx) * (Pa - Complex.exp wa) +
        (Px - Complex.exp wx) * Da +
        Complex.exp wx * (Da - ca * Complex.exp wa) -
        (Ds - cs * Complex.exp ws) := by
    rw [← hexp]
    rw [← hcoeff]
    ring
  rw [eval_derivative_finitePositivePhaseTranslationTopEdge]
  change ‖Dx * Pa + Px * Da - Ds‖ ≤ _
  rw [halg]
  calc
    ‖(Dx - cx * Complex.exp wx) * Pa +
        (cx * Complex.exp wx) * (Pa - Complex.exp wa) +
        (Px - Complex.exp wx) * Da +
        Complex.exp wx * (Da - ca * Complex.exp wa) -
        (Ds - cs * Complex.exp ws)‖ ≤
      ‖(Dx - cx * Complex.exp wx) * Pa‖ +
        ‖(cx * Complex.exp wx) * (Pa - Complex.exp wa)‖ +
        ‖(Px - Complex.exp wx) * Da‖ +
        ‖Complex.exp wx * (Da - ca * Complex.exp wa)‖ +
        ‖Ds - cs * Complex.exp ws‖ := by
      calc
        _ ≤ ‖(Dx - cx * Complex.exp wx) * Pa +
              (cx * Complex.exp wx) * (Pa - Complex.exp wa) +
              (Px - Complex.exp wx) * Da +
              Complex.exp wx * (Da - ca * Complex.exp wa)‖ +
              ‖Ds - cs * Complex.exp ws‖ := norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          calc
            _ ≤ ‖(Dx - cx * Complex.exp wx) * Pa +
                  (cx * Complex.exp wx) * (Pa - Complex.exp wa) +
                  (Px - Complex.exp wx) * Da‖ +
                  ‖Complex.exp wx * (Da - ca * Complex.exp wa)‖ := norm_add_le _ _
            _ ≤ _ := by
              gcongr
              calc
                _ ≤ ‖(Dx - cx * Complex.exp wx) * Pa +
                      (cx * Complex.exp wx) * (Pa - Complex.exp wa)‖ +
                      ‖(Px - Complex.exp wx) * Da‖ := norm_add_le _ _
                _ ≤ _ := by
                  gcongr
                  exact norm_add_le _ _
    _ = ‖Dx - cx * Complex.exp wx‖ * ‖Pa‖ +
        (‖cx‖ * ‖Complex.exp wx‖) * ‖Pa - Complex.exp wa‖ +
        ‖Px - Complex.exp wx‖ * ‖Da‖ +
        ‖Complex.exp wx‖ * ‖Da - ca * Complex.exp wa‖ +
        ‖Ds - cs * Complex.exp ws‖ := by
      repeat' rw [norm_mul]
    _ ≤
      (‖cx‖ * ((‖wx‖ ^ (2 * d) / (2 * d).factorial) * Real.exp ‖wx‖)) *
          Real.exp ‖wa‖ +
        ‖cx‖ * Real.exp ‖wx‖ *
          ((‖wa‖ ^ (2 * d + 1) / (2 * d + 1).factorial) * Real.exp ‖wa‖) +
        ((‖wx‖ ^ (2 * d + 1) / (2 * d + 1).factorial) * Real.exp ‖wx‖) *
          (‖ca‖ * Real.exp ‖wa‖) +
        Real.exp ‖wx‖ *
          (‖ca‖ * ((‖wa‖ ^ (2 * d) / (2 * d).factorial) * Real.exp ‖wa‖)) +
        ‖cs‖ * ((‖ws‖ ^ (2 * d) / (2 * d).factorial) * Real.exp ‖ws‖) := by
      gcongr
      · simpa only [Dx, cx, wx, norm_sub_rev] using
          norm_exp_derivative_sub_eval_derivative_finitePositivePhasePolynomial_le d x z
      · simpa only [Pa, wa] using
          norm_eval_finitePositivePhasePolynomial_le_exp_norm d a z
      · exact norm_complex_exp_le_exp_norm wx
      · simpa only [Pa, wa, norm_sub_rev] using
          norm_exp_sub_eval_finitePositivePhasePolynomial_le d z a
      · simpa only [Px, wx, norm_sub_rev] using
          norm_exp_sub_eval_finitePositivePhasePolynomial_le d z x
      · simpa only [Da, ca, wa] using
          norm_eval_derivative_finitePositivePhasePolynomial_le_exp_norm d a z
      · exact norm_complex_exp_le_exp_norm wx
      · simpa only [Da, ca, wa, norm_sub_rev] using
          norm_exp_derivative_sub_eval_derivative_finitePositivePhasePolynomial_le d a z
      · simpa only [Ds, cs, ws, norm_sub_rev] using
          norm_exp_derivative_sub_eval_derivative_finitePositivePhasePolynomial_le d (x + a) z
    _ = _ := by rfl

/-- On a nonnegative source half-line and a bounded spectral fibre, the value edge is bounded by
three copies of one shifted factorial envelope. -/
theorem norm_eval_finitePositivePhaseTranslationTopEdge_le_shiftedFactorialEnvelope
    (d R : ℕ) (x a : ℝ) (z : ℂ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hz : ‖z‖ ≤ R) :
    ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      3 * (((R : ℝ) * (x + a)) ^ (2 * d + 1) / (2 * d + 1).factorial *
        Real.exp ((R : ℝ) * (x + a))) := by
  let N : ℕ := 2 * d + 1
  let rx : ℝ := ‖(x : ℂ) * I * z‖
  let ra : ℝ := ‖(a : ℂ) * I * z‖
  let rs : ℝ := ‖((x + a : ℝ) : ℂ) * I * z‖
  let B : ℝ := (R : ℝ) * (x + a)
  have hxa : 0 ≤ x + a := add_nonneg hx ha
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ B := mul_nonneg hR hxa
  have hrx : rx = x * ‖z‖ := by simp [rx, abs_of_nonneg hx]
  have hra : ra = a * ‖z‖ := by simp [ra, abs_of_nonneg ha]
  have hrs : rs = (x + a) * ‖z‖ := by
    simp only [rs, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one, abs_of_nonneg hxa]
  have hrsle : rs ≤ B := by
    rw [hrs]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hxa]
  have hrxle : rx ≤ B := by
    rw [hrx]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hx]
  have hrale : ra ≤ B := by
    rw [hra]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz ha]
  have hsumle : rx + ra ≤ B := by
    rw [hrx, hra]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hxa]
  have htermX :
      (rx ^ N / N.factorial) * Real.exp rx * Real.exp ra ≤
        (B ^ N / N.factorial) * Real.exp B := by
    rw [show (rx ^ N / N.factorial) * Real.exp rx * Real.exp ra =
      (rx ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    gcongr
  have htermA :
      Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) ≤
        (B ^ N / N.factorial) * Real.exp B := by
    rw [show Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) =
      (ra ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    gcongr
  have htermS :
      (rs ^ N / N.factorial) * Real.exp rs ≤
        (B ^ N / N.factorial) * Real.exp B := by
    gcongr
  have h := norm_eval_finitePositivePhaseTranslationTopEdge_le d x a z
  change ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      (rx ^ N / N.factorial) * Real.exp rx * Real.exp ra +
        Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) +
        (rs ^ N / N.factorial) * Real.exp rs at h
  change ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      3 * (B ^ N / N.factorial * Real.exp B)
  nlinarith

/-- Multiplication by one source coordinate advances a factorial envelope by one order. -/
theorem mul_factorialEnvelope_eq_succ (N : ℕ) (B : ℝ) :
    B * (B ^ N / N.factorial) =
      (N + 1) * (B ^ (N + 1) / (N + 1).factorial) := by
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  rw [pow_succ]
  ring

/-- Continuity in the source coordinate of the evaluated positive phase section. -/
theorem continuous_eval_finitePositivePhasePolynomial (d : ℕ) (z : ℂ) :
    Continuous (fun x : ℝ => (finitePositivePhasePolynomial d x).eval z) := by
  have h : Continuous (fun x : ℝ =>
      ∑ m ∈ Finset.range (2 * d + 1),
        (((x : ℂ) * I * z) ^ m) / m.factorial) := by fun_prop
  convert h using 1
  funext x
  exact eval_finitePositivePhasePolynomial_eq_sum d z x

/-- Continuity in the source coordinate of the evaluated positive phase edge. -/
theorem continuous_eval_finitePositivePhaseTranslationTopEdge
    (d : ℕ) (a : ℝ) (z : ℂ) :
    Continuous (fun x : ℝ =>
      (finitePositivePhaseTranslationTopEdge d x a).eval z) := by
  have hphase := continuous_eval_finitePositivePhasePolynomial d z
  have h : Continuous (fun x : ℝ =>
      (finitePositivePhasePolynomial d x).eval z *
          (finitePositivePhasePolynomial d a).eval z -
        (finitePositivePhasePolynomial d (x + a)).eval z) :=
    (hphase.mul continuous_const).sub
      (hphase.comp (continuous_id.add continuous_const))
  convert h using 1
  funext x
  exact eval_finitePositivePhaseTranslationTopEdge d x a z

/-- Continuity in the source coordinate of the evaluated spectral derivative of the phase. -/
theorem continuous_eval_derivative_finitePositivePhasePolynomial (d : ℕ) (z : ℂ) :
    Continuous (fun x : ℝ =>
      (finitePositivePhasePolynomial d x).derivative.eval z) := by
  have h : Continuous (fun x : ℝ =>
      ((x : ℂ) * I) * ∑ m ∈ Finset.range (2 * d),
        (((x : ℂ) * I * z) ^ m) / m.factorial) := by fun_prop
  convert h using 1
  funext x
  exact eval_derivative_finitePositivePhasePolynomial_eq_sum d z x

/-- Continuity in the source coordinate of the evaluated derivative edge. -/
theorem continuous_eval_derivative_finitePositivePhaseTranslationTopEdge
    (d : ℕ) (a : ℝ) (z : ℂ) :
    Continuous (fun x : ℝ =>
      (finitePositivePhaseTranslationTopEdge d x a).derivative.eval z) := by
  have hphase := continuous_eval_finitePositivePhasePolynomial d z
  have hderiv := continuous_eval_derivative_finitePositivePhasePolynomial d z
  have h : Continuous (fun x : ℝ =>
      (finitePositivePhasePolynomial d x).derivative.eval z *
          (finitePositivePhasePolynomial d a).eval z +
        (finitePositivePhasePolynomial d x).eval z *
          (finitePositivePhasePolynomial d a).derivative.eval z -
        (finitePositivePhasePolynomial d (x + a)).derivative.eval z) :=
    ((hderiv.mul continuous_const).add (hphase.mul continuous_const)).sub
      (hderiv.comp (continuous_id.add continuous_const))
  convert h using 1
  funext x
  exact eval_derivative_finitePositivePhaseTranslationTopEdge d x a z

/-- The derivative edge is bounded by three order-`2d+1` and two order-`2d+2` shifted factorial
envelopes.  The only losses are the displayed linear cutoff factors. -/
theorem norm_eval_derivative_finitePositivePhaseTranslationTopEdge_le_shiftedFactorialEnvelope
    (d R : ℕ) (x a : ℝ) (z : ℂ)
    (hRone : 1 ≤ R) (hx : 0 ≤ x) (ha : 0 ≤ a) (hz : ‖z‖ ≤ R) :
    ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      3 * (2 * d + 1 : ℕ) *
          ((((R : ℝ) * (x + a)) ^ (2 * d + 1) / (2 * d + 1).factorial) *
            Real.exp ((R : ℝ) * (x + a))) +
        2 * (2 * d + 2 : ℕ) *
          ((((R : ℝ) * (x + a)) ^ (2 * d + 2) / (2 * d + 2).factorial) *
            Real.exp ((R : ℝ) * (x + a))) := by
  let M : ℕ := 2 * d
  let N : ℕ := M + 1
  let rx : ℝ := ‖(x : ℂ) * I * z‖
  let ra : ℝ := ‖(a : ℂ) * I * z‖
  let rs : ℝ := ‖((x + a : ℝ) : ℂ) * I * z‖
  let cx : ℝ := ‖(x : ℂ) * I‖
  let ca : ℝ := ‖(a : ℂ) * I‖
  let cs : ℝ := ‖((x + a : ℝ) : ℂ) * I‖
  let B : ℝ := (R : ℝ) * (x + a)
  let EN : ℝ := (B ^ N / N.factorial) * Real.exp B
  let EN1 : ℝ := (B ^ (N + 1) / (N + 1).factorial) * Real.exp B
  have hxa : 0 ≤ x + a := add_nonneg hx ha
  have hR : (1 : ℝ) ≤ R := by exact_mod_cast hRone
  have hB : 0 ≤ B := mul_nonneg (by positivity) hxa
  have hrx : rx = x * ‖z‖ := by simp [rx, abs_of_nonneg hx]
  have hra : ra = a * ‖z‖ := by simp [ra, abs_of_nonneg ha]
  have hrs : rs = (x + a) * ‖z‖ := by
    simp only [rs, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one, abs_of_nonneg hxa]
  have hcx : cx = x := by simp [cx, abs_of_nonneg hx]
  have hca : ca = a := by simp [ca, abs_of_nonneg ha]
  have hcs : cs = x + a := by
    simp only [cs, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one, abs_of_nonneg hxa]
  have hrsle : rs ≤ B := by
    rw [hrs]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hxa]
  have hrxle : rx ≤ B := by
    rw [hrx]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hx]
  have hrale : ra ≤ B := by
    rw [hra]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz ha]
  have hsumle : rx + ra ≤ B := by
    rw [hrx, hra]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hz hxa]
  have hcxle : cx ≤ B := by
    rw [hcx]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_right hR hxa]
  have hcale : ca ≤ B := by
    rw [hca]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_right hR hxa]
  have hcsle : cs ≤ B := by
    rw [hcs]
    dsimp [B]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hR hxa
  have hMN : N = 2 * d + 1 := by dsimp [N, M]
  have hderX :
      (cx * ((rx ^ M / M.factorial) * Real.exp rx)) * Real.exp ra ≤
        N * EN := by
    rw [show (cx * ((rx ^ M / M.factorial) * Real.exp rx)) * Real.exp ra =
      cx * (rx ^ M / M.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ M / M.factorial) * Real.exp B := by gcongr
      _ = N * EN := by
        dsimp [EN, N]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
  have hderA :
      Real.exp rx * (ca * ((ra ^ M / M.factorial) * Real.exp ra)) ≤
        N * EN := by
    rw [show Real.exp rx * (ca * ((ra ^ M / M.factorial) * Real.exp ra)) =
      ca * (ra ^ M / M.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ M / M.factorial) * Real.exp B := by gcongr
      _ = N * EN := by
        dsimp [EN, N]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
  have hderS :
      cs * ((rs ^ M / M.factorial) * Real.exp rs) ≤ N * EN := by
    have htailS : (rs ^ M / M.factorial) * Real.exp rs ≤
        (B ^ M / M.factorial) * Real.exp B := by gcongr
    calc
      _ ≤ B * ((B ^ M / M.factorial) * Real.exp B) :=
        mul_le_mul hcsle htailS (by positivity) hB
      _ = B * (B ^ M / M.factorial) * Real.exp B := by ring
      _ = N * EN := by
        dsimp [EN, N]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
  have hvalA :
      cx * Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) ≤
        (N + 1) * EN1 := by
    rw [show cx * Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) =
      cx * (ra ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ N / N.factorial) * Real.exp B := by gcongr
      _ = (N + 1) * EN1 := by
        dsimp only [EN1]
        rw [← mul_assoc, mul_factorialEnvelope_eq_succ]
  have hvalX :
      ((rx ^ N / N.factorial) * Real.exp rx) *
          (ca * Real.exp ra) ≤ (N + 1) * EN1 := by
    rw [show ((rx ^ N / N.factorial) * Real.exp rx) *
        (ca * Real.exp ra) =
      ca * (rx ^ N / N.factorial) * Real.exp (rx + ra) by rw [Real.exp_add]; ring]
    calc
      _ ≤ B * (B ^ N / N.factorial) * Real.exp B := by gcongr
      _ = (N + 1) * EN1 := by
        dsimp only [EN1]
        rw [← mul_assoc, mul_factorialEnvelope_eq_succ]
  have h := norm_eval_derivative_finitePositivePhaseTranslationTopEdge_le d x a z
  change ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      (cx * ((rx ^ M / M.factorial) * Real.exp rx)) * Real.exp ra +
        cx * Real.exp rx * ((ra ^ N / N.factorial) * Real.exp ra) +
        ((rx ^ N / N.factorial) * Real.exp rx) * (ca * Real.exp ra) +
        Real.exp rx * (ca * ((ra ^ M / M.factorial) * Real.exp ra)) +
        cs * ((rs ^ M / M.factorial) * Real.exp rs) at h
  have hcomb : ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      3 * N * EN + 2 * (N + 1) * EN1 := by nlinarith
  calc
    _ ≤ 3 * N * EN + 2 * (N + 1) * EN1 := hcomb
    _ = _ := by
      dsimp only [EN, EN1, B]
      rw [hMN]
      push_cast
      ring

/-- Every finite cosine section is dominated by the full exponential series, uniformly in its
degree.  This is the degree-free envelope used for the dyadic top row. -/
theorem norm_truncatedCosineSection_le_exp
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖truncatedCosineSection d z x‖ ≤ Real.exp (‖z‖ * |x|) := by
  let r : ℝ := ‖z‖ * |x|
  have hr : 0 ≤ r := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsum :
      ∑ k ∈ Finset.range (d + 1), r ^ (2 * k) / ((2 * k).factorial : ℝ) ≤
        Real.cosh r := by
    rw [Real.cosh_eq_tsum]
    exact (r.hasSum_cosh.summable).sum_le_tsum (Finset.range (d + 1))
      (fun k _hk => div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
  calc
    ‖truncatedCosineSection d z x‖ ≤
        ∑ k ∈ Finset.range (d + 1),
          r ^ (2 * k) / ((2 * k).factorial : ℝ) := by
      unfold truncatedCosineSection
      calc
        ‖∑ k ∈ Finset.range (d + 1),
            (-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k) / (2 * k).factorial‖ ≤
            ∑ k ∈ Finset.range (d + 1),
              ‖(-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k) /
                (2 * k).factorial‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range (d + 1),
            r ^ (2 * k) / ((2 * k).factorial : ℝ) := by
          apply Finset.sum_le_sum
          intro k _hk
          simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
          dsimp [r]
          exact le_rfl
    _ ≤ Real.cosh r := hsum
    _ ≤ Real.exp r := by
      rw [Real.cosh_eq]
      have hneg : Real.exp (-r) ≤ Real.exp r := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ = _ := rfl

/-- The odd companion enjoys the same degree-uniform exponential envelope. -/
theorem norm_truncatedSineCompanion_le_exp
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖truncatedSineCompanion d z x‖ ≤ Real.exp (‖z‖ * |x|) := by
  let r : ℝ := ‖z‖ * |x|
  have hr : 0 ≤ r := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsum :
      ∑ k ∈ Finset.range d, r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) ≤
        Real.sinh r := by
    rw [Real.sinh_eq_tsum]
    exact (r.hasSum_sinh.summable).sum_le_tsum (Finset.range d)
      (fun k _hk => div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
  calc
    ‖truncatedSineCompanion d z x‖ ≤
        ∑ k ∈ Finset.range d,
          r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
      unfold truncatedSineCompanion
      calc
        ‖∑ k ∈ Finset.range d,
            (-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k + 1) /
              (2 * k + 1).factorial‖ ≤
            ∑ k ∈ Finset.range d,
              ‖(-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k + 1) /
                (2 * k + 1).factorial‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range d,
            r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
          apply Finset.sum_le_sum
          intro k _hk
          simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
          dsimp [r]
          exact le_rfl
    _ ≤ Real.sinh r := hsum
    _ ≤ Real.exp r := by
      rw [Real.sinh_eq]
      have hneg : 0 < Real.exp (-r) := Real.exp_pos _
      linarith [Real.exp_pos r]
    _ = _ := rfl

/-- The spectral derivative of every finite cosine section has a degree-uniform exponential
envelope with the expected single source-coordinate factor. -/
theorem norm_truncatedCosineSectionDerivative_le
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖truncatedCosineSectionDerivative d z x‖ ≤
      |x| * Real.exp (‖z‖ * |x|) := by
  let r : ℝ := ‖z‖ * |x|
  have hr : 0 ≤ r := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsum :
      ∑ k ∈ Finset.range d,
          r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) ≤ Real.sinh r := by
    rw [Real.sinh_eq_tsum]
    exact (r.hasSum_sinh.summable).sum_le_tsum (Finset.range d)
      (fun k _hk => div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
  calc
    ‖truncatedCosineSectionDerivative d z x‖ ≤
        |x| * ∑ k ∈ Finset.range d,
          r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
      unfold truncatedCosineSectionDerivative
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
      calc
        ‖∑ k ∈ Finset.range d,
            (-1 : ℂ) ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℂ) *
              z ^ (2 * (k + 1) - 1) *
                ((x : ℂ) ^ (2 * (k + 1)) / (2 * (k + 1)).factorial)‖ ≤
            ∑ k ∈ Finset.range d,
              ‖(-1 : ℂ) ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℂ) *
                z ^ (2 * (k + 1) - 1) *
                  ((x : ℂ) ^ (2 * (k + 1)) / (2 * (k + 1)).factorial)‖ :=
          norm_sum_le _ _
        _ = |x| * ∑ k ∈ Finset.range d,
            r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [show 2 * (k + 1) = 2 * k + 2 by omega,
            show 2 * k + 2 - 1 = 2 * k + 1 by omega]
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast, norm_div, Complex.norm_real, Real.norm_eq_abs]
          have hfac : (2 * k + 2).factorial =
              (2 * k + 2) * (2 * k + 1).factorial := by
            rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ]
          rw [hfac]
          push_cast
          have hk : (0 : ℝ) < 2 * k + 2 := by positivity
          field_simp
          dsimp [r]
          rw [mul_pow]
          ring
    _ ≤ |x| * Real.sinh r := by gcongr
    _ ≤ |x| * Real.exp r := by
      gcongr
      rw [Real.sinh_eq]
      have hneg : 0 < Real.exp (-r) := Real.exp_pos _
      linarith [Real.exp_pos r]
    _ = _ := rfl

/-- Explicit constant for arbitrary-rate decay of every derivative of the raw theta tail. -/
def thetaCuspTailDerivativeNatExpConstant (m p : ℕ) : ℝ :=
  let P := thetaCuspTailDerivativePolynomial m
  thetaCuspCoeffMass P *
    Real.exp (((p + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
      ∑' n : ℕ,
        ((n + 1 : ℕ) : ℝ) ^ P.natDegree *
          Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)

/-- A polynomial Gaussian atom retains arbitrary natural exponential decay; its polynomial factor
is absorbed by the summable discrete Gaussian in the square index. -/
theorem exp_nat_mul_abs_thetaCuspPolynomialAtom_le_of_pos
    (P : ℝ[X]) (p : ℕ) {x : ℝ} (hx : 0 ≤ x) {q : ℕ} (hq : 0 < q) :
    Real.exp ((p : ℝ) * x) * |thetaCuspPolynomialAtom P q x| ≤
      thetaCuspCoeffMass P *
        Real.exp (((p + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
          (q : ℝ) ^ P.natDegree *
            Real.exp (-(Real.pi / 2) * (q : ℝ) ^ 2) := by
  let y : ℝ := (q : ℝ) * Real.exp x
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hexp1 : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  have hy1 : 1 ≤ y := by
    dsimp [y]
    nlinarith [Real.exp_pos x]
  have heval := abs_eval_le_coeffMass_mul_pow P hy1
  have hbase := exp_nat_mul_abs_thetaCuspTailAtom_le (p + P.natDegree) hx hq
  simp only [thetaCuspPolynomialAtom, eval_one, mul_one, abs_mul,
    abs_of_pos (Real.exp_pos _)] at hbase ⊢
  change Real.exp ((p : ℝ) * x) *
      (Real.exp (x / 2) * |eval y P| * Real.exp (-Real.pi * y ^ 2)) ≤ _
  change Real.exp (((p + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
      Real.exp (-(Real.pi / 2) * (q : ℝ) ^ 2) ≥
        Real.exp (((p + P.natDegree : ℕ) : ℝ) * x) *
          (Real.exp (x / 2) * Real.exp (-Real.pi * y ^ 2)) at hbase
  have hyPow : y ^ P.natDegree =
      (q : ℝ) ^ P.natDegree * Real.exp ((P.natDegree : ℝ) * x) := by
    dsimp [y]
    rw [mul_pow, ← Real.exp_nat_mul]
  rw [hyPow] at heval
  calc
    Real.exp ((p : ℝ) * x) *
        (Real.exp (x / 2) * |eval y P| * Real.exp (-Real.pi * y ^ 2)) ≤
      thetaCuspCoeffMass P * (q : ℝ) ^ P.natDegree *
        (Real.exp (((p + P.natDegree : ℕ) : ℝ) * x) *
          (Real.exp (x / 2) * Real.exp (-Real.pi * y ^ 2))) := by
      rw [show (((p + P.natDegree : ℕ) : ℝ)) =
          (p : ℝ) + (P.natDegree : ℝ) by norm_num,
        show ((p : ℝ) + (P.natDegree : ℝ)) * x =
          (p : ℝ) * x + (P.natDegree : ℝ) * x by ring,
        Real.exp_add]
      have hnon : 0 ≤ Real.exp ((p : ℝ) * x) * Real.exp (x / 2) *
          Real.exp (-Real.pi * y ^ 2) := by positivity
      nlinarith
    _ ≤ thetaCuspCoeffMass P * (q : ℝ) ^ P.natDegree *
        (Real.exp (((p + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
          Real.exp (-(Real.pi / 2) * (q : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left hbase
      exact mul_nonneg (thetaCuspCoeffMass_nonneg P)
        (pow_nonneg (Nat.cast_nonneg q) _)
    _ = _ := by ring

/-- Every raw-tail derivative decays at every prescribed natural exponential rate.  In
particular this gives degree-uniform domination of `rho = 4 T''` against bounded spectral
exponential envelopes. -/
theorem abs_thetaCuspTailDerivative_le_nat_exp_neg
    (m p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |thetaCuspTailDerivative m x| ≤
      thetaCuspTailDerivativeNatExpConstant m p * Real.exp (-(p : ℝ) * x) := by
  let P : ℝ[X] := thetaCuspTailDerivativePolynomial m
  let a : ℕ → ℝ := fun n => thetaCuspPolynomialAtom P (n + 1) x
  let g : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ) ^ P.natDegree *
      Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)
  let B : ℝ := thetaCuspCoeffMass P *
    Real.exp (((p + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi))
  have ha : Summable a := by
    simpa [a, P, thetaCuspTailDerivative] using summable_thetaCuspTailDerivative m x
  have hg : Summable g := by
    exact (summable_nat_add_iff 1).mpr
      (summable_pow_mul_exp_neg_nat_sq P.natDegree (by positivity : 0 < Real.pi / 2))
  have hag : Summable (fun n => Real.exp ((p : ℝ) * x) * |a n|) :=
    ha.norm.mul_left _
  have hBg : Summable (fun n => B * g n) := hg.mul_left _
  have hterm (n : ℕ) : Real.exp ((p : ℝ) * x) * |a n| ≤ B * g n := by
    dsimp [a, B, g, P]
    simpa only [mul_assoc] using
      exp_nat_mul_abs_thetaCuspPolynomialAtom_le_of_pos
        (thetaCuspTailDerivativePolynomial m) p hx (Nat.succ_pos n)
  have hsum : Real.exp ((p : ℝ) * x) * |∑' n, a n| ≤ B * ∑' n, g n := by
    calc
      Real.exp ((p : ℝ) * x) * |∑' n, a n| ≤
          Real.exp ((p : ℝ) * x) * ∑' n, |a n| := by
        gcongr
        exact norm_tsum_le_tsum_norm ha.norm
      _ = ∑' n, Real.exp ((p : ℝ) * x) * |a n| := by rw [tsum_mul_left]
      _ ≤ ∑' n, B * g n := hag.tsum_le_tsum hterm hBg
      _ = B * ∑' n, g n := by rw [tsum_mul_left]
  rw [thetaCuspTailDerivative]
  change |∑' n, a n| ≤ _
  calc
    |∑' n, a n| = Real.exp (-(p : ℝ) * x) *
        (Real.exp ((p : ℝ) * x) * |∑' n, a n|) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-(p : ℝ) * x) * (B * ∑' n, g n) := by gcongr
    _ = thetaCuspTailDerivativeNatExpConstant m p * Real.exp (-(p : ℝ) * x) := by
      simp [thetaCuspTailDerivativeNatExpConstant, B, P, g]
      ring

/-- Double integration by parts on a positive half-line, with all four endpoint values retained.
This abstract form is used for translated theta potentials: it prevents a seam term from being
silently lost when a reflected Haar packet is moved back to the positive source half-line. -/
theorem integral_Ioi_secondDerivative_mul_eq_boundary_add
    {a : ℝ} {f f' f'' : ℝ → ℂ} {g g' g'' : ℝ → ℂ}
    {A₁ B₁ A₂ B₂ : ℂ}
    (hf : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioi a, HasDerivAt f' (f'' x) x)
    (hg : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi a, HasDerivAt g' (g'' x) x)
    (hgf'' : IntegrableOn (g * f'') (Ioi a))
    (hg'f' : IntegrableOn (g' * f') (Ioi a))
    (hg''f : IntegrableOn (g'' * f) (Ioi a))
    (hzero₁ : Tendsto (g * f') (𝓝[>] a) (𝓝 A₁))
    (hinfty₁ : Tendsto (g * f') atTop (𝓝 B₁))
    (hzero₂ : Tendsto (g' * f) (𝓝[>] a) (𝓝 A₂))
    (hinfty₂ : Tendsto (g' * f) atTop (𝓝 B₂)) :
    (∫ x : ℝ in Ioi a, f'' x * g x) =
      (B₁ - A₁) - (B₂ - A₂) +
        ∫ x : ℝ in Ioi a, f x * g'' x := by
  have hfirst := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    hg hf' hgf'' hg'f' hzero₁ hinfty₁
  have hsecond := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    hg' hf hg'f' hg''f hzero₂ hinfty₂
  rw [show (∫ x : ℝ in Ioi a, f'' x * g x) =
      ∫ x : ℝ in Ioi a, g x * f'' x by
        apply integral_congr_ae
        filter_upwards [] with x
        ring,
    hfirst, hsecond]
  have hcomm : (∫ x : ℝ in Ioi a, g'' x * f x) =
      ∫ x : ℝ in Ioi a, f x * g'' x := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hcomm]
  ring

end


end RHTower
