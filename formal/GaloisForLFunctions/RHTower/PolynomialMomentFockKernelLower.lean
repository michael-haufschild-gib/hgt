import GaloisForLFunctions.RHTower.PolynomialFockTangentGaussian
import GaloisForLFunctions.RHTower.PolynomialMomentFockNorm
import GaloisForLFunctions.RHTower.GaussianAbsoluteMoment

/-!
# Sharp lower bound for the polynomial moment Fock kernel

An explicit exponential vector tangent to the radial weight is constructed inside the exact
coefficient carrier. Its weighted plane norm is controlled by the tangent Gaussian, while its
value at the base point is one. Reproducing-kernel duality then gives the real-axis lower bound.
-/

open MeasureTheory Set
open scoped Real

namespace RHTower

noncomputable section

/-- Gaussian upper bound for every exact polynomial Fock monomial moment. -/
theorem polynomialFockMoment_le_gaussian
    {m : ℝ} (hm : 2 ≤ m) (n : ℕ) :
    polynomialFockMoment m n ≤
      Real.pi * (1 / 2 : ℝ) ^ (n + 1) * n.factorial := by
  have hp := integrableOn_polynomialFockMomentIntegrand hm n
  have hg := integrableOn_pow_mul_exp_neg_mul_sq_Ioi_zero (2 * n + 1)
    (b := 2) (by norm_num)
  have hle :
      (∫ r in Ioi (0 : ℝ), polynomialFockMomentIntegrand m n r) ≤
        ∫ r in Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-(2 * r ^ 2)) := by
    apply MeasureTheory.integral_mono_ae hp hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := hr.le
    unfold polynomialFockMomentIntegrand
    rw [abs_of_pos hr]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (by
      have hpot := polynomialFockPotential_ge_sq (m := m) (r := r) hm
      linarith)
  have hformula := integral_rpow_mul_exp_neg_mul_sq_Ioi
    (sig := (2 * n + 1 : ℕ)) (b := 2)
      (by have h : (0 : ℝ) ≤ (2 * n + 1 : ℕ) := Nat.cast_nonneg _; linarith) (by norm_num)
  have hgauss :
      (∫ r in Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-(2 * r ^ 2))) =
        (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (n + 1) * n.factorial := by
    have hpow :
        (fun r : ℝ => r ^ (2 * n + 1) * Real.exp (-(2 * r ^ 2))) =
          fun r => r ^ ((2 * n + 1 : ℕ) : ℝ) * Real.exp (-2 * r ^ 2) := by
      funext r
      rw [Real.rpow_natCast]
      congr 1
      ring
    rw [hpow, hformula]
    have harg : (((2 * n + 1 : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 := by
      push_cast
      ring
    rw [harg, Real.Gamma_nat_eq_factorial]
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  unfold polynomialFockMoment
  rw [hgauss] at hle
  nlinarith [Real.pi_pos]

/-- Coefficients of the literal exponential in the polynomial moment carrier. -/
def polynomialFockExponentialSequence (m a : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (polynomialFockMoment m n) : ℂ) * (a : ℂ) ^ n / n.factorial

theorem summable_normSq_polynomialFockExponentialSequence
    {m : ℝ} (hm : 2 ≤ m) (a : ℝ) :
    Summable fun n => ‖polynomialFockExponentialSequence m a n‖ ^ (2 : ℝ) := by
  have hmajor : Summable fun n : ℕ =>
      (Real.pi / 2) * ((a ^ 2 / 2) ^ n / n.factorial) :=
    (NormedSpace.expSeries_div_hasSum_exp (a ^ 2 / 2)).summable.mul_left (Real.pi / 2)
  apply Summable.of_nonneg_of_le (f := fun n : ℕ =>
      (Real.pi / 2) * ((a ^ 2 / 2) ^ n / n.factorial))
    (g := fun n => ‖polynomialFockExponentialSequence m a n‖ ^ (2 : ℝ))
  · intro n
    positivity
  · intro n
    have hmoment := polynomialFockMoment_pos hm n
    have hmomentUpper := polynomialFockMoment_le_gaussian hm n
    have hnorma : ‖((a : ℂ) ^ n)‖ = |a| ^ n := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hnormfac : ‖((n.factorial : ℕ) : ℂ)‖ = (n.factorial : ℝ) := by simp
    rw [polynomialFockExponentialSequence, Real.rpow_two, norm_div, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hnorma, hnormfac,
      div_pow, mul_pow, Real.sq_sqrt hmoment.le]
    have hfact : (0 : ℝ) < n.factorial := by positivity
    have ha2 : (|a| ^ n) ^ 2 = (a ^ 2) ^ n := by
      calc
        (|a| ^ n) ^ 2 = |a| ^ (n * 2) := (pow_mul |a| n 2).symm
        _ = |a| ^ (2 * n) := by rw [mul_comm]
        _ = (|a| ^ 2) ^ n := pow_mul |a| 2 n
        _ = (a ^ 2) ^ n := by rw [sq_abs]
    rw [ha2]
    calc
      polynomialFockMoment m n * (a ^ 2) ^ n / (n.factorial : ℝ) ^ 2 ≤
          (Real.pi * (1 / 2 : ℝ) ^ (n + 1) * n.factorial) *
            (a ^ 2) ^ n / (n.factorial : ℝ) ^ 2 := by
        gcongr
      _ = (Real.pi / 2) * ((a ^ 2 / 2) ^ n / n.factorial) := by
        rw [pow_succ]
        field_simp
        ring
  · exact hmajor

/-- Literal exponential vector in the exact polynomial moment Fock carrier. -/
def polynomialMomentFockExponential
    (m : ℝ) (hm : 2 ≤ m) (a : ℝ) : MomentFock :=
  ⟨polynomialFockExponentialSequence m a,
    memℓp_gen (summable_normSq_polynomialFockExponentialSequence hm a)⟩

theorem momentFockCoefficient_polynomialMomentFockExponential
    (m : ℝ) (hm : 2 ≤ m) (a : ℝ) (n : ℕ) :
    momentFockCoefficient (polynomialMomentFockData m hm)
        (polynomialMomentFockExponential m hm a) n =
      (a : ℂ) ^ n / n.factorial := by
  have hsqrt : Real.sqrt (polynomialFockMoment m n) ≠ 0 :=
    (Real.sqrt_pos.2 (polynomialFockMoment_pos hm n)).ne'
  have hsqrtC : (Real.sqrt (polynomialFockMoment m n) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt
  unfold momentFockCoefficient polynomialMomentFockExponential
    polynomialFockExponentialSequence
  dsimp
  change ((Real.sqrt (polynomialFockMoment m n) : ℂ) * (a : ℂ) ^ n /
      (n.factorial : ℂ)) / (Real.sqrt (polynomialFockMoment m n) : ℂ) =
    (a : ℂ) ^ n / n.factorial
  field_simp [hsqrtC]

/-- Exponential coefficient vector represents the literal complex exponential. -/
theorem polynomialMomentFockFunction_exponential
    (m : ℝ) (hm : 2 ≤ m) (a : ℝ) (z : ℂ) :
    polynomialMomentFockFunction m hm (polynomialMomentFockExponential m hm a) z =
      Complex.exp ((a : ℂ) * z) := by
  unfold polynomialMomentFockFunction momentFockFunction
  rw [GaloisForLFunctions.HTGeometry.coeffFun_eq_tsum]
  simp_rw [momentFockCoefficient_polynomialMomentFockExponential]
  have hsum := NormedSpace.expSeries_div_hasSum_exp ((a : ℂ) * z)
  rw [Complex.exp_eq_exp_ℂ, ← hsum.tsum_eq]
  apply tsum_congr
  intro n
  rw [mul_pow]
  ring

/-- Holomorphic tangent exponential normalized to take value one at its base point. -/
def polynomialMomentFockTangentVector
    (m : ℝ) (hm : 2 ≤ m) (x : ℝ) : MomentFock :=
  (Real.exp (-(polynomialFockRadialSlope m x * x)) : ℂ) •
    polynomialMomentFockExponential m hm (polynomialFockRadialSlope m x)

theorem polynomialMomentFockFunction_tangentVector
    (m : ℝ) (hm : 2 ≤ m) (x : ℝ) (z : ℂ) :
    polynomialMomentFockFunction m hm (polynomialMomentFockTangentVector m hm x) z =
      Complex.exp ((polynomialFockRadialSlope m x : ℂ) * (z - x)) := by
  rw [polynomialMomentFockFunction_eq_evaluation]
  simp only [polynomialMomentFockTangentVector, map_smul]
  rw [← polynomialMomentFockFunction_eq_evaluation,
    polynomialMomentFockFunction_exponential]
  rw [Complex.ofReal_exp, smul_eq_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem polynomialMomentFockEvaluation_tangentVector_base
    (m : ℝ) (hm : 2 ≤ m) (x : ℝ) :
    polynomialMomentFockEvaluation m hm (x : ℂ)
      (polynomialMomentFockTangentVector m hm x) = 1 := by
  rw [← polynomialMomentFockFunction_eq_evaluation,
    polynomialMomentFockFunction_tangentVector]
  simp

theorem polynomialMomentFockWeightedNormSq_tangentVector
    (m : ℝ) (hm : 2 ≤ m) (x : ℝ) (z : ℂ) :
    polynomialMomentFockWeightedNormSq m hm
        (polynomialMomentFockTangentVector m hm x) z =
      polynomialFockTangentDensity m x z := by
  rw [polynomialMomentFockWeightedNormSq,
    polynomialMomentFockFunction_tangentVector]
  rw [Complex.norm_exp]
  unfold polynomialFockTangentDensity
  rw [← Real.exp_nat_mul]
  rw [← Real.exp_add]
  congr 1
  simp
  ring

/-- Exact tangent vector has adapted Gaussian norm upper bound. -/
theorem normSq_polynomialMomentFockTangentVector_le
    (m : ℝ) (hm : 2 ≤ m) (x : ℝ) :
    ‖polynomialMomentFockTangentVector m hm x‖ ^ 2 ≤
      Real.exp (-2 * polynomialFockPotential m x) *
        (Real.pi / (m * (1 + x ^ 2) ^ (m / 2 - 1))) := by
  rw [← integral_polynomialMomentFockWeightedNormSq m hm]
  have heq :
      (fun z : ℂ => polynomialMomentFockWeightedNormSq m hm
        (polynomialMomentFockTangentVector m hm x) z) =
      polynomialFockTangentDensity m x := by
    funext z
    exact polynomialMomentFockWeightedNormSq_tangentVector m hm x z
  rw [heq]
  exact integral_polynomialFockTangentDensity_le hm

/-- Sharp real-axis diagonal-kernel lower bound from normalized tangent exponential. -/
theorem normSq_polynomialMomentFockKernel_lower
    {m : ℝ} (hm : 2 ≤ m) (x : ℝ) :
    Real.exp (2 * polynomialFockPotential m x) *
        (m * (1 + x ^ 2) ^ (m / 2 - 1) / Real.pi) ≤
      ‖momentFockKernel (polynomialMomentFockData m hm) (x : ℂ)‖ ^ 2 := by
  let K : ℝ := ‖momentFockKernel (polynomialMomentFockData m hm) (x : ℂ)‖
  let T : ℝ := ‖polynomialMomentFockTangentVector m hm x‖
  let c : ℝ := m * (1 + x ^ 2) ^ (m / 2 - 1)
  let E : ℝ := Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / c)
  let D : ℝ := Real.exp (2 * polynomialFockPotential m x) * (c / Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT : T ^ 2 ≤ E := by
    dsimp [T, E, c]
    exact normSq_polynomialMomentFockTangentVector_le m hm x
  have hprod : 1 ≤ K * T := by
    have h := norm_momentFockEvaluation_apply_le
      (polynomialMomentFockData m hm) (x : ℂ)
      (polynomialMomentFockTangentVector m hm x)
    change ‖polynomialMomentFockEvaluation m hm (x : ℂ)
        (polynomialMomentFockTangentVector m hm x)‖ ≤ K * T at h
    rw [polynomialMomentFockEvaluation_tangentVector_base, norm_one] at h
    exact h
  have hsq : 1 ≤ K ^ 2 * T ^ 2 := by nlinarith
  have hone : 1 ≤ K ^ 2 * E :=
    hsq.trans (mul_le_mul_of_nonneg_left hT (sq_nonneg K))
  have hD : 0 ≤ D := by dsimp [D, c]; positivity
  have hDE : D * E = 1 := by
    have hc0 : c ≠ 0 := hc.ne'
    have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
    have hexp : Real.exp (2 * polynomialFockPotential m x) *
        Real.exp (-2 * polynomialFockPotential m x) = 1 := by
      rw [← Real.exp_add]
      simp
    have hfrac : (c / Real.pi) * (Real.pi / c) = 1 := by field_simp
    dsimp [D, E]
    calc
      Real.exp (2 * polynomialFockPotential m x) * (c / Real.pi) *
          (Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / c)) =
        (Real.exp (2 * polynomialFockPotential m x) *
          Real.exp (-2 * polynomialFockPotential m x)) *
            ((c / Real.pi) * (Real.pi / c)) := by ring
      _ = 1 := by rw [hexp, hfrac, mul_one]
  change D ≤ K ^ 2
  calc
    D = D * 1 := by ring
    _ ≤ D * (K ^ 2 * E) := mul_le_mul_of_nonneg_left hone hD
    _ = K ^ 2 * (D * E) := by ring
    _ = K ^ 2 := by rw [hDE, mul_one]

end

end RHTower
