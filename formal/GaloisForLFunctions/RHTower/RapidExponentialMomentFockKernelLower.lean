import GaloisForLFunctions.RHTower.RapidExponentialFockTangentGaussian
import GaloisForLFunctions.RHTower.RapidExponentialMomentFockNorm
import GaloisForLFunctions.RHTower.GaussianAbsoluteMoment

/-!
# Lower bound for the rapid exponential moment Fock kernel

An explicit normalized tangent exponential lies in the exact coefficient carrier.  Its weighted
plane norm is controlled by the global tangent Gaussian, and reproducing-kernel duality gives a
quantitative real-axis diagonal lower bound.  The retained polynomial loss is explicit.
-/

open MeasureTheory Set
open scoped Real

namespace RHTower

noncomputable section

/-- Gaussian upper bound for every rapid exponential Fock monomial moment. -/
theorem rapidExponentialFockMoment_le_gaussian
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    rapidExponentialFockMoment a n ≤
      Real.pi * (1 / (2 * a ^ 2) : ℝ) ^ (n + 1) * n.factorial := by
  have hp := integrableOn_rapidExponentialFockMomentIntegrand ha n
  have hb : 0 < 2 * a ^ 2 := by positivity
  have hg := integrableOn_pow_mul_exp_neg_mul_sq_Ioi_zero (2 * n + 1) hb
  have hle :
      (∫ r in Ioi (0 : ℝ), rapidExponentialFockMomentIntegrand a n r) ≤
        ∫ r in Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-(2 * a ^ 2 * r ^ 2)) := by
    apply MeasureTheory.integral_mono_ae hp hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := hr.le
    have har0 : 0 ≤ a * r := mul_nonneg ha.le hr0
    have hlinear : a * r ≤ Real.exp (a * r) := by
      linarith [Real.add_one_le_exp (a * r)]
    have hsquare : (a * r) ^ 2 ≤ Real.exp (a * r) ^ 2 :=
      (sq_le_sq₀ har0 (Real.exp_pos _).le).2 hlinear
    have hpotential : a ^ 2 * r ^ 2 ≤ rapidExponentialFockPotential a r := by
      unfold rapidExponentialFockPotential
      calc
        a ^ 2 * r ^ 2 = (a * r) ^ 2 := by ring
        _ ≤ Real.exp (a * r) ^ 2 := hsquare
        _ = Real.exp (2 * a * r) := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
    have hexp :
        Real.exp (-2 * rapidExponentialFockPotential a r) ≤
          Real.exp (-(2 * a ^ 2 * r ^ 2)) := by
      rw [Real.exp_le_exp]
      linarith
    unfold rapidExponentialFockMomentIntegrand
    rw [abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hformula := integral_rpow_mul_exp_neg_mul_sq_Ioi
    (sig := (2 * n + 1 : ℕ)) (b := 2 * a ^ 2)
      (by have h : (0 : ℝ) ≤ (2 * n + 1 : ℕ) := Nat.cast_nonneg _; linarith) hb
  have hgauss :
      (∫ r in Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-(2 * a ^ 2 * r ^ 2))) =
        (1 / 2 : ℝ) * (1 / (2 * a ^ 2) : ℝ) ^ (n + 1) * n.factorial := by
    have hpow :
        (fun r : ℝ => r ^ (2 * n + 1) * Real.exp (-(2 * a ^ 2 * r ^ 2))) =
          fun r => r ^ ((2 * n + 1 : ℕ) : ℝ) * Real.exp (-(2 * a ^ 2) * r ^ 2) := by
      funext r
      rw [Real.rpow_natCast]
      congr 1
      ring_nf
    rw [hpow, hformula]
    have harg : (((2 * n + 1 : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 := by
      push_cast
      ring
    rw [harg, Real.Gamma_nat_eq_factorial]
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  unfold rapidExponentialFockMoment
  rw [hgauss] at hle
  nlinarith [Real.pi_pos]

/-- Coefficients of a literal exponential in the rapid moment carrier. -/
def rapidExponentialFockExponentialSequence (a s : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (rapidExponentialFockMoment a n) : ℂ) * (s : ℂ) ^ n / n.factorial

theorem summable_normSq_rapidExponentialFockExponentialSequence
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Summable fun n => ‖rapidExponentialFockExponentialSequence a s n‖ ^ (2 : ℝ) := by
  let B : ℝ := 1 / (2 * a ^ 2)
  have hB : 0 < B := by dsimp [B]; positivity
  have hmajor : Summable fun n : ℕ =>
      (Real.pi * B) * ((B * s ^ 2) ^ n / n.factorial) :=
    (NormedSpace.expSeries_div_hasSum_exp (B * s ^ 2)).summable.mul_left (Real.pi * B)
  apply Summable.of_nonneg_of_le
    (f := fun n : ℕ => (Real.pi * B) * ((B * s ^ 2) ^ n / n.factorial))
    (g := fun n => ‖rapidExponentialFockExponentialSequence a s n‖ ^ (2 : ℝ))
  · intro n
    positivity
  · intro n
    have hmoment := rapidExponentialFockMoment_pos ha n
    have hmomentUpper := rapidExponentialFockMoment_le_gaussian ha n
    have hnorms : ‖((s : ℂ) ^ n)‖ = |s| ^ n := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hnormfac : ‖((n.factorial : ℕ) : ℂ)‖ = (n.factorial : ℝ) := by simp
    rw [rapidExponentialFockExponentialSequence, Real.rpow_two, norm_div, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hnorms, hnormfac,
      div_pow, mul_pow, Real.sq_sqrt hmoment.le]
    have hfact : (0 : ℝ) < n.factorial := by positivity
    have hs2 : (|s| ^ n) ^ 2 = (s ^ 2) ^ n := by
      calc
        (|s| ^ n) ^ 2 = |s| ^ (n * 2) := (pow_mul |s| n 2).symm
        _ = |s| ^ (2 * n) := by rw [mul_comm]
        _ = (|s| ^ 2) ^ n := pow_mul |s| 2 n
        _ = (s ^ 2) ^ n := by rw [sq_abs]
    rw [hs2]
    calc
      rapidExponentialFockMoment a n * (s ^ 2) ^ n / (n.factorial : ℝ) ^ 2 ≤
          (Real.pi * B ^ (n + 1) * n.factorial) *
            (s ^ 2) ^ n / (n.factorial : ℝ) ^ 2 := by
        dsimp [B]
        gcongr
      _ = (Real.pi * B) * ((B * s ^ 2) ^ n / n.factorial) := by
        rw [pow_succ]
        field_simp
        ring
  · exact hmajor

/-- Literal exponential vector in the exact rapid moment Fock carrier. -/
def rapidExponentialMomentFockExponential
    (a : ℝ) (ha : 0 < a) (s : ℝ) : MomentFock :=
  ⟨rapidExponentialFockExponentialSequence a s,
    memℓp_gen (summable_normSq_rapidExponentialFockExponentialSequence ha s)⟩

theorem momentFockCoefficient_rapidExponentialMomentFockExponential
    (a : ℝ) (ha : 0 < a) (s : ℝ) (n : ℕ) :
    momentFockCoefficient (rapidExponentialMomentFockData a ha)
        (rapidExponentialMomentFockExponential a ha s) n =
      (s : ℂ) ^ n / n.factorial := by
  have hsqrt : Real.sqrt (rapidExponentialFockMoment a n) ≠ 0 :=
    (Real.sqrt_pos.2 (rapidExponentialFockMoment_pos ha n)).ne'
  have hsqrtC : (Real.sqrt (rapidExponentialFockMoment a n) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt
  unfold momentFockCoefficient rapidExponentialMomentFockExponential
    rapidExponentialFockExponentialSequence
  dsimp
  change ((Real.sqrt (rapidExponentialFockMoment a n) : ℂ) * (s : ℂ) ^ n /
      (n.factorial : ℂ)) / (Real.sqrt (rapidExponentialFockMoment a n) : ℂ) =
    (s : ℂ) ^ n / n.factorial
  field_simp [hsqrtC]

/-- Exponential coefficient vector represents the literal complex exponential. -/
theorem rapidExponentialMomentFockFunction_exponential
    (a : ℝ) (ha : 0 < a) (s : ℝ) (z : ℂ) :
    rapidExponentialMomentFockFunction a ha
        (rapidExponentialMomentFockExponential a ha s) z =
      Complex.exp ((s : ℂ) * z) := by
  unfold rapidExponentialMomentFockFunction momentFockFunction
  rw [GaloisForLFunctions.HTGeometry.coeffFun_eq_tsum]
  simp_rw [momentFockCoefficient_rapidExponentialMomentFockExponential]
  have hsum := NormedSpace.expSeries_div_hasSum_exp ((s : ℂ) * z)
  rw [Complex.exp_eq_exp_ℂ, ← hsum.tsum_eq]
  apply tsum_congr
  intro n
  rw [mul_pow]
  ring

/-- Holomorphic tangent exponential normalized to take value one at its base point. -/
def rapidExponentialMomentFockTangentVector
    (a : ℝ) (ha : 0 < a) (x : ℝ) : MomentFock :=
  (Real.exp (-(rapidExponentialFockRadialSlope a x * x)) : ℂ) •
    rapidExponentialMomentFockExponential a ha (rapidExponentialFockRadialSlope a x)

theorem rapidExponentialMomentFockFunction_tangentVector
    (a : ℝ) (ha : 0 < a) (x : ℝ) (z : ℂ) :
    rapidExponentialMomentFockFunction a ha
        (rapidExponentialMomentFockTangentVector a ha x) z =
      Complex.exp ((rapidExponentialFockRadialSlope a x : ℂ) * (z - x)) := by
  rw [rapidExponentialMomentFockFunction_eq_evaluation]
  simp only [rapidExponentialMomentFockTangentVector, map_smul]
  rw [← rapidExponentialMomentFockFunction_eq_evaluation,
    rapidExponentialMomentFockFunction_exponential]
  rw [Complex.ofReal_exp, smul_eq_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rapidExponentialMomentFockEvaluation_tangentVector_base
    (a : ℝ) (ha : 0 < a) (x : ℝ) :
    rapidExponentialMomentFockEvaluation a ha (x : ℂ)
      (rapidExponentialMomentFockTangentVector a ha x) = 1 := by
  rw [← rapidExponentialMomentFockFunction_eq_evaluation,
    rapidExponentialMomentFockFunction_tangentVector]
  simp

theorem rapidExponentialMomentFockWeightedNormSq_tangentVector
    (a : ℝ) (ha : 0 < a) (x : ℝ) (z : ℂ) :
    rapidExponentialMomentFockWeightedNormSq a ha
        (rapidExponentialMomentFockTangentVector a ha x) z =
      rapidExponentialFockTangentDensity a x z := by
  rw [rapidExponentialMomentFockWeightedNormSq,
    rapidExponentialMomentFockFunction_tangentVector]
  rw [Complex.norm_exp]
  unfold rapidExponentialFockTangentDensity
  rw [← Real.exp_nat_mul]
  rw [← Real.exp_add]
  congr 1
  simp
  ring

/-- Exact tangent vector has the explicit global Gaussian norm upper bound. -/
theorem normSq_rapidExponentialMomentFockTangentVector_le
    (a : ℝ) (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    ‖rapidExponentialMomentFockTangentVector a ha x‖ ^ 2 ≤
      Real.exp (-2 * rapidExponentialFockPotential a x) *
        (Real.pi / (2 * rapidExponentialFockTangentCurvature a x)) := by
  rw [← integral_rapidExponentialMomentFockWeightedNormSq a ha]
  have heq :
      (fun z : ℂ => rapidExponentialMomentFockWeightedNormSq a ha
        (rapidExponentialMomentFockTangentVector a ha x) z) =
      rapidExponentialFockTangentDensity a x := by
    funext z
    exact rapidExponentialMomentFockWeightedNormSq_tangentVector a ha x z
  rw [heq]
  exact integral_rapidExponentialFockTangentDensity_le ha hx

/-- Real-axis diagonal-kernel lower bound from the normalized tangent exponential. -/
theorem normSq_rapidExponentialMomentFockKernel_lower
    {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (2 * rapidExponentialFockPotential a x) *
        (2 * rapidExponentialFockTangentCurvature a x / Real.pi) ≤
      ‖momentFockKernel (rapidExponentialMomentFockData a ha) (x : ℂ)‖ ^ 2 := by
  let K : ℝ := ‖momentFockKernel (rapidExponentialMomentFockData a ha) (x : ℂ)‖
  let T : ℝ := ‖rapidExponentialMomentFockTangentVector a ha x‖
  let c : ℝ := 2 * rapidExponentialFockTangentCurvature a x
  let E : ℝ := Real.exp (-2 * rapidExponentialFockPotential a x) * (Real.pi / c)
  let D : ℝ := Real.exp (2 * rapidExponentialFockPotential a x) * (c / Real.pi)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (by norm_num) (rapidExponentialFockTangentCurvature_pos ha hx)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT : T ^ 2 ≤ E := by
    dsimp [T, E, c]
    exact normSq_rapidExponentialMomentFockTangentVector_le a ha hx
  have hprod : 1 ≤ K * T := by
    have h := norm_momentFockEvaluation_apply_le
      (rapidExponentialMomentFockData a ha) (x : ℂ)
      (rapidExponentialMomentFockTangentVector a ha x)
    change ‖rapidExponentialMomentFockEvaluation a ha (x : ℂ)
        (rapidExponentialMomentFockTangentVector a ha x)‖ ≤ K * T at h
    rw [rapidExponentialMomentFockEvaluation_tangentVector_base, norm_one] at h
    exact h
  have hsq : 1 ≤ K ^ 2 * T ^ 2 := by nlinarith
  have hone : 1 ≤ K ^ 2 * E :=
    hsq.trans (mul_le_mul_of_nonneg_left hT (sq_nonneg K))
  have hD : 0 ≤ D := by dsimp [D, c]; positivity
  have hDE : D * E = 1 := by
    have hc0 : c ≠ 0 := hc.ne'
    have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
    have hexp : Real.exp (2 * rapidExponentialFockPotential a x) *
        Real.exp (-2 * rapidExponentialFockPotential a x) = 1 := by
      rw [← Real.exp_add]
      simp
    have hfrac : (c / Real.pi) * (Real.pi / c) = 1 := by field_simp
    dsimp [D, E]
    calc
      Real.exp (2 * rapidExponentialFockPotential a x) * (c / Real.pi) *
          (Real.exp (-2 * rapidExponentialFockPotential a x) * (Real.pi / c)) =
        (Real.exp (2 * rapidExponentialFockPotential a x) *
          Real.exp (-2 * rapidExponentialFockPotential a x)) *
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
