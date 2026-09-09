import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffComplexAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exact entire extension of the actual cutoff group

The identity theorem identifies the literal complex multiplier with the
operator exponential. Every derivative is the corresponding generator
power, and the exact norm characterizes real time as the entire unitary locus.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Each complex derivative factors through the same actual bounded time generator. -/
theorem cutoffComplexOperator_succ_eq_generator_comp (a : ℝ) (n : ℕ) (τ : ℂ) :
    cutoffComplexOperator a (n+1) τ =
      (cutoffEvolutionTimeOperator a 0).comp (cutoffComplexOperator a n τ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [cutoffComplexOperator_ae a (n+1) τ u,
    cutoffEvolutionTimeOperator_ae a 0 (cutoffComplexOperator a n τ u),
    cutoffComplexOperator_ae a n τ u] with z h0 h1 h2
  change (cutoffComplexOperator a (n+1) τ u) z =
    (cutoffEvolutionTimeOperator a 0 (cutoffComplexOperator a n τ u)) z
  rw [h0,h1,h2]
  simp only [cutoffComplexSymbol,cutoffPhaseTimeSymbol,cutoffPhase,zero_mul,Complex.ofReal_zero,
    neg_zero,zero_mul,Complex.exp_zero,mul_one,pow_succ]
  ring

/-- Every complex derivative is the actual generator power times the zeroth multiplier. -/
theorem cutoffComplexOperator_eq_pow_mul (a : ℝ) (n : ℕ) (τ : ℂ) :
    cutoffComplexOperator a n τ = cutoffEvolutionTimeOperator a 0 ^ n * cutoffComplexOperator a 0 τ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cutoffComplexOperator_succ_eq_generator_comp,ih]
    change cutoffEvolutionTimeOperator a 0 *
      (cutoffEvolutionTimeOperator a 0 ^ n * cutoffComplexOperator a 0 τ) = _
    rw [pow_succ',mul_assoc]

/-- Real restriction preserves every previously audited derivative operator, exactly. -/
theorem cutoffComplexOperator_ofReal (a t : ℝ) (n : ℕ) :
    cutoffComplexOperator a n (t : ℂ) = cutoffEvolutionDerivative a n t := by
  rw [cutoffComplexOperator_eq_pow_mul,cutoffComplexOperator_zero_ofReal]
  rfl

/-- The actual complex-time multiplier is exactly the entire operator exponential. -/
theorem cutoffComplexOperator_eq_exp (a : ℝ) (τ : ℂ) :
    cutoffComplexOperator a 0 τ = NormedSpace.exp (τ • cutoffEvolutionTimeOperator a 0) := by
  have hf : AnalyticOnNhd ℂ (cutoffComplexOperator a 0) Set.univ :=
    fun t _ => cutoffComplexOperator_analyticAt a 0 t
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => NormedSpace.exp (t • cutoffEvolutionTimeOperator a 0)) Set.univ := by
    intro t _
    have hl : AnalyticAt ℂ (fun s : ℂ => s • cutoffEvolutionTimeOperator a 0) t := by fun_prop
    exact (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp hl
  have ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ)+1) : ℝ) : ℂ)) atTop (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · apply Eventually.of_forall
      intro n
      simp only [mem_compl_iff,mem_singleton_iff,Complex.ofReal_eq_zero]
      positivity
  have he : cutoffComplexOperator a 0 = fun t : ℂ => NormedSpace.exp (t • cutoffEvolutionTimeOperator a 0) := by
    apply hf.eq_of_frequently_eq hg
    apply ht.frequently
    apply (Eventually.of_forall ?_).frequently
    intro n
    rw [cutoffComplexOperator_zero_ofReal,Complex.coe_smul,cutoffEvolution_eq_exp]
  exact congrFun he τ

/-- Every complex derivative is a generator power times the actual operator exponential. -/
theorem cutoffComplexOperator_eq_pow_exp (a : ℝ) (n : ℕ) (τ : ℂ) :
    cutoffComplexOperator a n τ =
      cutoffEvolutionTimeOperator a 0 ^ n * NormedSpace.exp (τ • cutoffEvolutionTimeOperator a 0) := by
  rw [cutoffComplexOperator_eq_pow_mul,cutoffComplexOperator_eq_exp]

/-- The actual generator exponential has its exact vertical complex-time growth. -/
theorem norm_exp_cutoffGenerator (a : ℝ) (τ : ℂ) :
    ‖NormedSpace.exp (τ • cutoffEvolutionTimeOperator a 0)‖ =
      Real.exp (|τ.im| * cutoffPhaseBudget a) := by
  rw [← cutoffComplexOperator_eq_exp,norm_cutoffComplexOperator,pow_zero,one_mul]

/-- Norm one occurs exactly on the real-time axis. -/
theorem norm_cutoffComplexOperator_eq_one_iff (a : ℝ) (τ : ℂ) :
    ‖cutoffComplexOperator a 0 τ‖ = 1 ↔ τ.im = 0 := by
  rw [norm_cutoffComplexOperator,pow_zero,one_mul,Real.exp_eq_one_iff,
    mul_eq_zero,or_iff_left (ne_of_gt (cutoffPhaseBudget_pos a)),abs_eq_zero]

/-- The real axis is exactly the unitary locus of the actual entire operator family. -/
theorem cutoffComplexOperator_mem_unitary_iff (a : ℝ) (τ : ℂ) :
    cutoffComplexOperator a 0 τ ∈ unitary (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) ↔
      τ.im = 0 := by
  constructor
  · intro h
    exact (norm_cutoffComplexOperator_eq_one_iff a τ).1 (CStarRing.norm_of_mem_unitary h)
  · intro h
    have he : τ = (τ.re : ℂ) := by apply Complex.ext <;> simp [h]
    rw [he,cutoffComplexOperator_zero_ofReal]
    exact cutoffEvolution_mem_unitary a τ.re


/-- Every complex-time operator remains invertible on the original Hilbert space. -/
theorem isUnit_cutoffComplexOperator (a : ℝ) (τ : ℂ) :
    IsUnit (cutoffComplexOperator a 0 τ) := by
  letI : NormedAlgebra ℚ (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :=
    .restrictScalars ℚ ℂ _
  rw [cutoffComplexOperator_eq_exp]
  exact NormedSpace.isUnit_exp _

/-- The actual algebraic inverse is precisely evolution at the negative complex time. -/
theorem ringInverse_cutoffComplexOperator (a : ℝ) (τ : ℂ) :
    Ring.inverse (cutoffComplexOperator a 0 τ) = cutoffComplexOperator a 0 (-τ) := by
  letI : NormedAlgebra ℚ (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :=
    .restrictScalars ℚ ℂ _
  rw [cutoffComplexOperator_eq_exp,cutoffComplexOperator_eq_exp,Ring.inverse_exp,neg_smul]

/-- Exact norm conditioning: forward and inverse growth multiply to twice the vertical exponent. -/
theorem cutoffComplexOperator_condition_number (a : ℝ) (τ : ℂ) :
    ‖cutoffComplexOperator a 0 τ‖ * ‖Ring.inverse (cutoffComplexOperator a 0 τ)‖ =
      Real.exp (2 * |τ.im| * cutoffPhaseBudget a) := by
  rw [ringInverse_cutoffComplexOperator,norm_cutoffComplexOperator,norm_cutoffComplexOperator]
  simp only [pow_zero,one_mul,Complex.neg_im,abs_neg]
  rw [← Real.exp_add]
  congr 1
  ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
