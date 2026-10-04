import GaloisForLFunctions.RHTower.LiouvillePrimeBandSimpleZero
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Actual exponential weights have no summable Dirichlet square root

The complete prime-phase source has a simple zero for every sufficiently small
positive damping parameter. Evaluation of an absolutely summable convolution
square would be a holomorphic square on the phase disc, contradicting simplicity.
All public conclusions discharge the arithmetic and analytic inputs internally.
This rules out one proposed positivity construction; it does not decide the sign
of the literal Liouville density or the Riemann hypothesis.
-/

open Filter Finset
open scoped Topology BigOperators Classical

namespace RHTower.LiouvillePrimeBand
noncomputable section

/-- The complete exponential harmonic weight, including its zero-index convention. -/
def exponentialWeight (t : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => (Real.exp (-((n : ℝ)*t)) : ℂ) / (n : ℂ), by simp⟩

private theorem weight_apply_pow (t : ℝ) (n : ℕ) :
    exponentialWeight t n = (Real.exp (-t) : ℂ)^n / (n : ℂ) := by
  change (Real.exp (-((n : ℝ)*t)) : ℂ) / (n : ℂ) = _
  rw [show -((n : ℝ)*t) = (n : ℝ)*(-t) by ring, Real.exp_nat_mul, Complex.ofReal_pow]

private def twistArith (χ : ℕ →*₀ ℂ) (a : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => a n * χ n, by simp⟩

private def evalArith (χ : ℕ →*₀ ℂ) (a : ArithmeticFunction ℂ) : ℂ := ∑' n, a n * χ n

private theorem twistArith_mul (χ : ℕ →*₀ ℂ) (a b : ArithmeticFunction ℂ) :
    twistArith χ (a*b) = twistArith χ a * twistArith χ b := by
  ext n
  change (a*b) n * χ n = _
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  have hprod : q.1*q.2 = n := (Nat.mem_divisorsAntidiagonal.mp hq).1
  have hχ : χ n = χ q.1 * χ q.2 := by rw [← map_mul, hprod]
  rw [hχ]
  change _ = (a q.1 * χ q.1) * (b q.2 * χ q.2)
  ring

private theorem eval_eq_LSeries (χ : ℕ →*₀ ℂ) (a : ArithmeticFunction ℂ) :
    evalArith χ a = LSeries (⇑(twistArith χ a)) 0 := by
  unfold evalArith LSeries
  apply tsum_congr
  intro n
  rw [LSeries.term_def₀ (f := ⇑(twistArith χ a)) ArithmeticFunction.map_zero]
  simp [twistArith]

private theorem twisted_summable {χ : ℕ →*₀ ℂ} (hχ : ∀ n, ‖χ n‖ ≤ 1)
    {a : ArithmeticFunction ℂ} (ha : Summable (fun n => ‖a n‖)) :
    LSeriesSummable (⇑(twistArith χ a)) 0 := by
  have hs : Summable (fun n => a n * χ n) := ha.of_norm_bounded fun n => by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hχ n)
  unfold LSeriesSummable
  convert hs using 1
  funext n
  rw [LSeries.term_def₀ (f := ⇑(twistArith χ a)) ArithmeticFunction.map_zero]
  simp [twistArith]

private theorem evalArith_mul {χ : ℕ →*₀ ℂ} (hχ : ∀ n, ‖χ n‖ ≤ 1)
    {a b : ArithmeticFunction ℂ} (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖)) :
    evalArith χ (a*b) = evalArith χ a * evalArith χ b := by
  rw [eval_eq_LSeries, twistArith_mul, ArithmeticFunction.LSeries_mul'
    (twisted_summable hχ ha) (twisted_summable hχ hb),
    ← eval_eq_LSeries, ← eval_eq_LSeries]

private theorem norm_character_le_one {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) {z : ℂ} (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖character P β z n‖ ≤ 1 :=
  (norm_character_le_pow hβ z n).trans (pow_le_one₀ (norm_nonneg _) hz)

private theorem source_eq_weight_eval (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) (z : ℂ) :
    source P β t z = evalArith (character P β z) (exponentialWeight t) := by
  rw [source_eq_character, evalArith]
  apply tsum_congr
  intro n
  rw [weight_apply_pow]
  ring

private theorem differentiableOn_evaluation {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) {a : ArithmeticFunction ℂ}
    (ha : Summable (fun n => ‖a n‖)) :
    DifferentiableOn ℂ (fun z => evalArith (character P β z) a) (Metric.ball 0 1) := by
  unfold evalArith
  refine Complex.differentiableOn_tsum_of_summable_norm ha ?_ Metric.isOpen_ball ?_
  · intro n
    have he : (fun z : ℂ => a n * character P β z n) =
        (fun z : ℂ => (a n * character P β 1 n) * z ^ degree P n) := by
      funext z
      rw [character_eq_monomial P β z n]
      ring
    rw [he]
    fun_prop
  · intro n z hz
    rw [norm_mul]
    have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_character_le_one hβ hz'.le n)

private theorem no_square_of_simple_zero {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) {t : ℝ} {z : ℂ}
    (hz : ‖z‖ < 1) (hz0 : source P β t z = 0) (hder : deriv (source P β t) z ≠ 0) :
    ¬ ∃ a : ArithmeticFunction ℂ, Summable (fun n => ‖a n‖) ∧ a*a = exponentialWeight t := by
  rintro ⟨a, ha, hsq⟩
  let E : ℂ → ℂ := fun w => evalArith (character P β w) a
  have he : ∀ w : ℂ, ‖w‖ ≤ 1 → source P β t w = (E w)^2 := by
    intro w hw
    rw [source_eq_weight_eval, ← hsq, evalArith_mul (fun n => norm_character_le_one hβ hw n) ha ha]
    change E w * E w = (E w)^2
    ring
  have hEz : E z = 0 := by
    have hpow : (E z)^2 = 0 := by rw [← he z hz.le, hz0]
    have hm : E z * E z = 0 := by simpa only [pow_two] using hpow
    exact (mul_eq_zero.mp hm).elim id id
  have hdiff : DifferentiableAt ℂ E z := (differentiableOn_evaluation hβ ha).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right] using hz))
  have hd : HasDerivAt (E * E) 0 z := by
    simpa [hEz] using hdiff.hasDerivAt.mul hdiff.hasDerivAt
  have hevent : source P β t =ᶠ[𝓝 z] (E * E) := by
    have hnear : ∀ᶠ w : ℂ in 𝓝 z, ‖w‖ < 1 :=
      continuous_norm.continuousAt.tendsto.eventually (isOpen_Iio.mem_nhds hz)
    filter_upwards [hnear] with w hw
    simpa only [Pi.mul_apply, pow_two] using he w hw.le
  exact hder (hd.congr_of_eventuallyEq hevent).deriv


/-- At every sufficiently large real scale, the literal exponential weight has no complex
absolutely summable Dirichlet-convolution square root. -/
theorem eventually_no_summable_dirichlet_square_root :
    ∀ᶠ T : ℝ in atTop,
      ¬ ∃ a : ArithmeticFunction ℂ, Summable (fun n => ‖a n‖) ∧
        a*a = exponentialWeight (1/T) := by
  obtain ⟨a,b,c,d,_,_,_,_,hzero⟩ := exists_eventually_simple_prime_phase_zero
  filter_upwards [hzero] with T hT
  obtain ⟨β,hβ,z,hz,hz0,hder⟩ := hT
  exact no_square_of_simple_zero (fun p _ => hβ p) hz hz0 hder

/-- The square-root obstruction holds throughout a punctured interval of positive damping. -/
theorem exists_small_no_summable_dirichlet_square_root :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ¬ ∃ a : ArithmeticFunction ℂ, Summable (fun n => ‖a n‖) ∧ a*a = exponentialWeight t := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp eventually_no_summable_dirichlet_square_root
  let M : ℝ := max B 1 + 1
  have hM : 0 < M := by have := le_max_right B 1; dsimp [M]; linarith
  refine ⟨1/M, one_div_pos.mpr hM, fun t ht0 htδ => ?_⟩
  have hMT : M*t < 1 := by
    have h := (lt_div_iff₀ hM).mp htδ
    nlinarith
  have hinv : M < 1/t := (lt_div_iff₀ ht0).mpr hMT
  have hBT : B ≤ 1/t := by have := le_max_left B 1; dsimp [M] at hinv; linarith
  simpa only [one_div, inv_inv] using hB (1/t) hBT

/-- The universal absolutely summable square-root proposal for the actual weights is false. -/
theorem not_all_weights_have_summable_square_roots :
    ¬ ∀ t : ℝ, 0 < t → ∃ a : ArithmeticFunction ℂ,
      Summable (fun n => ‖a n‖) ∧ a*a = exponentialWeight t := by
  intro h
  obtain ⟨δ,hδ,hno⟩ := exists_small_no_summable_dirichlet_square_root
  exact hno (δ/2) (by linarith) (by linarith) (h (δ/2) (by linarith))

end
end RHTower.LiouvillePrimeBand
