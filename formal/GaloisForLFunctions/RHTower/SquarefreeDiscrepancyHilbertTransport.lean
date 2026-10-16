import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyMellin
import GaloisForLFunctions.HTGeometry.L2CauchyHolomorphy
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# A fixed Hilbert source for the squarefree counting discrepancy

Summing the arithmetic coefficients and subtracting their exact density precedes
Hilbert admission. In logarithmic coordinates the fixed source is
`E(exp t) exp(-t/2)/(1+t)`, supported on the positive ray. Its pairing with
`(1+t) exp(-(s-1/2)t)` is the discrepancy Mellin moment throughout `Re s > 1/2`.
The evaluation vectors are strongly holomorphic in the actual L² quotient.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace RHTower.SquarefreeDiscrepancy

open GaloisForLFunctions.HTGeometry

/-- The fixed continuum carrier, with Lebesgue measure in logarithmic scale. -/
abbrev LogHilbert := Lp ℂ 2 (volume : Measure ℝ)

/-- Arithmetic summatory cancellation, followed by a logarithmic Hilbert weight. -/
def hilbertSourceFunction : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator fun t =>
    ((error (Real.exp t) * Real.exp (-t / 2) / (1 + t) : ℝ) : ℂ)

/-- The evaluation kernel keeps the original spectral coordinate. -/
def hilbertEvaluationFunction (s : ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator fun t =>
    ((1 + t : ℝ) : ℂ) * Complex.exp (-(s - 1 / 2) * (t : ℂ))

theorem measurable_hilbertSourceFunction : Measurable hilbertSourceFunction := by
  have hE : Measurable (fun t : ℝ => error (Real.exp t)) :=
    measurable_error.comp Real.measurable_exp
  have hw : Measurable (fun t : ℝ => Real.exp (-t / 2)) := by fun_prop
  have hd : Measurable (fun t : ℝ => 1 + t) := by fun_prop
  exact (Complex.continuous_ofReal.measurable.comp ((hE.mul hw).div hd)).indicator
    measurableSet_Ioi

theorem measurable_hilbertEvaluationFunction (s : ℂ) :
    Measurable (hilbertEvaluationFunction s) := by
  apply Measurable.indicator _ measurableSet_Ioi
  fun_prop

private theorem integrable_polynomial_exp (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (1 + t) ^ (2 : ℕ) * Real.exp (-b * t)) (Ioi 0) := by
  have h (n : ℕ) : IntegrableOn
      (fun t : ℝ => t ^ n * Real.exp (-b * t)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (n : ℝ)) (p := 1) (by linarith [Nat.cast_nonneg (α := ℝ) n]) le_rfl hb)
  refine IntegrableOn.congr_fun ((h 0).add (((h 1).const_mul 2).add (h 2)))
    (fun t _ => ?_) measurableSet_Ioi
  dsimp
  ring

theorem norm_hilbertEvaluationFunction_of_pos (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖hilbertEvaluationFunction s t‖ =
      (1 + t) * Real.exp (-(s.re - 1 / 2) * t) := by
  rw [hilbertEvaluationFunction, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + t), Complex.norm_exp]
  congr 2
  simp

theorem memLp_hilbertEvaluationFunction {s : ℂ} (hs : 1 / 2 < s.re) :
    MemLp (hilbertEvaluationFunction s) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_hilbertEvaluationFunction s).aestronglyMeasurable).2
  have heq : (fun t => ‖hilbertEvaluationFunction s t‖ ^ (2 : ℕ)) =
      (Ioi (0 : ℝ)).indicator
        (fun t => (1 + t) ^ (2 : ℕ) * Real.exp (-(2 * (s.re - 1 / 2)) * t)) := by
    funext t
    by_cases ht : 0 < t
    · rw [norm_hilbertEvaluationFunction_of_pos s ht, mul_pow,
        ← Real.exp_nat_mul, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      congr 2
      ring
    · simp [hilbertEvaluationFunction, ht]
  rw [heq, integrable_indicator_iff measurableSet_Ioi]
  exact integrable_polynomial_exp _ (by linarith)

theorem norm_hilbertSourceFunction_le {t : ℝ} (ht : 0 < t) :
    ‖hilbertSourceFunction t‖ ≤ 4 / (1 + t) := by
  have hE := abs_error_le (Real.one_le_exp ht.le)
  have hw : 0 < Real.exp (-t / 2) := Real.exp_pos _
  have hd : 0 < 1 + t := by linarith
  have hexp : Real.sqrt (Real.exp t) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_half, ← Real.exp_add, show t / 2 + -t / 2 = 0 by ring,
      Real.exp_zero]
  rw [hilbertSourceFunction, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hw, abs_of_pos hd]
  calc
    |error (Real.exp t)| * Real.exp (-t / 2) / (1 + t) ≤
        (4 * Real.sqrt (Real.exp t)) * Real.exp (-t / 2) / (1 + t) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hE hw.le) hd.le
    _ = 4 / (1 + t) := by rw [mul_assoc, hexp, mul_one]

/-- One arithmetic vector works for the entire strict-right half-plane. -/
theorem memLp_hilbertSourceFunction : MemLp hilbertSourceFunction 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    measurable_hilbertSourceFunction.aestronglyMeasurable).2
  have hi : IntegrableOn (fun t : ℝ => 16 / (1 + t) ^ (2 : ℕ)) (Ioi 0) := by
    have h := (integrableOn_add_rpow_Ioi_of_lt
      (a := -2) (c := 0) (m := 1) (by norm_num) (by norm_num)).const_mul 16
    refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
    rw [Real.rpow_neg (add_nonneg (show 0 ≤ t from le_of_lt ht) zero_le_one),
      Real.rpow_two]
    simp only [div_eq_mul_inv, add_comm]
  have hib := (integrable_indicator_iff measurableSet_Ioi).2 hi
  apply hib.mono'
    (measurable_hilbertSourceFunction.aestronglyMeasurable.norm.pow 2)
  filter_upwards with t
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    change |‖hilbertSourceFunction t‖ ^ (2 : ℕ)| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := norm_hilbertSourceFunction_le ht
    calc
      ‖hilbertSourceFunction t‖ ^ (2 : ℕ) ≤ (4 / (1 + t)) ^ (2 : ℕ) := by
        gcongr
      _ = 16 / (1 + t) ^ (2 : ℕ) := by rw [div_pow]; norm_num
  · simp [hilbertSourceFunction, ht]

/-- The source is fixed before a spectral point or a zero is selected. -/
def hilbertSource : LogHilbert :=
  memLp_hilbertSourceFunction.toLp hilbertSourceFunction

/-- The actual L² evaluation vector, with value zero outside its admission domain. -/
def hilbertEvaluation (s : ℂ) : LogHilbert :=
  l2Family volume hilbertEvaluationFunction s

theorem hilbertSource_ae :
    (hilbertSource : ℝ → ℂ) =ᵐ[volume] hilbertSourceFunction :=
  memLp_hilbertSourceFunction.coeFn_toLp

theorem hilbertEvaluation_ae {s : ℂ} (hs : 1 / 2 < s.re) :
    (hilbertEvaluation s : ℝ → ℂ) =ᵐ[volume] hilbertEvaluationFunction s := by
  rw [hilbertEvaluation, l2Family_eq_toLp volume hilbertEvaluationFunction s
    (memLp_hilbertEvaluationFunction hs)]
  exact (memLp_hilbertEvaluationFunction hs).coeFn_toLp

/-- The spectral derivative is the logarithmic clock acting on the evaluation kernel. -/
def hilbertEvaluationJetFunction (s : ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator fun t =>
    -(t : ℂ) * (((1 + t : ℝ) : ℂ) *
      Complex.exp (-(s - 1 / 2) * (t : ℂ)))

theorem hasDerivAt_hilbertEvaluationFunction (s : ℂ) (t : ℝ) :
    HasDerivAt (fun z => hilbertEvaluationFunction z t)
      (hilbertEvaluationJetFunction s t) s := by
  by_cases ht : 0 < t
  · simp only [hilbertEvaluationFunction, hilbertEvaluationJetFunction,
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    have harg : HasDerivAt (fun z : ℂ => -(z - 1 / 2) * (t : ℂ)) (-(t : ℂ)) s :=
      (((hasDerivAt_id s).sub_const (1 / 2)).neg.mul_const (t : ℂ)).congr_deriv (by ring)
    exact (((Complex.hasDerivAt_exp _).comp s harg).const_mul
      (((1 + t : ℝ) : ℂ))).congr_deriv (by ring)
  · simpa [hilbertEvaluationFunction, hilbertEvaluationJetFunction, ht] using
      (hasDerivAt_const s (0 : ℂ))

/-- The derivative vector is a second explicit, admitted continuum vector. -/
def hilbertEvaluationJet (s : ℂ) : LogHilbert :=
  l2Family volume hilbertEvaluationJetFunction s

private theorem hilbertEvaluation_jet_admission {s : ℂ} (hs : 1 / 2 < s.re) :
    MemLp (hilbertEvaluationJetFunction s) 2 ∧
      HasDerivAt hilbertEvaluation (hilbertEvaluationJet s) s := by
  let R : ℝ := (s.re - 1 / 2) / 2
  let a : ℂ := (((s.re + 1 / 2) / 2 : ℝ) : ℂ)
  have hR : 0 < R := by dsimp [R]; linarith
  have ha : 1 / 2 < a.re := by dsimp [a]; linarith
  have hb : MemLp (fun t => ‖hilbertEvaluationFunction a t‖) 2 :=
    (memLp_hilbertEvaluationFunction ha).norm
  have hbound : ∀ t : ℝ, ∀ z ∈ ball s R,
      ‖hilbertEvaluationFunction z t‖ ≤ ‖hilbertEvaluationFunction a t‖ := by
    intro t z hz
    by_cases ht : 0 < t
    · rw [norm_hilbertEvaluationFunction_of_pos z ht,
        norm_hilbertEvaluationFunction_of_pos a ht]
      have hzs : (s - z).re < R :=
        lt_of_le_of_lt (Complex.re_le_norm _) (by
          simpa only [norm_sub_rev] using (mem_ball_iff_norm.mp hz))
      have haz : a.re ≤ z.re := by
        dsimp [a, R] at *
        linarith
      gcongr
    · simp [hilbertEvaluationFunction, ht]
  have hd : ∀ t : ℝ, DifferentiableOn ℂ
      (fun z => hilbertEvaluationFunction z t) (ball s R) :=
    fun t z _ => (hasDerivAt_hilbertEvaluationFunction z t).differentiableAt.differentiableWithinAt
  obtain ⟨hm, h⟩ := exists_memLp_deriv_hasDerivAt_l2Family_of_cauchy_dominated
    volume hilbertEvaluationFunction
    s R hR (fun t => ‖hilbertEvaluationFunction a t‖) hb
    (fun z _ => (measurable_hilbertEvaluationFunction z).aestronglyMeasurable) hd hbound
  have heq : (fun t => deriv (fun w => hilbertEvaluationFunction w t) s) =
      hilbertEvaluationJetFunction s := by
    funext t
    exact (hasDerivAt_hilbertEvaluationFunction s t).deriv
  rw [heq] at hm h
  refine ⟨hm, ?_⟩
  change HasDerivAt (l2Family volume hilbertEvaluationFunction)
    (l2Family volume hilbertEvaluationJetFunction s) s
  rw [l2Family_eq_toLp volume hilbertEvaluationJetFunction s hm]
  exact h

/-- Strong holomorphy holds in the fixed Hilbert space, not only after scalar observation. -/
theorem hasDerivAt_hilbertEvaluation {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt hilbertEvaluation (hilbertEvaluationJet s) s :=
  (hilbertEvaluation_jet_admission hs).2

theorem hilbertEvaluationJet_ae {s : ℂ} (hs : 1 / 2 < s.re) :
    (hilbertEvaluationJet s : ℝ → ℂ) =ᵐ[volume] hilbertEvaluationJetFunction s := by
  rw [hilbertEvaluationJet, l2Family_eq_toLp volume hilbertEvaluationJetFunction s
    (hilbertEvaluation_jet_admission hs).1]
  exact (hilbertEvaluation_jet_admission hs).1.coeFn_toLp

theorem analyticOnNhd_hilbertEvaluation :
    AnalyticOnNhd ℂ hilbertEvaluation {s : ℂ | 1 / 2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  exact fun _ hs => (hasDerivAt_hilbertEvaluation hs).differentiableAt.differentiableWithinAt

private theorem exp_cpow (s : ℂ) (t : ℝ) :
    ((Real.exp t : ℝ) : ℂ) ^ (-(s + 1)) =
      Complex.exp (-(s + 1) * (t : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.exp_ne_zero t),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  congr 1
  ring

/-- The Mellin moment in logarithmic coordinates, with its exact lower endpoint. -/
theorem moment_eq_log_integral (s : ℂ) :
    moment s = ∫ t in Ioi (0 : ℝ),
      (error (Real.exp t) : ℂ) * Complex.exp (-s * (t : ℂ)) := by
  rw [moment_eq_integral]
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (0 : ℝ)) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun x : ℝ => (error x : ℂ) * (x : ℂ) ^ (-(s + 1)))
  rw [Real.image_exp_Ioi, Real.exp_zero] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [abs_of_pos (Real.exp_pos t), Complex.real_smul, exp_cpow,
    Complex.ofReal_exp]
  calc
    Complex.exp (t : ℂ) *
        ((error (Real.exp t) : ℂ) * Complex.exp (-(s + 1) * (t : ℂ))) =
      (error (Real.exp t) : ℂ) *
        Complex.exp ((t : ℂ) + (-(s + 1) * (t : ℂ))) := by
          rw [Complex.exp_add]
          ring
    _ = _ := by congr 2; ring

/-- Exact Hilbert factorization of the actual arithmetic discrepancy moment. -/
theorem inner_hilbertSource_evaluation {s : ℂ} (hs : 1 / 2 < s.re) :
    inner ℂ hilbertSource (hilbertEvaluation s) = moment s := by
  rw [L2.inner_def, moment_eq_log_integral, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [hilbertSource_ae, hilbertEvaluation_ae hs] with t hsource heval
  rw [hsource, heval, RCLike.inner_apply]
  by_cases ht : 0 < t
  · rw [hilbertEvaluationFunction, hilbertSourceFunction,
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    simp only [Complex.conj_ofReal]
    have hd : (1 + (t : ℂ)) ≠ 0 := by
      exact_mod_cast (show 1 + t ≠ 0 by linarith)
    have hexp : Complex.exp (-(s - 1 / 2) * (t : ℂ)) *
        Complex.exp (-(t : ℂ) / 2) = Complex.exp (-s * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    push_cast
    calc
      _ = (error (Real.exp t) : ℂ) *
          (Complex.exp (-(s - 1 / 2) * (t : ℂ)) *
            Complex.exp (-(t : ℂ) / 2)) := by field_simp [hd]
      _ = _ := by rw [hexp]
  · simp [hilbertEvaluationFunction, hilbertSourceFunction, ht]

/-- Undoing the Hilbert weight recovers the actual arithmetic staircase. -/
theorem hilbertSourceFunction_recovers_count {t : ℝ} (ht : 0 < t) :
    (((1 + t) * Real.exp (t / 2) : ℝ) : ℂ) * hilbertSourceFunction t +
        (Sieve.squarefreeDensity : ℂ) * (Real.exp t : ℂ) =
      (count (Real.exp t) : ℂ) := by
  rw [hilbertSourceFunction, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
  have hden : 1 + t ≠ 0 := by linarith
  have hexp : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]
  have h : ((1 + t) * Real.exp (t / 2)) *
        (error (Real.exp t) * Real.exp (-t / 2) / (1 + t)) +
        Sieve.squarefreeDensity * Real.exp t = count (Real.exp t) := by
    calc
      _ = error (Real.exp t) * (Real.exp (t / 2) * Real.exp (-t / 2)) +
          Sieve.squarefreeDensity * Real.exp t := by field_simp [hden]
      _ = _ := by rw [hexp]; simp [error]
  exact_mod_cast h

/-- An interval readout of the actual L² class; null-set representative choices do not enter. -/
def hilbertCountReadout (f : LogHilbert) (density : ℂ) (n : ℕ) : ℂ :=
  (((Real.log (n + 2 : ℝ) - Real.log (n + 1 : ℝ) : ℝ) : ℂ))⁻¹ *
    ∫ t in Ioo (Real.log (n + 1 : ℝ)) (Real.log (n + 2 : ℝ)),
      (((1 + t) * Real.exp (t / 2) : ℝ) : ℂ) * (f : ℝ → ℂ) t +
        density * (Real.exp t : ℂ)

private theorem count_exp_on_log_interval (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (Real.log (n + 1 : ℝ)) (Real.log (n + 2 : ℝ))) :
    count (Real.exp t) = count ((n + 1 : ℕ) : ℝ) := by
  have h1 : 0 < (n : ℝ) + 1 := by positivity
  have h2 : 0 < (n : ℝ) + 2 := by positivity
  have hlo : (n : ℝ) + 1 < Real.exp t := by
    simpa only [Real.exp_log h1] using Real.exp_lt_exp.mpr ht.1
  have hhi : Real.exp t < (n : ℝ) + 2 := by
    simpa only [Real.exp_log h2] using Real.exp_lt_exp.mpr ht.2
  have hf : ⌊Real.exp t⌋₊ = n + 1 :=
    (Nat.floor_eq_iff (Real.exp_pos t).le).2 ⟨by exact_mod_cast hlo.le, by
      push_cast
      linarith⟩
  simp only [count, hf, Nat.floor_natCast]

/-- Every summatory coefficient is recovered from the fixed arithmetic Hilbert source. -/
theorem hilbertCountReadout_source (n : ℕ) :
    hilbertCountReadout hilbertSource (Sieve.squarefreeDensity : ℂ) n =
      (count ((n + 1 : ℕ) : ℝ) : ℂ) := by
  have hab : Real.log (n + 1 : ℝ) < Real.log (n + 2 : ℝ) :=
    Real.log_lt_log (by positivity) (by linarith)
  have hI : (∫ t in Ioo (Real.log (n + 1 : ℝ)) (Real.log (n + 2 : ℝ)),
      (((1 + t) * Real.exp (t / 2) : ℝ) : ℂ) * (hilbertSource : ℝ → ℂ) t +
        (Sieve.squarefreeDensity : ℂ) * (Real.exp t : ℂ)) =
      ∫ _t in Ioo (Real.log (n + 1 : ℝ)) (Real.log (n + 2 : ℝ)),
        (count ((n + 1 : ℕ) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [hilbertSource_ae.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioo] with t hsource ht
    have ht0 : 0 < t :=
      (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])).trans_lt ht.1
    rw [hsource, hilbertSourceFunction_recovers_count ht0,
      count_exp_on_log_interval n ht]
  rw [hilbertCountReadout, hI, setIntegral_const]
  have hd : (((Real.log (n + 2 : ℝ) - Real.log (n + 1 : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hab.ne'
  simp only [Real.volume_real_Ioo, sub_nonneg.mpr hab.le, max_eq_left,
    Complex.real_smul]
  exact inv_mul_cancel_left₀ hd _

/-- Consecutive recovered counts retain every arithmetic coefficient after the first. -/
theorem hilbertCountReadout_source_difference (n : ℕ) :
    hilbertCountReadout hilbertSource (Sieve.squarefreeDensity : ℂ) (n + 1) -
        hilbertCountReadout hilbertSource (Sieve.squarefreeDensity : ℂ) n =
      ((((ArithmeticFunction.moebius (n + 2) : ℤ) : ℝ) ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [hilbertCountReadout_source, hilbertCountReadout_source]
  norm_cast
  simp only [count, Nat.floor_natCast]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ (n + 1) + 1)]
  simp [Nat.add_assoc]

/-- A reciprocal continuum clock factor admits the source and its first clock moment. -/
def clockSourceFunction (t : ℝ) : ℂ :=
  hilbertSourceFunction t / ((1 + |t| : ℝ) : ℂ)

theorem memLp_clockSourceFunction : MemLp clockSourceFunction 2 := by
  apply memLp_hilbertSourceFunction.of_le
    (measurable_hilbertSourceFunction.div (by fun_prop)).aestronglyMeasurable
  filter_upwards with t
  rw [clockSourceFunction, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 + |t|)]
  apply (div_le_iff₀ (by positivity : 0 < 1 + |t|)).2
  nlinarith [mul_nonneg (norm_nonneg (hilbertSourceFunction t)) (abs_nonneg t)]

/-- Fixed arithmetic source in the domain of the logarithmic multiplication clock. -/
def clockSource : LogHilbert :=
  memLp_clockSourceFunction.toLp clockSourceFunction

/-- Its genuine clock tangent, admitted without an arithmetic cancellation hypothesis. -/
def clockSourceJet : LogHilbert := clockSource - hilbertSource

/-- The opposite clock factor acts on the holomorphic evaluation family. -/
def clockEvaluation (s : ℂ) : LogHilbert :=
  hilbertEvaluation s - hilbertEvaluationJet s

theorem clockSource_ae :
    (clockSource : ℝ → ℂ) =ᵐ[volume] clockSourceFunction :=
  memLp_clockSourceFunction.coeFn_toLp

/-- The admitted tangent is exactly multiplication of the actual source by `-t`. -/
theorem clockSourceJet_ae :
    (clockSourceJet : ℝ → ℂ) =ᵐ[volume]
      fun t => -(t : ℂ) * (clockSource : ℝ → ℂ) t := by
  filter_upwards [Lp.coeFn_sub clockSource hilbertSource, clockSource_ae,
    hilbertSource_ae] with t hsub hclock hsource
  change (clockSource - hilbertSource : LogHilbert) t = _
  rw [hsub, Pi.sub_apply, hclock, hsource, clockSourceFunction]
  by_cases ht : 0 < t
  · rw [abs_of_pos ht]
    have hd : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + t ≠ 0 by linarith)
    push_cast
    field_simp [hd]
    ring
  · simp [hilbertSourceFunction, ht]

/-- The two admitted source columns reconstruct the complete original arithmetic source. -/
theorem clockSource_sub_clockSourceJet : clockSource - clockSourceJet = hilbertSource := by
  simp [clockSourceJet]

theorem analyticOnNhd_hilbertEvaluationJet :
    AnalyticOnNhd ℂ hilbertEvaluationJet {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  apply (analyticOnNhd_hilbertEvaluation.deriv s hs).congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  exact (hasDerivAt_hilbertEvaluation hz).deriv

theorem analyticOnNhd_clockEvaluation :
    AnalyticOnNhd ℂ clockEvaluation {s : ℂ | 1 / 2 < s.re} :=
  analyticOnNhd_hilbertEvaluation.sub analyticOnNhd_hilbertEvaluationJet

/-- Reciprocal source/evaluation clock factors preserve the full arithmetic moment. -/
theorem inner_clockSource_evaluation {s : ℂ} (hs : 1 / 2 < s.re) :
    inner ℂ clockSource (clockEvaluation s) = moment s := by
  rw [← inner_hilbertSource_evaluation hs, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [clockSource_ae, hilbertSource_ae, hilbertEvaluation_ae hs,
    hilbertEvaluationJet_ae hs,
    Lp.coeFn_sub (hilbertEvaluation s) (hilbertEvaluationJet s)] with t hc hh he hj hsub
  change inner ℂ ((clockSource : ℝ → ℂ) t)
    ((hilbertEvaluation s - hilbertEvaluationJet s : LogHilbert) t) = _
  rw [hsub, Pi.sub_apply, hc, hh, he, hj]
  by_cases ht : 0 < t
  · simp only [clockSourceFunction, hilbertSourceFunction, hilbertEvaluationFunction,
      hilbertEvaluationJetFunction,
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), RCLike.inner_apply,
      abs_of_pos ht, map_div₀, Complex.conj_ofReal]
    have hd : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + t ≠ 0 by linarith)
    push_cast
    field_simp [hd]
    ring
  · simp [clockSourceFunction, hilbertSourceFunction, hilbertEvaluationFunction,
      hilbertEvaluationJetFunction, ht]

theorem inner_hilbertSource_evaluationJet {s : ℂ} (hs : 1 / 2 < s.re) :
    inner ℂ hilbertSource (hilbertEvaluationJet s) = deriv moment s := by
  have h := (innerSL ℂ hilbertSource).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_hilbertEvaluation hs)
  apply Eq.symm
  apply HasDerivAt.deriv
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  exact (inner_hilbertSource_evaluation hz).symm

/-- The same evaluation vector observes the value and its genuine arithmetic clock tangent. -/
theorem inner_clockSourceJet_evaluation {s : ℂ} (hs : 1 / 2 < s.re) :
    inner ℂ clockSourceJet (clockEvaluation s) = deriv moment s := by
  rw [clockSourceJet, inner_sub_left, inner_clockSource_evaluation hs,
    clockEvaluation, inner_sub_right, inner_hilbertSource_evaluation hs,
    inner_hilbertSource_evaluationJet hs]
  ring

/-- A fixed source and its admitted clock tangent give the arithmetic moment and its derivative
on the whole strict-right half-plane, and retain the original arithmetic source exactly. -/
theorem fixedArithmeticClockPair :
    clockSource - clockSourceJet = hilbertSource ∧
      ((clockSourceJet : ℝ → ℂ) =ᵐ[volume]
        fun t => -(t : ℂ) * (clockSource : ℝ → ℂ) t) ∧
      AnalyticOnNhd ℂ clockEvaluation {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : {s : ℂ // 1 / 2 < s.re},
        inner ℂ clockSource (clockEvaluation s) = moment s ∧
        inner ℂ clockSourceJet (clockEvaluation s) = deriv moment s :=
  ⟨clockSource_sub_clockSourceJet, clockSourceJet_ae, analyticOnNhd_clockEvaluation,
    fun s => ⟨inner_clockSource_evaluation s.property,
      inner_clockSourceJet_evaluation s.property⟩⟩

end RHTower.SquarefreeDiscrepancy
