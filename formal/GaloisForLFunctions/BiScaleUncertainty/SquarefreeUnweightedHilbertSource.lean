import GaloisForLFunctions.BiScaleUncertainty.SquarefreeCriticalLogEnvelope
import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyHilbertTransport
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The unweighted squarefree source belongs to the physical Hilbert space

The full signed squarefree discrepancy now admits the critical L² carrier
without the auxiliary factor `(1+t)⁻¹`. This removes a source admission
obstacle. It does not assert the remaining inverse-overlap Sonin comparison.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower.SquarefreeDiscrepancy

/-- The actual critical discrepancy source, with no logarithmic weight. -/
def unweightedSourceFunction : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator fun t =>
    ((error (Real.exp t) * Real.exp (-t / 2) : ℝ) : ℂ)

private theorem critical_source_bound {t : ℝ} (ht : 0 ≤ t) :
    |error (Real.exp t)| * Real.exp (-t / 2) ≤ 4 := by
  have hx : 1 ≤ Real.exp t := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ht
  have h := mul_le_mul_of_nonneg_right (abs_error_le hx) (Real.exp_pos (-t / 2)).le
  have he : Real.sqrt (Real.exp t) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_half, ← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  nlinarith

/-- A global integrable-square envelope, produced from the unconditional
arithmetic saving and the elementary compact-range bound. -/
theorem exists_unweightedSourceFunction_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖unweightedSourceFunction t‖ ≤ C / (1 + |t|) := by
  obtain ⟨A, hA, hevent⟩ := eventually_abs_error_exp_critical_le
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  let S := max T 1
  let C := 4 * (1 + S) + 2 * A
  have hS : 1 ≤ S := le_max_right _ _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun t => ?_⟩
  by_cases ht : 0 < t
  · have he : ‖unweightedSourceFunction t‖ =
        |error (Real.exp t)| * Real.exp (-t / 2) := by
      rw [unweightedSourceFunction, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
        Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (-t / 2))]
    rw [he, abs_of_pos ht]
    by_cases hlarge : S ≤ t
    · have ht1 : 1 ≤ t := hS.trans hlarge
      have htail := hT t ((le_max_left T 1).trans hlarge)
      have hden : A / t ≤ 2 * A / (1 + t) := by
        rw [div_le_div_iff₀ ht (by positivity)]
        nlinarith
      apply htail.trans (hden.trans _)
      apply div_le_div_of_nonneg_right _ (by positivity)
      dsimp [C]
      linarith
    · have hsmall := critical_source_bound ht.le
      have hct : 4 * (1 + t) ≤ C := by
        dsimp [C]
        linarith [lt_of_not_ge hlarge]
      exact hsmall.trans ((le_div_iff₀ (by positivity)).mpr hct)
  · rw [unweightedSourceFunction,
      indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht), norm_zero]
    positivity

/-- The literal unweighted squarefree discrepancy is square integrable at the
critical exponent. No RH or conditional cancellation premise occurs. -/
theorem memLp_unweightedSourceFunction : MemLp unweightedSourceFunction 2
    (volume : Measure ℝ) := by
  have hmeas : Measurable unweightedSourceFunction :=
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_error.comp Real.measurable_exp).mul
        (Real.measurable_exp.comp (measurable_id.neg.div_const 2)))).indicator
      measurableSet_Ioi
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
  obtain ⟨C, hC, hbound⟩ := exists_unweightedSourceFunction_envelope
  apply (integrable_inv_one_add_sq.const_mul (C^2)).mono'
    (hmeas.norm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hden : 0 < 1 + |t| := by positivity
  calc
    ‖unweightedSourceFunction t‖^2 ≤ (C / (1 + |t|))^2 := by
      nlinarith [hbound t, norm_nonneg (unweightedSourceFunction t),
        div_nonneg hC.le hden.le]
    _ = C^2 / (1 + |t|)^2 := div_pow _ _ _
    _ ≤ C^2 / (1 + t^2) := by
      apply div_le_div_of_nonneg_left (sq_nonneg C) (by positivity)
      nlinarith [abs_nonneg t, sq_abs t]
    _ = _ := by ring

/-- The physical critical Hilbert source, admitted from the arithmetic estimate. -/
def unweightedSource : LogHilbert :=
  memLp_unweightedSourceFunction.toLp unweightedSourceFunction

private theorem norm_unweightedSourceFunction_sq {t : ℝ} (ht : 0 < t) :
    ‖unweightedSourceFunction t‖^2 =
      error (Real.exp t)^2 / Real.exp t := by
  simp only [unweightedSourceFunction, Set.mem_Ioi, ht, indicator_of_mem,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  have he : Real.exp (-t / 2)^2 = (Real.exp t)⁻¹ := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  rw [he, div_eq_mul_inv]

/-- The actual full discrepancy has finite critical energy on `(1,∞)`. -/
theorem integrableOn_discrepancy_critical_energy :
    IntegrableOn (fun x : ℝ => error x^2 / x^2) (Ioi 1) := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (0 : ℝ)) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn (fun x : ℝ => error x^2 / x^2)
  rw [Real.image_exp_Ioi, Real.exp_zero] at hchange
  apply hchange.mpr
  have hint := ((memLp_two_iff_integrable_sq_norm
    memLp_unweightedSourceFunction.aestronglyMeasurable).mp
      memLp_unweightedSourceFunction).integrableOn (s := Ioi (0 : ℝ))
  apply hint.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [norm_unweightedSourceFunction_sq ht]
  rw [abs_of_pos (Real.exp_pos t), smul_eq_mul]
  field_simp <;> ring

/-- Exact critical energy identity under the physical logarithmic coordinate. -/
theorem integral_discrepancy_critical_energy_eq :
    (∫ x in Ioi (1 : ℝ), error x^2 / x^2) =
      ∫ t : ℝ, ‖unweightedSourceFunction t‖^2 := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (0 : ℝ)) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn (fun x : ℝ => error x^2 / x^2)
  rw [Real.image_exp_Ioi, Real.exp_zero] at hchange
  rw [hchange]
  have hlocal : (∫ t in Ioi (0 : ℝ), |Real.exp t| •
      (error (Real.exp t)^2 / Real.exp t^2)) =
      ∫ t in Ioi (0 : ℝ), ‖unweightedSourceFunction t‖^2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [norm_unweightedSourceFunction_sq ht, abs_of_pos (Real.exp_pos t), smul_eq_mul]
    field_simp <;> ring
  rw [hlocal]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp [ht]
  · simp [unweightedSourceFunction, ht]

/-- Applying the prior auxiliary factor to the admitted physical source
recovers exactly the prior fixed Hilbert source, pointwise. -/
theorem unweightedSourceFunction_div_eq (t : ℝ) :
    unweightedSourceFunction t / ((1 + t : ℝ) : ℂ) = hilbertSourceFunction t := by
  by_cases ht : 0 < t
  · simp [unweightedSourceFunction, hilbertSourceFunction, ht, Complex.ofReal_div]
  · simp [unweightedSourceFunction, hilbertSourceFunction, ht]

/-- The natural critical Mellin evaluation column, with no compensating
logarithmic-coordinate factor. -/
def unweightedEvaluationFunction (s : ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator fun t => Complex.exp (-(s - 1 / 2) * (t : ℂ))

theorem memLp_unweightedEvaluationFunction {s : ℂ} (hs : 1 / 2 < s.re) :
    MemLp (unweightedEvaluationFunction s) 2 (volume : Measure ℝ) := by
  have hmeas : Measurable (unweightedEvaluationFunction s) := by
    apply Measurable.indicator _ measurableSet_Ioi
    fun_prop
  apply (memLp_hilbertEvaluationFunction hs).of_le hmeas.aestronglyMeasurable
  filter_upwards [] with t
  by_cases ht : 0 < t
  · simp only [unweightedEvaluationFunction, hilbertEvaluationFunction, Set.mem_Ioi,
      ht, indicator_of_mem, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < 1 + t by linarith)]
    nlinarith [mul_nonneg ht.le (norm_nonneg (Complex.exp (-(s - 1 / 2) * (t : ℂ))))]
  · simp [unweightedEvaluationFunction, hilbertEvaluationFunction, ht]

/-- The natural evaluation vector on the strict-right critical half-plane. -/
def unweightedEvaluation (s : ℂ) (hs : 1 / 2 < s.re) : LogHilbert :=
  (memLp_unweightedEvaluationFunction hs).toLp (unweightedEvaluationFunction s)

/-- The admitted unweighted source reads the same full arithmetic moment.
Both members of the pairing now have their natural critical Mellin weights. -/
theorem inner_unweightedSource_evaluation {s : ℂ} (hs : 1 / 2 < s.re) :
    inner ℂ unweightedSource (unweightedEvaluation s hs) = moment s := by
  rw [L2.inner_def, moment_eq_log_integral, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [memLp_unweightedSourceFunction.coeFn_toLp,
    (memLp_unweightedEvaluationFunction hs).coeFn_toLp] with t hsource heval
  change unweightedSource t = unweightedSourceFunction t at hsource
  change unweightedEvaluation s hs t = unweightedEvaluationFunction s t at heval
  rw [hsource, heval, RCLike.inner_apply]
  by_cases ht : 0 < t
  · rw [unweightedSourceFunction, unweightedEvaluationFunction,
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    simp only [Complex.conj_ofReal]
    have hexp : Complex.exp (-(s - 1 / 2) * (t : ℂ)) *
        Complex.exp (-(t : ℂ) / 2) = Complex.exp (-s * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    push_cast
    calc
      _ = (error (Real.exp t) : ℂ) *
          (Complex.exp (-(s - 1 / 2) * (t : ℂ)) *
            Complex.exp (-(t : ℂ) / 2)) := by ring
      _ = _ := by rw [hexp]
  · simp [unweightedSourceFunction, unweightedEvaluationFunction, ht]

end RHTower.SquarefreeDiscrepancy
