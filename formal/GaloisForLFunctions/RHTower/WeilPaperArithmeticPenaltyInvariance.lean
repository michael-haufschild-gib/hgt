import GaloisForLFunctions.RHTower.WeilPaperObservedPenaltyQuotient

/-!
# Integer origin phases are invisible to gamma-energy minimization

Pull integer prime-torus phases back to bounded continuous real-frequency
observables. Their expectations vanish on every actual observed completion.
Every finite complex combination therefore gives a real trigonometric penalty
that leaves objectives, minima, and optimizers unchanged. Subtracting these
invisible directions sharpens both value stability and optimizer transfer.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Actual integer prime-torus phase as a bounded continuous real-frequency observable. -/
def paperOriginPhaseObservable (n : LogIndex) : ℝ →ᵇ ℂ :=
  (BoundedContinuousFunction.mkOfCompact (arithmeticPhase n.1)).compContinuous
    ⟨primeSpectralPoint, continuous_primeSpectralPoint⟩

@[simp] theorem paperOriginPhaseObservable_apply (n : LogIndex) (ξ : ℝ) :
    paperOriginPhaseObservable n ξ = arithmeticPhase n.1 (primeSpectralPoint ξ) := rfl

/-- The origin observable is the actual integer logarithmic Fourier phase. -/
theorem paperOriginPhaseObservable_eq_exp (n : LogIndex) (ξ : ℝ) :
    paperOriginPhaseObservable n ξ =
      Complex.exp (2 * Real.pi * Complex.I * ξ * Real.log n.1) :=
  arithmeticPhase_primeSpectralPoint (by have := n.2; omega) ξ

/-- The real spectral expectation is exactly the pushed-forward torus moment. -/
theorem integral_paperOriginPhaseObservable (μ : ProbabilityMeasure ℝ) (n : LogIndex) :
    (∫ ξ, paperOriginPhaseObservable n ξ ∂(μ : Measure ℝ)) =
      ∫ z, arithmeticPhase n.1 z ∂(paperPrimeSpectralPushforward μ : Measure PrimePhaseSpace) := by
  unfold paperPrimeSpectralPushforward
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map continuous_primeSpectralPoint.measurable.aemeasurable
      (arithmeticPhase n.1).continuous.aestronglyMeasurable]
  rfl

/-- Every origin phase has zero expectation throughout every observed completion. -/
theorem integral_paperOriginPhaseObservable_observed_zero
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (n : LogIndex) :
    (∫ ξ, paperOriginPhaseObservable n ξ ∂(μ.1 : Measure ℝ)) = 0 := by
  rw [integral_paperOriginPhaseObservable]
  exact paperObservedSpectralCompletion_represents_origin c F μ n.1 n.2

/-- An arbitrary finite real trigonometric penalty from integer logarithmic phases. -/
def paperArithmeticSpectralPenalty (s : Finset LogIndex) (a : LogIndex → ℂ) : ℝ →ᵇ ℝ :=
  paperFiniteSpectralPenalty paperOriginPhaseObservable s a

theorem paperArithmeticSpectralPenalty_apply (s : Finset LogIndex) (a : LogIndex → ℂ) (ξ : ℝ) :
    paperArithmeticSpectralPenalty s a ξ =
      (∑ n ∈ s, a n * Complex.exp (2 * Real.pi * Complex.I * ξ * Real.log n.1)).re := by
  rw [paperArithmeticSpectralPenalty, paperFiniteSpectralPenalty_apply]
  simp only [paperOriginPhaseObservable_eq_exp]

/-- Integer arithmetic penalties have exactly zero expectation, without any additional observation. -/
theorem integral_paperArithmeticSpectralPenalty_zero
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (s : Finset LogIndex) (a : LogIndex → ℂ) :
    (∫ ξ, paperArithmeticSpectralPenalty s a ξ ∂(μ.1 : Measure ℝ)) = 0 := by
  rw [paperArithmeticSpectralPenalty, integral_paperFiniteSpectralPenalty]
  have hs : (∑ n ∈ s, a n * ∫ ξ, paperOriginPhaseObservable n ξ ∂(μ.1 : Measure ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    rw [integral_paperOriginPhaseObservable_observed_zero c F μ n, mul_zero]
  rw [hs]
  rfl

/-- Every feasible objective is unchanged by adding an integer arithmetic penalty. -/
theorem paperPerturbedGammaExpectation_add_arithmeticPenalty
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (G : ℝ →ᵇ ℝ)
    (s : Finset LogIndex) (a : LogIndex → ℂ) :
    paperPerturbedGammaExpectation (G + paperArithmeticSpectralPenalty s a) μ.1 =
      paperPerturbedGammaExpectation G μ.1 := by
  rw [paperPerturbedGammaExpectation_add, integral_paperArithmeticSpectralPenalty_zero c F μ,
    add_zero]

/-- The attained gamma value is exactly invariant under all finite integer arithmetic penalties. -/
theorem paperObservedGammaValue_add_arithmeticPenalty
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (G : ℝ →ᵇ ℝ) (s : Finset LogIndex) (a : LogIndex → ℂ) :
    paperObservedGammaValue c F (G + paperArithmeticSpectralPenalty s a) =
      paperObservedGammaValue c F G := by
  apply le_antisymm
  · calc
      _ ≤ paperPerturbedGammaExpectation (G + paperArithmeticSpectralPenalty s a)
          (paperObservedGammaMinimizer c F G).1 := paperObservedGammaValue_le c F _ _
      _ = _ := paperPerturbedGammaExpectation_add_arithmeticPenalty c F _ G s a
  · have h := paperObservedGammaValue_le c F G
      (paperObservedGammaMinimizer c F (G + paperArithmeticSpectralPenalty s a))
    have he : paperObservedGammaValue c F (G + paperArithmeticSpectralPenalty s a) =
        paperPerturbedGammaExpectation G
          (paperObservedGammaMinimizer c F (G + paperArithmeticSpectralPenalty s a)).1 :=
      paperPerturbedGammaExpectation_add_arithmeticPenalty c F _ G s a
    exact h.trans_eq he.symm

/-- Integer arithmetic penalties preserve every pairwise feasible objective comparison. -/
theorem paperArithmeticGammaPenalty_order_iff
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ ν : PaperObservedSpectralCompletion c F) (G : ℝ →ᵇ ℝ)
    (s : Finset LogIndex) (a : LogIndex → ℂ) :
    paperPerturbedGammaExpectation (G + paperArithmeticSpectralPenalty s a) μ.1 ≤
        paperPerturbedGammaExpectation (G + paperArithmeticSpectralPenalty s a) ν.1 ↔
      paperPerturbedGammaExpectation G μ.1 ≤ paperPerturbedGammaExpectation G ν.1 := by
  rw [paperPerturbedGammaExpectation_add_arithmeticPenalty c F μ,
    paperPerturbedGammaExpectation_add_arithmeticPenalty c F ν]

/-- Each optimizer remains optimal after adding any finite integer arithmetic penalty. -/
theorem paperObservedGammaMinimizer_add_arithmeticPenalty
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset LogIndex) (a : LogIndex → ℂ) (μ : PaperObservedSpectralCompletion c F) :
    paperPerturbedGammaExpectation (G + paperArithmeticSpectralPenalty s a)
        (paperObservedGammaMinimizer c F G).1 ≤
      paperPerturbedGammaExpectation (G + paperArithmeticSpectralPenalty s a) μ.1 :=
  (paperArithmeticGammaPenalty_order_iff c F _ μ G s a).mpr (paperObservedGammaValue_le c F G μ)

/-- The value bound ignores every finite integer arithmetic phase direction. -/
theorem paperObservedGammaValue_arithmetic_quotient_bound
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ)
    (s : Finset LogIndex) (a : LogIndex → ℂ) :
    |paperObservedGammaValue c F G - paperObservedGammaValue c F H| ≤
      ‖G - H - paperArithmeticSpectralPenalty s a‖ := by
  have h := abs_paperObservedGammaValue_sub_le c F G (H + paperArithmeticSpectralPenalty s a)
  rw [paperObservedGammaValue_add_arithmeticPenalty] at h
  exact h.trans_eq (congrArg norm (by abel))

/-- Optimizer transfer depends only on the penalty difference modulo integer arithmetic directions. -/
theorem paperObservedGammaMinimizer_arithmetic_transfer_bound
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ)
    (s : Finset LogIndex) (a : LogIndex → ℂ) :
    0 ≤ paperPerturbedGammaExpectation G (paperObservedGammaMinimizer c F H).1 -
        paperObservedGammaValue c F G ∧
      paperPerturbedGammaExpectation G (paperObservedGammaMinimizer c F H).1 -
        paperObservedGammaValue c F G ≤ 2 * ‖G - H - paperArithmeticSpectralPenalty s a‖ := by
  let μ := paperObservedGammaMinimizer c F H
  let P := paperArithmeticSpectralPenalty s a
  have hm := paperObservedGammaValue_le c F G μ
  have hd := paperPerturbedGammaExpectation_sub μ.1 G (H + P)
  have hz : paperPerturbedGammaExpectation (H + P) μ.1 = paperObservedGammaValue c F H :=
    paperPerturbedGammaExpectation_add_arithmeticPenalty c F μ H s a
  have hi : (∫ ξ, (G - (H + P)) ξ ∂(μ.1 : Measure ℝ)) ≤ ‖G - H - P‖ := by
    calc
      _ ≤ |∫ ξ, (G - (H + P)) ξ ∂(μ.1 : Measure ℝ)| := le_abs_self _
      _ ≤ ‖G - (H + P)‖ := by
        simpa only [Real.norm_eq_abs] using (G - (H + P)).norm_integral_le_norm (μ.1 : Measure ℝ)
      _ = _ := congrArg norm (by abel)
  have hv := abs_le.mp (paperObservedGammaValue_arithmetic_quotient_bound c F G H s a)
  constructor <;> linarith [hv.1]

end RHTower.WeilWorkPBAP
