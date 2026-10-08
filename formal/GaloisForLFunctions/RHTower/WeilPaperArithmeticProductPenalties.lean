import GaloisForLFunctions.RHTower.WeilPaperArithmeticSquarePenalties
import Mathlib.Topology.ContinuousMap.Bounded.Star

/-!
# Mixed arithmetic penalties retain rational correlations

The product of two real integer-phase penalties splits into an integer
sum-frequency term and a rational difference-frequency term. The first is
invisible throughout every observed completion. The second exactly records
a rational phase moment and survives in the arithmetic normed quotient.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Multiplication of admissible integer frequency labels. -/
def paperProductLogIndex (n m : LogIndex) : LogIndex :=
  ⟨n.1 * m.1, by have := n.2; have := m.2; nlinarith⟩

theorem paperOriginPhaseObservable_product (n m : LogIndex) (ξ : ℝ) :
    paperOriginPhaseObservable (paperProductLogIndex n m) ξ =
      paperOriginPhaseObservable n ξ * paperOriginPhaseObservable m ξ := by
  apply arithmeticPhase_mul <;> have hn := n.2 <;> have hm := m.2 <;> omega

/-- A rational difference-frequency observable on the real spectral line. -/
def paperRationalPhaseObservable (n m : LogIndex) : ℝ →ᵇ ℂ :=
  paperOriginPhaseObservable n * star (paperOriginPhaseObservable m)

@[simp] theorem paperRationalPhaseObservable_apply (n m : LogIndex) (ξ : ℝ) :
    paperRationalPhaseObservable n m ξ =
      paperOriginPhaseObservable n ξ * (starRingEnd ℂ) (paperOriginPhaseObservable m ξ) := rfl

/-- A real projection of the rational difference-frequency observable. -/
def paperRationalPhasePenalty (n m : LogIndex) (a : ℂ) : ℝ →ᵇ ℝ :=
  Complex.reCLM.compLeftContinuousBounded ℝ (a • paperRationalPhaseObservable n m)

@[simp] theorem paperRationalPhasePenalty_apply (n m : LogIndex) (a : ℂ) (ξ : ℝ) :
    paperRationalPhasePenalty n m a ξ = (a * paperRationalPhaseObservable n m ξ).re := rfl

/-- The rational observable integrates to the actual prime-torus phase moment. -/
theorem integral_paperRationalPhaseObservable (μ : ProbabilityMeasure ℝ) (n m : LogIndex) :
    (∫ ξ, paperRationalPhaseObservable n m ξ ∂(μ : Measure ℝ)) =
      phaseMoment (paperPrimeSpectralPushforward μ) n.1 m.1 := by
  have hc : Continuous (fun z : PrimePhaseSpace =>
      arithmeticPhase n.1 z * (starRingEnd ℂ) (arithmeticPhase m.1 z)) :=
    (arithmeticPhase n.1).continuous.mul (arithmeticPhase m.1).continuous.star
  unfold phaseMoment paperPrimeSpectralPushforward
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map continuous_primeSpectralPoint.measurable.aemeasurable hc.aestronglyMeasurable]
  rfl

/-- Rational penalty expectations are exactly real projections of rational phase moments. -/
theorem integral_paperRationalPhasePenalty (μ : ProbabilityMeasure ℝ)
    (n m : LogIndex) (a : ℂ) :
    (∫ ξ, paperRationalPhasePenalty n m a ξ ∂(μ : Measure ℝ)) =
      (a * phaseMoment (paperPrimeSpectralPushforward μ) n.1 m.1).re := by
  change (∫ ξ, (a * paperRationalPhaseObservable n m ξ).re ∂(μ : Measure ℝ)) = _
  have hr : (∫ ξ, (a * paperRationalPhaseObservable n m ξ).re ∂(μ : Measure ℝ)) =
      (∫ ξ, a * paperRationalPhaseObservable n m ξ ∂(μ : Measure ℝ)).re :=
    Complex.reCLM.integral_comp_comm ((paperRationalPhaseObservable n m).integrable _ |>.const_mul a)
  rw [hr, integral_const_mul, integral_paperRationalPhaseObservable]

/-- Exact product-to-sum decomposition for arbitrary complex amplitudes. -/
theorem paperSingleArithmeticPenalty_mul_decomposition (n m : LogIndex) (a b : ℂ) :
    paperSingleArithmeticPenalty n a * paperSingleArithmeticPenalty m b =
      (1 / 2 : ℝ) • paperSingleArithmeticPenalty (paperProductLogIndex n m) (a * b) +
        (1 / 2 : ℝ) • paperRationalPhasePenalty n m (a * (starRingEnd ℂ) b) := by
  ext ξ
  change (paperSingleArithmeticPenalty n a ξ) * (paperSingleArithmeticPenalty m b ξ) =
    (1 / 2 : ℝ) * paperSingleArithmeticPenalty (paperProductLogIndex n m) (a * b) ξ +
      (1 / 2 : ℝ) * paperRationalPhasePenalty n m (a * (starRingEnd ℂ) b) ξ
  simp only [paperSingleArithmeticPenalty_apply, paperRationalPhasePenalty_apply,
    paperRationalPhaseObservable_apply, paperOriginPhaseObservable_product,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The arithmetic quotient keeps precisely the rational part of each mixed product. -/
theorem paperArithmeticPenaltyClass_single_mul (n m : LogIndex) (a b : ℂ) :
    paperArithmeticPenaltyClass (paperSingleArithmeticPenalty n a * paperSingleArithmeticPenalty m b) =
      paperArithmeticPenaltyClass ((1 / 2 : ℝ) •
        paperRationalPhasePenalty n m (a * (starRingEnd ℂ) b)) := by
  rw [paperSingleArithmeticPenalty_mul_decomposition, map_add, map_smul,
    paperArithmeticPenaltyClass_single, smul_zero, zero_add]

/-- Each single-phase coordinate is centered on every actual observed completion. -/
theorem integral_paperSingleArithmeticPenalty_zero
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (n : LogIndex) (a : ℂ) :
    (∫ ξ, paperSingleArithmeticPenalty n a ξ ∂(μ.1 : Measure ℝ)) = 0 :=
  integral_paperClosedArithmeticPenalty_zero c F μ
    ⟨_, paperSingleArithmeticPenalty_mem_closed n a⟩

/-- Mixed second moments are exact rational correlations, not additional free parameters. -/
theorem integral_paperSingleArithmeticPenalty_mul
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (n m : LogIndex) (a b : ℂ) :
    (∫ ξ, paperSingleArithmeticPenalty n a ξ * paperSingleArithmeticPenalty m b ξ
      ∂(μ.1 : Measure ℝ)) =
      (1 / 2 : ℝ) *
        ((a * (starRingEnd ℂ) b) * phaseMoment (paperPrimeSpectralPushforward μ.1) n.1 m.1).re := by
  have he := congrArg (paperArithmeticQuotientExpectation c F μ)
    (paperArithmeticPenaltyClass_single_mul n m a b)
  simp only [paperArithmeticQuotientExpectation_class] at he
  change (∫ ξ, paperSingleArithmeticPenalty n a ξ * paperSingleArithmeticPenalty m b ξ
    ∂(μ.1 : Measure ℝ)) = ∫ ξ,
      (1 / 2 : ℝ) * paperRationalPhasePenalty n m (a * (starRingEnd ℂ) b) ξ
        ∂(μ.1 : Measure ℝ) at he
  rw [integral_const_mul, integral_paperRationalPhasePenalty] at he
  exact he

/-- The actual gamma objective sees only the rational correlation part of a mixed penalty. -/
theorem paperPerturbedGammaExpectation_add_single_mul
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (G : ℝ →ᵇ ℝ)
    (n m : LogIndex) (a b : ℂ) :
    paperPerturbedGammaExpectation
        (G + paperSingleArithmeticPenalty n a * paperSingleArithmeticPenalty m b) μ.1 =
      paperPerturbedGammaExpectation (G + (1 / 2 : ℝ) •
        paperRationalPhasePenalty n m (a * (starRingEnd ℂ) b)) μ.1 := by
  apply paperPerturbedGammaExpectation_eq_of_class_eq c F μ
  rw [map_add, map_add, paperArithmeticPenaltyClass_single_mul]

/-- The attained optimization problem reduces exactly to the rational correlation penalty. -/
theorem paperObservedGammaValue_add_single_mul
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (n m : LogIndex) (a b : ℂ) :
    paperObservedGammaValue c F
        (G + paperSingleArithmeticPenalty n a * paperSingleArithmeticPenalty m b) =
      paperObservedGammaValue c F (G + (1 / 2 : ℝ) •
        paperRationalPhasePenalty n m (a * (starRingEnd ℂ) b)) := by
  apply paperObservedGammaValue_eq_of_class_eq
  rw [map_add, map_add, paperArithmeticPenaltyClass_single_mul]

end RHTower.WeilWorkPBAP
