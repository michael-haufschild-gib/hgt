import GaloisForLFunctions.RHTower.WeilPaperArithmeticNormedQuotient

/-!
# Squaring an invisible arithmetic penalty

A single integer logarithmic phase has zero expectation, but the square of
its real projection has expectation exactly half the squared amplitude.
Modulo closed arithmetic directions, this square is exactly a constant.
Thus squaring shifts gamma values by an explicit positive amount while
preserving minimizers. The invisible subspace is not closed under squaring.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- A single real projection of an integer logarithmic Fourier phase. -/
def paperSingleArithmeticPenalty (n : LogIndex) (a : ℂ) : ℝ →ᵇ ℝ :=
  paperArithmeticSpectralPenalty {n} (fun _ => a)

@[simp] theorem paperSingleArithmeticPenalty_apply (n : LogIndex) (a : ℂ) (ξ : ℝ) :
    paperSingleArithmeticPenalty n a ξ = (a * paperOriginPhaseObservable n ξ).re := by
  simp only [paperSingleArithmeticPenalty, paperArithmeticSpectralPenalty,
    paperFiniteSpectralPenalty_apply, Finset.sum_singleton]

/-- The squared integer remains an admissible origin frequency. -/
def paperSquaredLogIndex (n : LogIndex) : LogIndex :=
  ⟨n.1 * n.1, by have := n.2; nlinarith⟩

theorem paperOriginPhaseObservable_squared (n : LogIndex) (ξ : ℝ) :
    paperOriginPhaseObservable (paperSquaredLogIndex n) ξ =
      paperOriginPhaseObservable n ξ * paperOriginPhaseObservable n ξ := by
  apply arithmeticPhase_mul <;> have := n.2 <;> omega

/-- The arithmetic phase has exactly unit squared modulus. -/
theorem paperOriginPhaseObservable_re_sq_add_im_sq (n : LogIndex) (ξ : ℝ) :
    (paperOriginPhaseObservable n ξ).re ^ 2 +
      (paperOriginPhaseObservable n ξ).im ^ 2 = 1 := by
  have h := congrArg Complex.re (arithmeticPhase_mul_conj n.1 (primeSpectralPoint ξ))
  simpa only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re,
    mul_neg, sub_neg_eq_add, pow_two, paperOriginPhaseObservable_apply] using h

/-- Exact decomposition into a constant plus an invisible doubled-frequency penalty. -/
theorem paperSingleArithmeticPenalty_sq_decomposition (n : LogIndex) (a : ℂ) :
    paperSingleArithmeticPenalty n a ^ 2 =
      BoundedContinuousFunction.const ℝ (‖a‖ ^ 2 / 2) +
        (1 / 2 : ℝ) • paperSingleArithmeticPenalty (paperSquaredLogIndex n) (a * a) := by
  ext ξ
  change (paperSingleArithmeticPenalty n a ξ) ^ 2 = ‖a‖ ^ 2 / 2 +
    (1 / 2 : ℝ) * paperSingleArithmeticPenalty (paperSquaredLogIndex n) (a * a) ξ
  rw [paperSingleArithmeticPenalty_apply, paperSingleArithmeticPenalty_apply,
    paperOriginPhaseObservable_squared, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hz := paperOriginPhaseObservable_re_sq_add_im_sq n ξ
  have hm := congrArg (fun t : ℝ => (a.re ^ 2 + a.im ^ 2) * t) hz
  simp only [Complex.mul_re, Complex.mul_im]
  nlinarith

theorem paperSingleArithmeticPenalty_mem_closed (n : LogIndex) (a : ℂ) :
    paperSingleArithmeticPenalty n a ∈ paperClosedArithmeticPenalties :=
  paperArithmeticSpectralPenalty_mem_closed {n} (fun _ => a)

@[simp] theorem paperArithmeticPenaltyClass_single (n : LogIndex) (a : ℂ) :
    paperArithmeticPenaltyClass (paperSingleArithmeticPenalty n a) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (paperSingleArithmeticPenalty_mem_closed n a)

/-- Every squared single phase is the constant half-amplitude square in the quotient. -/
theorem paperArithmeticPenaltyClass_single_sq (n : LogIndex) (a : ℂ) :
    paperArithmeticPenaltyClass (paperSingleArithmeticPenalty n a ^ 2) =
      paperArithmeticPenaltyClass (BoundedContinuousFunction.const ℝ (‖a‖ ^ 2 / 2)) := by
  rw [paperSingleArithmeticPenalty_sq_decomposition, map_add, map_smul,
    paperArithmeticPenaltyClass_single, smul_zero, add_zero]

/-- The exact second moment holds for every law in every observed native completion. -/
theorem integral_paperSingleArithmeticPenalty_sq
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (n : LogIndex) (a : ℂ) :
    (∫ ξ, (paperSingleArithmeticPenalty n a ξ) ^ 2 ∂(μ.1 : Measure ℝ)) = ‖a‖ ^ 2 / 2 := by
  have he := congrArg (paperArithmeticQuotientExpectation c F μ)
    (paperArithmeticPenaltyClass_single_sq n a)
  simpa only [paperArithmeticQuotientExpectation_class, BoundedContinuousFunction.pow_apply,
    BoundedContinuousFunction.const_apply, integral_const, probReal_univ, one_smul] using he

/-- Squaring shifts every actual feasible gamma objective by the same explicit amount. -/
theorem paperPerturbedGammaExpectation_add_single_sq
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (G : ℝ →ᵇ ℝ) (n : LogIndex) (a : ℂ) :
    paperPerturbedGammaExpectation (G + paperSingleArithmeticPenalty n a ^ 2) μ.1 =
      paperPerturbedGammaExpectation G μ.1 + ‖a‖ ^ 2 / 2 := by
  rw [paperPerturbedGammaExpectation_add]
  exact congrArg (fun t => paperPerturbedGammaExpectation G μ.1 + t)
    (integral_paperSingleArithmeticPenalty_sq c F μ n a)

/-- The attained gamma value has the same exact half-amplitude-square shift. -/
theorem paperObservedGammaValue_add_single_sq
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (n : LogIndex) (a : ℂ) :
    paperObservedGammaValue c F (G + paperSingleArithmeticPenalty n a ^ 2) =
      paperObservedGammaValue c F G + ‖a‖ ^ 2 / 2 := by
  calc
    _ = paperObservedGammaValue c F
        (G + BoundedContinuousFunction.const ℝ (‖a‖ ^ 2 / 2)) := by
      apply paperObservedGammaValue_eq_of_class_eq
      rw [map_add, map_add, paperArithmeticPenaltyClass_single_sq]
    _ = _ := paperObservedGammaValue_add_const c F G _

/-- Although the squared penalty changes the value, it preserves every feasible objective comparison. -/
theorem paperSingleArithmeticPenalty_sq_order_iff
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ ν : PaperObservedSpectralCompletion c F) (G : ℝ →ᵇ ℝ) (n : LogIndex) (a : ℂ) :
    paperPerturbedGammaExpectation (G + paperSingleArithmeticPenalty n a ^ 2) μ.1 ≤
        paperPerturbedGammaExpectation (G + paperSingleArithmeticPenalty n a ^ 2) ν.1 ↔
      paperPerturbedGammaExpectation G μ.1 ≤ paperPerturbedGammaExpectation G ν.1 := by
  rw [paperPerturbedGammaExpectation_add_single_sq c F μ,
    paperPerturbedGammaExpectation_add_single_sq c F ν, add_le_add_iff_right]

/-- The effective norm of the squared penalty is exactly half the squared amplitude. -/
theorem norm_paperArithmeticPenaltyClass_single_sq
    (c : ComplexNullMixture) (n : LogIndex) (a : ℂ) :
    ‖paperArithmeticPenaltyClass (paperSingleArithmeticPenalty n a ^ 2)‖ = ‖a‖ ^ 2 / 2 := by
  rw [paperArithmeticPenaltyClass_single_sq, norm_paperArithmeticPenaltyClass_const c,
    abs_of_nonneg (by positivity)]

/-- A unit-amplitude invisible direction has a square outside the invisible subspace. -/
theorem paperSingleArithmeticPenalty_one_sq_not_mem
    (c : ComplexNullMixture) (n : LogIndex) :
    paperSingleArithmeticPenalty n 1 ^ 2 ∉ paperClosedArithmeticPenalties := by
  intro h
  have hz : paperArithmeticPenaltyClass (paperSingleArithmeticPenalty n 1 ^ 2) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr h
  have hn := norm_paperArithmeticPenaltyClass_single_sq c n 1
  have hn0 : ‖(0 : PaperArithmeticPenaltyQuotient)‖ = 0 :=
    @norm_zero PaperArithmeticPenaltyQuotient _
  rw [hz, hn0, norm_one, one_pow] at hn
  linarith

end RHTower.WeilWorkPBAP
