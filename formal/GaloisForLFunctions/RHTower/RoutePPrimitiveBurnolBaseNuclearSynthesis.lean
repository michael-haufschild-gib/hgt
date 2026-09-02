/-
Literal all-prime Burnol synthesis and its strict sub-unit nuclear covariance.

P-G186 supplies actual half-line L2 columns whose full Gram is the primitive base-Cauchy kernel.
This module assembles every prime-depth column, at zero source clock, into one Bochner synthesis
over counting measure.  Its Hilbert--Schmidt mass is exactly the literal base-Cauchy budget.  The
new sharp arithmetic bound makes that unscaled budget strictly smaller than one.
-/
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolMatrixCompleteColligation
import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open Complex Matrix Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

local instance routePPrimitiveFactTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) :=
  ⟨by norm_num⟩

abbrev RoutePPrimitiveIndex := Nat.Primes × ℕ

local instance : MeasurableSpace RoutePPrimitiveIndex := ⊤

/-- Actual zero-clock Burnol column for one resolved prime-depth source cell. -/
def routePPrimitiveBurnolBaseField
    (pe : RoutePPrimitiveIndex) : routePBurnolHalfLineL2 :=
  routePPrimitiveBurnolWindowFeatureLp pe 0

/-- Each column norm is exactly its unsquared-Euler base-Cauchy diagonal weight. -/
theorem norm_sq_routePPrimitiveBurnolBaseField
    (pe : RoutePPrimitiveIndex) :
    ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 =
      routePPrimitiveBaseCauchyCubicWeight pe := by
  let labels : Fin 1 → RoutePPrimitiveIndex := fun _ => pe
  let clocks : Fin 1 → ℝ := fun _ => 0
  have hgram := congrArg (fun M => M (0 : Fin 1) (0 : Fin 1))
    (routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2 labels clocks)
  have hbase := congrArg (fun M => M (0 : Fin 1) (0 : Fin 1))
    (routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy labels clocks)
  have hdiag := routePPrimitiveBaseCauchyCubicKernelMatrix_diagonal
    (R := (1 : ℝ)) (by norm_num) labels clocks (0 : Fin 1)
  dsimp [labels, clocks] at hgram hbase hdiag
  rw [routePPrimitiveBurnolBaseField]
  rw [inner_self_eq_norm_sq_to_K] at hgram
  have hcomplex : (‖routePPrimitiveBurnolWindowFeatureLp pe 0‖ ^ 2 : ℂ) =
      routePPrimitiveBaseCauchyCubicWeight pe := by
    calc
      (‖routePPrimitiveBurnolWindowFeatureLp pe 0‖ ^ 2 : ℂ) =
          routePPrimitiveBurnolWindowGramMatrix labels clocks 0 0 := hgram.symm
      _ = routePPrimitiveBaseCauchyCubicKernelMatrix 1 labels clocks 0 0 := hbase
      _ = routePPrimitiveBaseCauchyCubicWeight pe := hdiag
  exact_mod_cast hcomplex

theorem summable_norm_sq_routePPrimitiveBurnolBaseField :
    Summable (fun pe : RoutePPrimitiveIndex =>
      ‖routePPrimitiveBurnolBaseField pe‖ ^ 2) := by
  apply summable_routePPrimitiveBaseCauchyCubicWeight.congr
  intro pe
  exact (norm_sq_routePPrimitiveBurnolBaseField pe).symm

theorem integrable_norm_sq_routePPrimitiveBurnolBaseField :
    Integrable (fun pe : RoutePPrimitiveIndex =>
      ‖routePPrimitiveBurnolBaseField pe‖ ^ 2) Measure.count := by
  rw [integrable_count_iff]
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using
    summable_norm_sq_routePPrimitiveBurnolBaseField

theorem memLp_two_routePPrimitiveBurnolBaseField :
    MemLp routePPrimitiveBurnolBaseField 2
      (Measure.count : Measure RoutePPrimitiveIndex) := by
  rw [memLp_two_iff_integrable_sq_norm]
  · exact integrable_norm_sq_routePPrimitiveBurnolBaseField
  · fun_prop

/-- One vector-valued L2 field containing every resolved prime-depth column. -/
def routePPrimitiveBurnolBaseFieldLp :
    Lp routePBurnolHalfLineL2 2
      (Measure.count : Measure RoutePPrimitiveIndex) :=
  memLp_two_routePPrimitiveBurnolBaseField.toLp
    routePPrimitiveBurnolBaseField

/-- Literal all-prime synthesis; no Xi divisor or adjustable normalization enters. -/
def routePPrimitiveBurnolBaseSynthesis :
    Lp ℂ 2 (Measure.count : Measure RoutePPrimitiveIndex) →L[ℂ]
      routePBurnolHalfLineL2 :=
  l2Synthesis Measure.count routePPrimitiveBurnolBaseFieldLp

theorem norm_sq_routePPrimitiveBurnolBaseFieldLp :
    ‖routePPrimitiveBurnolBaseFieldLp‖ ^ 2 =
      routePPrimitiveBaseCauchyCubicTraceBudget := by
  rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  calc
    (∫ pe, ‖routePPrimitiveBurnolBaseFieldLp pe‖ ^ 2 ∂Measure.count) =
        ∫ pe, ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 ∂Measure.count := by
      apply integral_congr_ae
      filter_upwards [memLp_two_routePPrimitiveBurnolBaseField.coeFn_toLp] with pe hpe
      exact congrArg (fun z : routePBurnolHalfLineL2 => ‖z‖ ^ 2) hpe
    _ = ∑' pe, ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 := by
      rw [integral_countable integrable_norm_sq_routePPrimitiveBurnolBaseField]
      simp
    _ = routePPrimitiveBaseCauchyCubicTraceBudget := by
      rw [routePPrimitiveBaseCauchyCubicTraceBudget]
      exact tsum_congr norm_sq_routePPrimitiveBurnolBaseField

/-- The whole literal source synthesis is Hilbert--Schmidt. -/
theorem routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt :
    (routePPrimitiveBurnolBaseSynthesis).IsHilbertSchmidt :=
  l2Synthesis_isHilbertSchmidt Measure.count routePPrimitiveBurnolBaseFieldLp

/-- Its Hilbert--Schmidt mass is exactly the complete base-Cauchy budget. -/
theorem hsNormSq_routePPrimitiveBurnolBaseSynthesis_eq_budget :
    ContinuousLinearMap.hsNormSq routePPrimitiveBurnolBaseSynthesis =
      routePPrimitiveBaseCauchyCubicTraceBudget := by
  rw [routePPrimitiveBurnolBaseSynthesis,
    hsNormSq_l2Synthesis_eq_norm_sq,
    norm_sq_routePPrimitiveBurnolBaseFieldLp]

/-- Positive source covariance of the literal all-prime synthesis. -/
def routePPrimitiveBurnolBaseNuclearSource :
    routePBurnolHalfLineL2 →L[ℂ] routePBurnolHalfLineL2 :=
  rangeCovariance routePPrimitiveBurnolBaseSynthesis

theorem routePPrimitiveBurnolBaseNuclearSource_memSchattenClass_one :
    MemSchattenClass 1 routePPrimitiveBurnolBaseNuclearSource := by
  rw [routePPrimitiveBurnolBaseNuclearSource]
  exact rangeCovariance_l2Synthesis_memSchattenClass_one
    Measure.count routePPrimitiveBurnolBaseFieldLp

/-- Exact trace conservation from primitive source mass to nuclear covariance. -/
theorem re_opTrace_routePPrimitiveBurnolBaseNuclearSource_eq_budget :
    (ContinuousLinearMap.opTrace
      routePPrimitiveBurnolBaseNuclearSource).re =
        routePPrimitiveBaseCauchyCubicTraceBudget := by
  rw [routePPrimitiveBurnolBaseNuclearSource,
    routePPrimitiveBurnolBaseSynthesis,
    re_opTrace_rangeCovariance_l2Synthesis_eq_norm_sq,
    norm_sq_routePPrimitiveBurnolBaseFieldLp]

/-- The unscaled literal prime-mixed nuclear source lies strictly below one unit. -/
theorem re_opTrace_routePPrimitiveBurnolBaseNuclearSource_lt_one :
    (ContinuousLinearMap.opTrace
      routePPrimitiveBurnolBaseNuclearSource).re < 1 := by
  rw [re_opTrace_routePPrimitiveBurnolBaseNuclearSource_eq_budget]
  exact routePPrimitiveBaseCauchyCubicTraceBudget_lt_one

end
end RHTower
