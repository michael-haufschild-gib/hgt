import GaloisForLFunctions.RHTower.FiniteTimeBandFourierCompact

/-!
# Compact operators from continuous kernels

Continuous kernel sections on a compact input space define continuous fields
of `L²` functionals. On a compact output space, or after restricting output
to a compact set, these fields are square integrable. The corpus field-kernel
theorem gives compactness and the expected almost-everywhere integral formula.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev

variable {X Y 𝕜 : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y] [SecondCountableTopology X]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] [RCLike 𝕜]
  (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Kernel rows as a continuous family of square-integrable functions. -/
def continuousKernelSections (k : C(X × Y,𝕜)) : C(X,Lp 𝕜 2 ν) where
  toFun x := ContinuousMap.toLp 2 ν 𝕜 (k.curry x)
  continuous_toFun := (ContinuousMap.toLp 2 ν 𝕜).continuous.comp k.curry.continuous

/-- Integration against each kernel row as a continuous functional. -/
def continuousKernelFunctionals (k : C(X × Y,𝕜)) : C(X,Lp 𝕜 2 ν →L[𝕜] 𝕜) where
  toFun x := ((ContinuousLinearMap.lsmul 𝕜 𝕜).lpPairing ν 2 2)
    (continuousKernelSections ν k x)
  continuous_toFun := ((ContinuousLinearMap.lsmul 𝕜 𝕜).lpPairing ν 2 2).continuous.comp
    (continuousKernelSections ν k).continuous

/-- The square-integrable field of row functionals. -/
def continuousKernelField (k : C(X × Y,𝕜)) : Lp (Lp 𝕜 2 ν →L[𝕜] 𝕜) 2 μ :=
  ContinuousMap.toLp 2 μ 𝕜 (continuousKernelFunctionals ν k)

/-- The continuous-kernel integral operator on compact spaces. -/
def continuousKernelOperator (k : C(X × Y,𝕜)) : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ :=
  RHTower.kernelOperator μ (continuousKernelField μ ν k)

theorem continuousKernelOperator_compact (k : C(X × Y,𝕜)) :
    IsCompactOperator (continuousKernelOperator μ ν k) :=
  RHTower.isCompactOperator_kernelOperator μ (continuousKernelField μ ν k)

theorem continuousKernelOperator_coe (k : C(X × Y,𝕜)) (f : Lp 𝕜 2 ν) :
    (continuousKernelOperator μ ν k f : X → 𝕜) =ᵐ[μ]
      fun x => ∫ y,k (x,y)*f y ∂ν := by
  filter_upwards [
    (RHTower.evalBilinear (𝕜 := 𝕜) (E := Lp 𝕜 2 ν)).coeFn_holder
      (r := (2:ℝ≥0∞)) (continuousKernelField μ ν k) (Lp.const ∞ μ f),
    ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := (2:ℝ≥0∞)) (μ := μ)
      (continuousKernelFunctionals ν k),
    Lp.coeFn_const (p := ∞) μ f] with x hholder hfield hconst
  rw [continuousKernelOperator,RHTower.kernelOperator,RHTower.kernelOperatorMap_apply,
    hholder,continuousKernelField,hfield,hconst]
  change ((ContinuousLinearMap.lsmul 𝕜 𝕜).lpPairing ν 2 2
    (continuousKernelSections ν k x)) f = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := (2:ℝ≥0∞))
    (μ := ν) (k.curry x)] with y hy
  change (ContinuousLinearMap.lsmul 𝕜 𝕜)
    ((ContinuousMap.toLp 2 ν 𝕜 (k.curry x)) y) (f y)=_
  rw [hy]
  rfl

#print axioms RHTower.isCompactOperator_kernelOperator
#print axioms continuousKernelOperator_compact
end GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev

namespace GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev
variable {X Y 𝕜 : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace Y] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] [RCLike 𝕜]
  (μ : Measure X) (ν : Measure Y) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasure ν]

lemma continuousKernelFunctionals_memLp (S : Set X) (hS : IsCompact S)
    (k : C(X × Y,𝕜)) : MemLp (continuousKernelFunctionals ν k) 2 (μ.restrict S) := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hS.measure_lt_top (μ := μ)⟩
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn
    (continuousKernelFunctionals ν k).continuous.continuousOn
  refine MemLp.of_bound ((continuousKernelFunctionals ν k).continuous.continuousOn.aestronglyMeasurable
    hS.measurableSet) C ?_
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC x hx

/-- Row functionals restricted to a compact output set. -/
def compactOutputKernelField (S : Set X) (hS : IsCompact S) (k : C(X × Y,𝕜)) :
    Lp (Lp 𝕜 2 ν →L[𝕜] 𝕜) 2 (μ.restrict S) :=
  (continuousKernelFunctionals_memLp μ ν S hS k).toLp (continuousKernelFunctionals ν k)

/-- The integral operator with output measured on a compact set. -/
def compactOutputKernelOperator (S : Set X) (hS : IsCompact S) (k : C(X × Y,𝕜)) :
    Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 (μ.restrict S) := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hS.measure_lt_top (μ := μ)⟩
  exact RHTower.kernelOperator (μ.restrict S) (compactOutputKernelField μ ν S hS k)

theorem compactOutputKernelOperator_compact (S : Set X) (hS : IsCompact S)
    (k : C(X × Y,𝕜)) : IsCompactOperator (compactOutputKernelOperator μ ν S hS k) := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hS.measure_lt_top (μ := μ)⟩
  exact RHTower.isCompactOperator_kernelOperator (μ.restrict S) (compactOutputKernelField μ ν S hS k)

lemma compactOutputKernelOperator_coe (S : Set X) (hS : IsCompact S)
    (k : C(X × Y,𝕜)) (f : Lp 𝕜 2 ν) :
    (compactOutputKernelOperator μ ν S hS k f : X → 𝕜) =ᵐ[μ.restrict S]
      fun x => ∫y,k (x,y)*f y ∂ν := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hS.measure_lt_top (μ := μ)⟩
  filter_upwards [
    (RHTower.evalBilinear (𝕜 := 𝕜) (E := Lp 𝕜 2 ν)).coeFn_holder
      (r := (2:ℝ≥0∞)) (compactOutputKernelField μ ν S hS k) (Lp.const ∞ (μ.restrict S) f),
    (continuousKernelFunctionals_memLp μ ν S hS k).coeFn_toLp,
    Lp.coeFn_const (p := ∞) (μ.restrict S) f] with x hholder hfield hconst
  rw [compactOutputKernelOperator,RHTower.kernelOperator,RHTower.kernelOperatorMap_apply,
    hholder,compactOutputKernelField,hfield,hconst]
  change ((ContinuousLinearMap.lsmul 𝕜 𝕜).lpPairing ν 2 2
    (continuousKernelSections ν k x)) f = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := (2:ℝ≥0∞))
    (μ := ν) (k.curry x)] with y hy
  change (ContinuousLinearMap.lsmul 𝕜 𝕜)
    ((ContinuousMap.toLp 2 ν 𝕜 (k.curry x)) y) (f y)=_
  rw [hy]
  rfl

#print axioms compactOutputKernelOperator_coe
#print axioms compactOutputKernelOperator_compact
end GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev
