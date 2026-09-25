import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWOperatorAnomalyLaw
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCovector
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareSourceDifferential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsLiftDefect
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWLiteralKernelGreenContact

/-!
# Actual PW-B source anomaly on the positive-height chart

The full angular field and every literal gated full kernel satisfy the
triangular operator relation on the complete positive-height chart, without
an angular-mode decomposition or an `L²` admission. The signed full-minus-
native reader's anomaly is exactly the coupling times the full-minus-native
kernel, including its direct/image gates and Goursat cone correction. The
already admitted two-event Peierls lift is therefore an absolutely integrable
operator anomaly. Noncompact cap incidence and extinction remain open.
-/

open Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.D4BMPWActualOperatorAnomaly
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries
open D4BMHorizon D4BMPWOperatorAnomaly D4BMLiteralCyclicPeierlsLiftDefect
open D4BMPWLiteralKernelGreenContact D4BMNativeCircle D4BMJointSource

noncomputable section
set_option autoImplicit false

abbrev PositivePoint := {z : Fin 2 → ℝ // 0 < z 1}
abbrev PositiveField := PositivePoint → ℂ

def positiveRestrict (f : (Fin 2 → ℝ) → ℂ) : PositiveField :=
  fun z => f z.1

def positiveExtend (f : PositiveField) : (Fin 2 → ℝ) → ℂ :=
  fun z => if hz : 0 < z 1 then f ⟨z,hz⟩ else 0

def positiveAngularOperator (f : PositiveField) : PositiveField :=
  fun z => hyperbolicLaplacian (positiveExtend f) z.1

/-- The actual full/square source equation holds globally as an equality of
fields on the positive-height chart. Zero extension is used only to feed the
coordinate Laplacian; germ locality removes the artificial lower boundary. -/
theorem physical_positive_source_relation (q : XiZeroCopy) (branch : Bool) :
    positiveAngularOperator (positiveRestrict (fullAngularField q branch)) =
      parameter q branch •
        (positiveRestrict (fullAngularField q branch) +
          positiveRestrict (fullSquarePotential q)) := by
  funext ⟨z,hz⟩
  have hopen : {w : Fin 2 → ℝ | (0 : ℝ) < w 1} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have he : positiveExtend (positiveRestrict (fullAngularField q branch)) =ᶠ[𝓝 z]
      fullAngularField q branch := by
    filter_upwards [hopen] with w hw
    simp [positiveExtend, positiveRestrict, hw]
  change hyperbolicLaplacian
      (positiveExtend (positiveRestrict (fullAngularField q branch))) z =
    parameter q branch *
      (fullAngularField q branch z + fullSquarePotential q z)
  calc
    _ = hyperbolicLaplacian (fullAngularField q branch) z :=
      hyperbolicLaplacian_congr he
    _ = _ := by
      have hs : scalarLaplacian (fullAngularField q branch) z -
          parameter q branch *
            (fullAngularField q branch z + fullSquarePotential q z) = 0 := by
        rw [fullAngularField_equation q branch z hz]
        unfold fullSquarePotential
        ring
      rw [D4BMHorizon.scalarLaplacian_eq _ z hz] at hs
      change hyperbolicLaplacian (fullAngularField q branch) z -
        parameter q branch *
          (fullAngularField q branch z + fullSquarePotential q z) = 0 at hs
      exact sub_eq_zero.mp hs

/-- Every complex-linear full/native reader obeys the exact anomaly budget
on the actual theta source, with no spectral or locality restriction. -/
theorem actual_source_operator_anomaly (q : XiZeroCopy) (branch : Bool)
    (S : (PositiveField × PositiveField) →ₗ[ℂ]
      (PositiveField × PositiveField)) :
    firstRowAnomaly (parameter q branch) positiveAngularOperator S
      (positiveRestrict (fullAngularField q branch)) =
    parameter q branch •
      (S (positiveRestrict (fullAngularField q branch),
        positiveRestrict (fullSquarePotential q))).1 := by
  exact firstRowAnomaly_eq_fullSourceReadout
    (parameter q branch) positiveAngularOperator S
    (positiveRestrict (fullAngularField q branch))
    (positiveRestrict (fullSquarePotential q))
    (physical_positive_source_relation q branch)

/-- The literal full-minus-native Peierls source vertex is the normalized
operator anomaly of the signed channel reader, at every physical event. -/
theorem actual_lift_vertex_anomaly (q : XiZeroCopy) (branch : Bool)
    (X k : ℝ) :
    firstRowAnomaly (parameter q branch) positiveAngularOperator
      (differenceReader (E := PositiveField))
      (positiveRestrict (fullAngularField q branch))
        ⟨![X, Real.exp k], Real.exp_pos k⟩ =
      parameter q branch * causalVertexDefect q branch X k := by
  rw [differenceReader_source_anomaly (parameter q branch) positiveAngularOperator
    (positiveRestrict (fullAngularField q branch))
    (positiveRestrict (fullSquarePotential q))
    (physical_positive_source_relation q branch)]
  rfl

/-- Native partner of the literal full causal kernel in physical height. -/
def nativePhysicalKernel (q : XiZeroCopy) (h x y : ℝ)
    (z : Fin 2 → ℝ) : ℂ :=
  nativeDirichletCausalKernel q h x y (z 0) (Real.log (z 1))

/-- The literal gated full kernel, not only its source vertex, satisfies the
full-plus-native equation as a field on the positive-height chart. -/
theorem physical_positive_kernel_relation (q : XiZeroCopy) (branch : Bool)
    (h x y : ℝ) :
    positiveAngularOperator (positiveRestrict (physicalKernel q branch h x y)) =
      parameter q branch •
        (positiveRestrict (physicalKernel q branch h x y) +
          positiveRestrict (nativePhysicalKernel q h x y)) := by
  funext ⟨z,hz⟩
  have hopen : {w : Fin 2 → ℝ | (0 : ℝ) < w 1} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have he : positiveExtend (positiveRestrict (physicalKernel q branch h x y)) =ᶠ[𝓝 z]
      physicalKernel q branch h x y := by
    filter_upwards [hopen] with w hw
    simp [positiveExtend, positiveRestrict, hw]
  change hyperbolicLaplacian
      (positiveExtend (positiveRestrict (physicalKernel q branch h x y))) z =
    parameter q branch *
      (physicalKernel q branch h x y z + nativePhysicalKernel q h x y z)
  calc
    _ = hyperbolicLaplacian (physicalKernel q branch h x y) z :=
      hyperbolicLaplacian_congr he
    _ = _ := by
      have hs := physicalKernel_scalarLaplacian q branch h x y z hz
      rw [D4BMHorizon.scalarLaplacian_eq _ z hz] at hs
      exact hs

/-- The entire direct-minus-image full/native kernel is the normalized
operator anomaly. No Goursat cone term is dropped. -/
theorem actual_lift_kernel_anomaly (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) :
    firstRowAnomaly (parameter q branch) positiveAngularOperator
      (differenceReader (E := PositiveField))
      (positiveRestrict (physicalKernel q branch h x y))
        ⟨![X, Real.exp k], Real.exp_pos k⟩ =
      parameter q branch *
        angularNativePeierlsDefect q branch h x y X k := by
  rw [differenceReader_source_anomaly (parameter q branch) positiveAngularOperator
    (positiveRestrict (physicalKernel q branch h x y))
    (positiveRestrict (nativePhysicalKernel q h x y))
    (physical_positive_kernel_relation q branch h x y)]
  simp [angularNativePeierlsDefect, physicalKernel, nativePhysicalKernel, positiveRestrict]

/-- Original ordered source legs paired through the full-kernel anomaly. -/
def sourcePairAnomalyDensity (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (z : Event × Event) : ℂ :=
  timeReducedCoefficient (physicalRate q b) a z.1.1 z.1.2 *
    firstRowAnomaly (parameter q branch) positiveAngularOperator
      (differenceReader (E := PositiveField))
      (positiveRestrict (physicalKernel q branch
        (z.2.1 - z.1.1) z.1.2 z.2.2))
        ⟨![X, Real.exp k], Real.exp_pos k⟩ *
    timeReducedCoefficient (physicalRate q c) d z.2.1 z.2.2

theorem sourcePairAnomalyDensity_eq (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (z : Event × Event) :
    sourcePairAnomalyDensity q branch b c a d X k z =
      parameter q branch * sourcePairLiftDefect q branch b c a d X k z := by
  unfold sourcePairAnomalyDensity sourcePairLiftDefect
  rw [actual_lift_kernel_anomaly]
  ring

/-- The genuine two-source anomaly is absolutely admitted by the existing
full/native source estimates, with no boundary or cutoff premise. -/
theorem sourcePairAnomalyDensity_integrable (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    Integrable (sourcePairAnomalyDensity q branch b c a d X k)
      (eventMeasure.prod eventMeasure) := by
  convert (sourcePairLiftDefect_integrable q branch b c a d X k).const_mul
    (parameter q branch) using 1
  funext z
  exact sourcePairAnomalyDensity_eq q branch b c a d X k z

/-- Antisymmetrized, integrated operator anomaly of the two original legs. -/
def causalSourceAnomaly (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) : ℂ :=
  (∫ z, sourcePairAnomalyDensity q branch c b d a X k z
    ∂eventMeasure.prod eventMeasure) -
  ∫ z, sourcePairAnomalyDensity q branch b c a d X k z
    ∂eventMeasure.prod eventMeasure

/-- Exact anomaly realization of the entire literal two-event Peierls lift.
It includes both source orders, causal gates, images, and cone corrections. -/
theorem causalSourceAnomaly_eq_liftDefect (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    causalSourceAnomaly q branch b c a d X k =
      parameter q branch * causalSourceLiftDefect q branch b c a d X k := by
  unfold causalSourceAnomaly causalSourceLiftDefect
  simp_rw [sourcePairAnomalyDensity_eq]
  rw [integral_const_mul, integral_const_mul]
  ring

/-- Defect-Ward normal form of the actual branchwise CTP source. The native
pair and its physical cap remain explicit; no cap incidence is inferred. -/
theorem fullCausalSourcePair_anomaly (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    parameter q branch * D4BMFullAngularCausalPeierls.fullCausalSourcePair
      q branch b c a d X k =
      parameter q branch * D4BMFullSourceReciprocity.causalSourcePair q b c a d X k +
        causalSourceAnomaly q branch b c a d X k := by
  rw [fullCausalSourcePair_eq_native_add_liftDefect,
    causalSourceAnomaly_eq_liftDefect]
  ring

end
end RHTower.D4BMPWActualOperatorAnomaly
