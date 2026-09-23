import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCausalPeierlsPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCausalDifference

/-!
# Literal full-circle Peierls lift defect

The pre-existing native causal pairing already has an exact expression through
the original retarded field, corrected future field, and cap.  The physical
two-leg metric, however, uses the full angular response.  This file gives the
exact difference: its vertex is `fullAngularField - fullSquarePotential` and
its cone term is the corresponding direct-minus-image Goursat correction.

Proof-chain role:
`full-circle Peierls pairing = original retarded/future/cap pairing + explicit
full-minus-native lift defect`.  Thus the remaining metric-incidence problem is
to realize this displayed defect at the cap/contact boundary; no source kernel
or image term is left implicit.
-/

open Set MeasureTheory Filter Topology

namespace RHTower.D4BMLiteralCyclicPeierlsLiftDefect

open GaloisForLFunctions.HTGeometry
open D4BMNativeCircle D4BMCausalKernel D4BMJointSource D4BMModularCore
open D4BMFullAngularCircle D4BMFullAngularReconstruction D4BMFullAngularGoursat
open D4BMFullAngularCausalPeierls D4BMFullSourceReciprocity
open D4BMOriginalCausalDifference
open D4BMOriginalCausalPotential D4BMCompleteOriginalWeakSource D4BMFutureHorizon

noncomputable section
set_option autoImplicit false

abbrev Event := ℝ × ℝ

abbrev eventMeasure : Measure Event :=
  (volume.restrict (Ioi 0)).prod (volume.restrict (Iio 0))

/-- Difference between the literal full angular vertex and the native source vertex. -/
def causalVertexDefect (q : XiZeroCopy) (branch : Bool) (X k : ℝ) : ℂ :=
  fullAngularField q branch ![X, Real.exp k] - fullSquarePotential q ![X, Real.exp k]

/-- Difference of the actual full and native Goursat corrections in one causal cone. -/
def causalCorrectionDefect (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) : ℂ :=
  fullAngularCorrection q branch h x y X k - nativeAngularCorrection q h x y X k

/-- Literal direct-minus-image difference between the full and native causal kernels. -/
def angularNativePeierlsDefect (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) : ℂ :=
  angularDirichletKernel q branch h x y X k - nativeDirichletCausalKernel q h x y X k

/-- The full/native discrepancy is exactly its physical vertex defect plus its
direct-minus-image cone defect.  Both causal gates and the factor `1/2` remain. -/
theorem angularNativePeierlsDefect_volterra (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) :
    angularNativePeierlsDefect q branch h x y X k =
      ((if |x - y| ≤ h then causalVertexDefect q branch X k else 0) -
        (if |x + y| ≤ h then causalVertexDefect q branch X k else 0)) / 2 +
      (causalCorrectionDefect q branch h x y X k -
        causalCorrectionDefect q branch h x (-y) X k) / 2 := by
  unfold angularNativePeierlsDefect
  rw [fullAngularDirichletKernel_volterra, nativeDirichletCausalKernel_volterra]
  unfold causalVertexDefect causalCorrectionDefect
  by_cases hxy : |x-y| ≤ h <;> by_cases hsum : |x+y| ≤ h <;>
    simp [hxy, hsum] <;> ring

/-- Two original source events paired through precisely the full-minus-native
direct-minus-image causal defect. -/
def sourcePairLiftDefect (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ)
    (z : Event × Event) : ℂ :=
  timeReducedCoefficient (physicalRate q b) a z.1.1 z.1.2 *
    angularNativePeierlsDefect q branch (z.2.1 - z.1.1) z.1.2 z.2.2 X k *
      timeReducedCoefficient (physicalRate q c) d z.2.1 z.2.2

/-- The literal full source density is the native density plus the displayed
full-circle lift defect. -/
theorem fullSourcePairDensity_eq_native_add_defect (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) (z : Event × Event) :
    fullSourcePairDensity q branch b c a d X k z =
      sourcePairDensity q b c a d X k z +
        sourcePairLiftDefect q branch b c a d X k z := by
  unfold fullSourcePairDensity sourcePairDensity sourcePairLiftDefect
  unfold angularNativePeierlsDefect
  ring

/-- The new lift defect is absolutely admitted on both original source events;
this is inherited from the full and native physical source admissions, not
assumed as a boundary premise. -/
theorem sourcePairLiftDefect_integrable (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    Integrable (sourcePairLiftDefect q branch b c a d X k)
      (eventMeasure.prod eventMeasure) := by
  have hfull := fullSourcePairDensity_integrable q branch b c a d X k
  have hnative := sourcePairDensity_integrable q b c a d X k
  convert hfull.sub hnative using 1
  funext z
  change sourcePairLiftDefect q branch b c a d X k z =
    fullSourcePairDensity q branch b c a d X k z - sourcePairDensity q b c a d X k z
  rw [fullSourcePairDensity_eq_native_add_defect]
  ring

/-- Antisymmetrized two-source contribution of the full-minus-native lift defect. -/
def causalSourceLiftDefect (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) : ℂ :=
  (∫ z, sourcePairLiftDefect q branch c b d a X k z ∂eventMeasure.prod eventMeasure) -
    ∫ z, sourcePairLiftDefect q branch b c a d X k z ∂eventMeasure.prod eventMeasure

/-- The literal full-circle Peierls pairing differs from the already admitted
native Peierls pairing by exactly the displayed lift defect. -/
theorem fullCausalSourcePair_eq_native_add_liftDefect (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    fullCausalSourcePair q branch b c a d X k =
      causalSourcePair q b c a d X k + causalSourceLiftDefect q branch b c a d X k := by
  rw [fullCausalSourcePair_decomposition, causalSourcePair_decomposition,
    causalSourceLiftDefect]
  simp_rw [fullSourcePairDensity_eq_native_add_defect]
  rw [integral_add (sourcePairDensity_integrable q c b d a X k)
      (sourcePairLiftDefect_integrable q branch c b d a X k),
    integral_add (sourcePairDensity_integrable q b c a d X k)
      (sourcePairLiftDefect_integrable q branch b c a d X k)]
  ring

/-- Full-circle causal Peierls pairing in literal physical fields.  The first
integral is the existing original retarded field minus corrected future field
minus its source-derived cap; the sole added term is the explicit full-circle
lift defect above. -/
theorem fullCausalSourcePair_original_fields_liftDefect (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    fullCausalSourcePair q branch b c a d X k =
      (∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        (originalPotential q c d (p.1 + p.2) (p.1 - p.2) X k -
          correctedFutureField q c d (p, X + Complex.I * k) -
            capBoundaryField q c d p.1 p.2 X k) ∂eventMeasure) +
      causalSourceLiftDefect q branch b c a d X k := by
  rw [fullCausalSourcePair_eq_native_add_liftDefect,
    causalSourcePair_original_fields]

end

end RHTower.D4BMLiteralCyclicPeierlsLiftDefect
