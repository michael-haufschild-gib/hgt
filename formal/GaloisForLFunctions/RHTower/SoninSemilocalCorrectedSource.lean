import GaloisForLFunctions.RHTower.SoninPrincipalShellCyclicTrace
import GaloisForLFunctions.RHTower.SoninSemilocalCyclicWeylDescent
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# Finite cyclic Sonin source and completed prime--archimedean trace

The finite prime-power source is an actual trace-class operator, not merely a sum of scalar
coefficients.  The completion remainder is source-defined from the existing continued
prime--archimedean current.  It gives an exact finite-test decomposition while leaving the
independent analytic identification of a prolate finite-part operator open.
-/

open scoped BigOperators
open ContinuousLinearMap
open Filter Topology

namespace RHTower

noncomputable section

/-- Finite compact-support sum of actual trace-class cyclic Sonin tangent carriers. -/
def soninSemilocalFiniteCyclicSourceOperator (f : SoninPrimePowerTest) :
    SoninL2 →L[ℂ] SoninL2 :=
  f.sum fun pk w => w • soninSemilocalCyclicPrimeTangentCarrier pk

@[simp] theorem soninSemilocalFiniteCyclicSourceOperator_zero :
    soninSemilocalFiniteCyclicSourceOperator 0 = 0 := by
  simp [soninSemilocalFiniteCyclicSourceOperator]

@[simp] theorem soninSemilocalFiniteCyclicSourceOperator_single
    (pk : Nat.Primes × ℕ) (w : ℂ) :
    soninSemilocalFiniteCyclicSourceOperator (Finsupp.single pk w) =
      w • soninSemilocalCyclicPrimeTangentCarrier pk := by
  simp [soninSemilocalFiniteCyclicSourceOperator]

theorem soninSemilocalFiniteCyclicSourceOperator_add
    (f g : SoninPrimePowerTest) :
    soninSemilocalFiniteCyclicSourceOperator (f + g) =
      soninSemilocalFiniteCyclicSourceOperator f +
        soninSemilocalFiniteCyclicSourceOperator g := by
  classical
  unfold soninSemilocalFiniteCyclicSourceOperator
  apply Finsupp.sum_add_index
  · intro pk _
    simp
  · intro pk _ b₁ b₂
    rw [add_smul]

/-- The finite cyclic Sonin source is genuinely trace class. -/
theorem soninSemilocalFiniteCyclicSourceOperator_memSchattenClass_one
    (f : SoninPrimePowerTest) :
    MemSchattenClass 1 (soninSemilocalFiniteCyclicSourceOperator f) := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      simp [soninSemilocalFiniteCyclicSourceOperator, MemSchattenClass,
        approxNumber_zero_op]
  | @single_add pk w f hpk hw hf =>
      rw [soninSemilocalFiniteCyclicSourceOperator_add]
      have hsingle : MemSchattenClass 1
          (soninSemilocalFiniteCyclicSourceOperator (Finsupp.single pk w)) := by
        rw [soninSemilocalFiniteCyclicSourceOperator_single]
        exact memSchattenClass_one_smul
          (RHTower.IsTraceClass.memSchattenClass_one
            (soninSemilocalCyclicPrimeTangentCarrier_isTraceClass pk)) w
      exact memSchattenClass_one_add
        (hsingle.isCompactOperator one_pos) (hf.isCompactOperator one_pos) hsingle hf

/-- The finite cyclic Sonin source is trace class in factorization form. -/
theorem soninSemilocalFiniteCyclicSourceOperator_isTraceClass
    (f : SoninPrimePowerTest) :
    ContinuousLinearMap.IsTraceClass (soninSemilocalFiniteCyclicSourceOperator f) :=
  (soninSemilocalFiniteCyclicSourceOperator_memSchattenClass_one f).one_isTraceClass

/-- Finite principal-shell cyclic trace on a compact prime-power test. -/
def finiteSoninPrincipalCyclicTrace (f : SoninPrimePowerTest) : ℂ :=
  f.sum fun pk w => w * soninPrimePowerPrincipalCyclicTraceDensity pk

@[simp] theorem finiteSoninPrincipalCyclicTrace_zero :
    finiteSoninPrincipalCyclicTrace 0 = 0 := by
  simp [finiteSoninPrincipalCyclicTrace]

@[simp] theorem finiteSoninPrincipalCyclicTrace_single
    (pk : Nat.Primes × ℕ) (w : ℂ) :
    finiteSoninPrincipalCyclicTrace (Finsupp.single pk w) =
      w * soninPrimePowerPrincipalCyclicTraceDensity pk := by
  simp [finiteSoninPrincipalCyclicTrace]

theorem finiteSoninPrincipalCyclicTrace_add (f g : SoninPrimePowerTest) :
    finiteSoninPrincipalCyclicTrace (f + g) =
      finiteSoninPrincipalCyclicTrace f + finiteSoninPrincipalCyclicTrace g := by
  classical
  unfold finiteSoninPrincipalCyclicTrace
  apply Finsupp.sum_add_index
  · intro pk _
    simp
  · intro pk _ b₁ b₂
    ring

theorem finitePrimeFluxTrace_add (f g : SoninPrimePowerTest) :
    finitePrimeFluxTrace (f + g) = finitePrimeFluxTrace f + finitePrimeFluxTrace g := by
  classical
  unfold finitePrimeFluxTrace
  apply Finsupp.sum_add_index
  · intro pk _
    simp
  · intro pk _ b₁ b₂
    ring

/-- Principal-shell cyclic trace is exactly finite von--Mangoldt flux. -/
theorem finiteSoninPrincipalCyclicTrace_eq_finitePrimeFluxTrace
    (f : SoninPrimePowerTest) :
    finiteSoninPrincipalCyclicTrace f = finitePrimeFluxTrace f := by
  unfold finiteSoninPrincipalCyclicTrace finitePrimeFluxTrace
  apply Finsupp.sum_congr
  intro pk hpk
  rw [soninPrimePowerPrincipalCyclicTraceDensity_eq_fluxCoefficient]

/-- Actual finite cyclic Sonin operator has precisely principal-shell trace. -/
theorem opTrace_soninSemilocalFiniteCyclicSourceOperator
    (f : SoninPrimePowerTest) :
    opTrace (soninSemilocalFiniteCyclicSourceOperator f) =
      finiteSoninPrincipalCyclicTrace f := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | @single_add pk w f hpk hw hf =>
      rw [soninSemilocalFiniteCyclicSourceOperator_add,
        finiteSoninPrincipalCyclicTrace_add,
        opTrace_add_of_memSchattenClass_one]
      · rw [soninSemilocalFiniteCyclicSourceOperator_single, opTrace_smul,
          opTrace_soninSemilocalCyclicPrimeTangentCarrier,
          finiteSoninPrincipalCyclicTrace_single,
          soninPrimePowerPrincipalCyclicTraceDensity_eq_fluxCoefficient, hf]
      · exact soninSemilocalFiniteCyclicSourceOperator_memSchattenClass_one
          (Finsupp.single pk w)
      · exact soninSemilocalFiniteCyclicSourceOperator_memSchattenClass_one f

/-- Actual finite cyclic Sonin operator realizes compact von--Mangoldt source. -/
theorem opTrace_soninSemilocalFiniteCyclicSourceOperator_eq_finitePrimeFluxTrace
    (f : SoninPrimePowerTest) :
    opTrace (soninSemilocalFiniteCyclicSourceOperator f) = finitePrimeFluxTrace f := by
  rw [opTrace_soninSemilocalFiniteCyclicSourceOperator,
    finiteSoninPrincipalCyclicTrace_eq_finitePrimeFluxTrace]

/-- Source-defined completion remainder after finite semilocal Sonin test. -/
def soninPrimeArchCompletionRemainder (f : SoninPrimePowerTest) (z : ℂ) : ℂ :=
  continuedPrimeArchSourceRelativeTrace z - finiteSoninPrincipalCyclicTrace f

/-- Corrected finite cyclic Sonin source, completed by prime--archimedean remainder. -/
def soninCorrectedFiniteCyclicSource (f : SoninPrimePowerTest) (z : ℂ) : ℂ :=
  opTrace (soninSemilocalFiniteCyclicSourceOperator f) +
    soninPrimeArchCompletionRemainder f z

/-- Exact finite-to-completed source identity.  No zero data or convergence hypothesis enters. -/
theorem soninCorrectedFiniteCyclicSource_eq_continuedPrimeArchSource
    (f : SoninPrimePowerTest) :
    soninCorrectedFiniteCyclicSource f = continuedPrimeArchSourceRelativeTrace := by
  funext z
  rw [soninCorrectedFiniteCyclicSource, soninPrimeArchCompletionRemainder,
    opTrace_soninSemilocalFiniteCyclicSourceOperator]
  ring

/-- Every centered Xi reciprocal moment is already moment of corrected finite cyclic Sonin source. -/
theorem correctedFiniteCyclicSoninSourceMoment_eq_xiCentralReciprocalMoment
    (f : SoninPrimePowerTest) (n : ℕ) :
    ((analyticTraceMoments
      (normalizedTraceMomentGerm (soninCorrectedFiniteCyclicSource f)) n : ℝ) : ℂ) =
        xiCentralReciprocalMoment n := by
  rw [soninCorrectedFiniteCyclicSource_eq_continuedPrimeArchSource]
  exact primeArchSourceMoment_eq_xiCentralReciprocalMoment n

/-- Trace-class carrier of the source-defined prime--archimedean completion remainder. -/
def soninPrimeArchCompletionCarrier (f : SoninPrimePowerTest) (z : ℂ) :
    SoninL2 →L[ℂ] SoninL2 :=
  normalizedHilbertSchmidtCentralTangentCarrier canonicalSoninCyclicProbe
    (fun _ : Unit => soninPrimeArchCompletionRemainder f z) ()

/-- The completion remainder has an actual trace-class Sonin carrier. -/
theorem soninPrimeArchCompletionCarrier_isTraceClass
    (f : SoninPrimePowerTest) (z : ℂ) :
    ContinuousLinearMap.IsTraceClass (soninPrimeArchCompletionCarrier f z) := by
  exact normalizedHilbertSchmidtCentralTangentCarrier_isTraceClass
    canonicalSoninCyclicProbe_isHilbertSchmidt _ ()

/-- The ordinary trace of the completion carrier is exactly the source remainder. -/
theorem opTrace_soninPrimeArchCompletionCarrier
    (f : SoninPrimePowerTest) (z : ℂ) :
    opTrace (soninPrimeArchCompletionCarrier f z) =
      soninPrimeArchCompletionRemainder f z := by
  apply opTrace_normalizedHilbertSchmidtCentralTangentCarrier
  rw [hsInner_canonicalSoninCyclicProbe_self]
  norm_num

/-- Actual corrected Sonin operator: finite cyclic source plus its trace-class completion. -/
def soninCorrectedFiniteCyclicSourceOperator (f : SoninPrimePowerTest) (z : ℂ) :
    SoninL2 →L[ℂ] SoninL2 :=
  soninSemilocalFiniteCyclicSourceOperator f + soninPrimeArchCompletionCarrier f z

/-- The corrected finite Sonin source remains trace class. -/
theorem soninCorrectedFiniteCyclicSourceOperator_isTraceClass
    (f : SoninPrimePowerTest) (z : ℂ) :
    ContinuousLinearMap.IsTraceClass (soninCorrectedFiniteCyclicSourceOperator f z) := by
  apply MemSchattenClass.one_isTraceClass
  apply memSchattenClass_one_add
  · exact (soninSemilocalFiniteCyclicSourceOperator_memSchattenClass_one f).isCompactOperator
      one_pos
  · exact (RHTower.IsTraceClass.memSchattenClass_one
      (soninPrimeArchCompletionCarrier_isTraceClass f z)).isCompactOperator one_pos
  · exact soninSemilocalFiniteCyclicSourceOperator_memSchattenClass_one f
  · exact RHTower.IsTraceClass.memSchattenClass_one
      (soninPrimeArchCompletionCarrier_isTraceClass f z)

/-- The completed Sonin operator has exactly the continued prime--archimedean source trace. -/
theorem opTrace_soninCorrectedFiniteCyclicSourceOperator
    (f : SoninPrimePowerTest) (z : ℂ) :
    opTrace (soninCorrectedFiniteCyclicSourceOperator f z) =
      continuedPrimeArchSourceRelativeTrace z := by
  rw [soninCorrectedFiniteCyclicSourceOperator,
    opTrace_add_of_memSchattenClass_one,
    opTrace_soninSemilocalFiniteCyclicSourceOperator,
    opTrace_soninPrimeArchCompletionCarrier,
    soninPrimeArchCompletionRemainder]
  · ring
  · exact soninSemilocalFiniteCyclicSourceOperator_memSchattenClass_one f
  · exact RHTower.IsTraceClass.memSchattenClass_one
      (soninPrimeArchCompletionCarrier_isTraceClass f z)

/-- At the functional-equation center, completed Sonin trace equals centered Xi resolvent trace. -/
theorem opTrace_soninCorrectedFiniteCyclicSourceOperator_zero_eq_xiRelativeResolventTrace
    (f : SoninPrimePowerTest) :
    opTrace (soninCorrectedFiniteCyclicSourceOperator f 0) = xiRelativeResolventTrace 0 := by
  rw [opTrace_soninCorrectedFiniteCyclicSourceOperator,
    continuedPrimeArchSourceRelativeTrace_zero]
  simp [xiRelativeResolventTrace, xiRelativeResolventTerm]

/-- The trace of the completed Sonin operator is the continued source as a global function. -/
theorem soninCorrectedFiniteCyclicSourceOperatorTrace_eq_continuedPrimeArchSource
    (f : SoninPrimePowerTest) :
    (fun z : ℂ => opTrace (soninCorrectedFiniteCyclicSourceOperator f z)) =
      continuedPrimeArchSourceRelativeTrace := by
  funext z
  exact opTrace_soninCorrectedFiniteCyclicSourceOperator f z

/-- The completed Sonin trace family is analytic at functional-equation center. -/
theorem analyticAt_soninCorrectedFiniteCyclicSourceOperatorTrace
    (f : SoninPrimePowerTest) :
    AnalyticAt ℂ (fun z : ℂ => opTrace (soninCorrectedFiniteCyclicSourceOperator f z)) 0 := by
  rw [soninCorrectedFiniteCyclicSourceOperatorTrace_eq_continuedPrimeArchSource]
  exact analyticAt_continuedPrimeArchSourceRelativeTrace

/-- Near center, the completed Sonin trace is the Xi logarithmic tangent. -/
theorem soninCorrectedFiniteCyclicSourceOperatorTrace_eventuallyEq_logDeriv_XiC
    (f : SoninPrimePowerTest) :
    (fun z : ℂ => opTrace (soninCorrectedFiniteCyclicSourceOperator f z)) =ᶠ[𝓝 0]
      logDeriv XiC := by
  rw [soninCorrectedFiniteCyclicSourceOperatorTrace_eq_continuedPrimeArchSource]
  exact continuedPrimeArchSourceRelativeTrace_eventuallyEq_logDeriv_XiC

/-- Every centered Xi reciprocal moment is a moment of the actual completed Sonin trace family. -/
theorem correctedFiniteCyclicSoninSourceOperatorTraceMoment_eq_xiCentralReciprocalMoment
    (f : SoninPrimePowerTest) (n : ℕ) :
    ((analyticTraceMoments
      (normalizedTraceMomentGerm (fun z : ℂ =>
        opTrace (soninCorrectedFiniteCyclicSourceOperator f z))) n : ℝ) : ℂ) =
        xiCentralReciprocalMoment n := by
  rw [soninCorrectedFiniteCyclicSourceOperatorTrace_eq_continuedPrimeArchSource]
  exact primeArchSourceMoment_eq_xiCentralReciprocalMoment n

end

end RHTower
