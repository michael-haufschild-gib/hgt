import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry
import GaloisForLFunctions.HTGeometry.FiniteClockQuantumFisher

/-!
# Greedy-bump profiling of finite-clock hidden directions

A finite periodic clock erases an observable tangent orthogonal to every stationary state.  This
module packages clock admissibility as data and applies Propositions 5.1 and 6.1 of
arXiv:2609.03581.  The optimized local profile gain is identified exactly with one eighth of the
erased pure-state quantum Fisher information per unit signal.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Admissible complex finite clock, stationary unit state, and observed operator. -/
structure GreedyBumpFiniteClockData (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  evolution : E →L[ℂ] E
  observable : E →L[ℂ] E
  period : ℕ
  period_ne : period ≠ 0
  isometry : evolution.adjoint * evolution = 1
  periodic : evolution ^ period = 1
  state : E
  state_norm : ‖state‖ = 1
  state_fixed : evolution state = state

/-- Observable tangent removed by finite-clock averaging. -/
def GreedyBumpFiniteClockData.erasedTangent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpFiniteClockData E) : E :=
  (1 - _root_.HTGeometry.finiteCyclicGaugeAverage A.evolution A.period)
    (A.observable A.state)

/-- Finite-clock averaging closes the paper's tangent-orthogonality requirement. -/
theorem GreedyBumpFiniteClockData.erasedTangent_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpFiniteClockData E) :
    inner ℂ A.state A.erasedTangent = 0 :=
  _root_.HTGeometry.inner_finiteClockErasedTangent_eq_zero
    A.evolution A.period A.period_ne A.isometry A.periodic A.state_fixed
      (A.observable A.state)

/-- Finite-clock state and erased tangent as a matched-filter direction. -/
def GreedyBumpFiniteClockData.templateTangent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpFiniteClockData E) : OrthogonalComplexTemplateTangent E where
  template := A.state
  tangent := A.erasedTangent
  orthogonal := A.erasedTangent_orthogonal

/-- Proposition 5.1 gives the exact optimized gain of every erased clock direction. -/
theorem greedyBump_finiteClock_profileGain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpFiniteClockData E) (Q : PositiveSignal) :
    greedyBumpProfile Q A.erasedTangent
        (greedyBumpDisplacement Q A.erasedTangent) =
      ‖A.erasedTangent‖ ^ 2 / (2 * (Q : ℝ)) :=
  greedyBumpProfile_at_displacement Q A.erasedTangent

/-- Proposition 6.1: subtracting any matched amplitude leaves the erased-direction score intact. -/
theorem greedyBump_finiteClock_matchedFilterDerivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpFiniteClockData E) (amplitude : ℝ) (data : E) :
    @inner ℂ E _ data A.erasedTangent =
      @inner ℂ E _ (greedyBumpComplexResidual amplitude data A.state) A.erasedTangent :=
  greedyBump_complexMatchedFilter_derivative_bridge A.templateTangent amplitude data

/-- Pure-state QFI of the clock-erased tangent. -/
def GreedyBumpFiniteClockData.erasedQuantumFisher
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpFiniteClockData E) : ℝ :=
  _root_.HTGeometry.pureStateQuantumFisherValue (‖A.state‖ ^ 2)
    (‖inner ℂ A.state A.erasedTangent‖) (‖A.erasedTangent‖ ^ 2)

/-- Clock-erased QFI is exactly four times squared tangent norm. -/
theorem GreedyBumpFiniteClockData.erasedQuantumFisher_eq_four_mul_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpFiniteClockData E) :
    A.erasedQuantumFisher = 4 * ‖A.erasedTangent‖ ^ 2 := by
  rw [GreedyBumpFiniteClockData.erasedQuantumFisher,
    _root_.HTGeometry.pureStateQuantumFisherValue,
    _root_.HTGeometry.projectiveQuantumTangentValue,
    A.state_norm, A.erasedTangent_orthogonal]
  norm_num

/-- New bridge: optimized clock-hidden profile gain is erased QFI divided by `8Q`. -/
theorem greedyBump_finiteClock_profileGain_eq_qfi
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpFiniteClockData E) (Q : PositiveSignal) :
    greedyBumpProfile Q A.erasedTangent
        (greedyBumpDisplacement Q A.erasedTangent) =
      A.erasedQuantumFisher / (8 * (Q : ℝ)) := by
  rw [greedyBump_finiteClock_profileGain,
    A.erasedQuantumFisher_eq_four_mul_norm_sq]
  ring

end

end GaloisForLFunctions.HTGeometry
