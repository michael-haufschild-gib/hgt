import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry
import GaloisForLFunctions.HTGeometry.FiniteClockQuantumFisher
import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockQuantumFisherDephasing

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
      ‖A.erasedTangent‖ ^ (2 : ℕ) / (2 * (Q : ℝ)) :=
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
  _root_.HTGeometry.pureStateQuantumFisherValue (‖A.state‖ ^ (2 : ℕ))
    (‖inner ℂ A.state A.erasedTangent‖) (‖A.erasedTangent‖ ^ (2 : ℕ))

/-- Clock-erased QFI is exactly four times squared tangent norm. -/
theorem GreedyBumpFiniteClockData.erasedQuantumFisher_eq_four_mul_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpFiniteClockData E) :
    A.erasedQuantumFisher = 4 * ‖A.erasedTangent‖ ^ (2 : ℕ) := by
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

/-! ## Two-reading clocks and commutator energy -/

/-- Admissible involutive clock with stationary unit state. -/
structure GreedyBumpInvolutiveClockData (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  evolution : E →L[ℂ] E
  observable : E →L[ℂ] E
  isometry : evolution.adjoint * evolution = 1
  involutive : evolution ^ (2 : ℕ) = 1
  state : E
  state_norm : ‖state‖ = 1
  state_fixed : evolution state = state

/-- An involutive clock is a finite clock of period two. -/
def GreedyBumpInvolutiveClockData.toFiniteClock
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpInvolutiveClockData E) : GreedyBumpFiniteClockData E where
  evolution := A.evolution
  observable := A.observable
  period := 2
  period_ne := two_ne_zero
  isometry := A.isometry
  periodic := A.involutive
  state := A.state
  state_norm := A.state_norm
  state_fixed := A.state_fixed

/-- For a two-reading clock, optimized profile gain is commutator energy divided by `8Q`. -/
theorem greedyBump_involutiveClock_profileGain_eq_commutator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpInvolutiveClockData E) (Q : PositiveSignal) :
    greedyBumpProfile Q A.toFiniteClock.erasedTangent
        (greedyBumpDisplacement Q A.toFiniteClock.erasedTangent) =
      ‖((A.observable * A.evolution - A.evolution * A.observable) :
        E →L[ℂ] E) A.state‖ ^ (2 : ℕ) / (8 * (Q : ℝ)) := by
  rw [greedyBump_finiteClock_profileGain_eq_qfi]
  unfold GreedyBumpFiniteClockData.erasedQuantumFisher
    GreedyBumpFiniteClockData.erasedTangent
    GreedyBumpInvolutiveClockData.toFiniteClock
  rw [_root_.HTGeometry.finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
    A.evolution A.observable A.isometry A.involutive A.state_norm A.state_fixed]

/-- Equivalent dephasing form: double-commutator energy is paid at rate `1/(32Q)`. -/
theorem greedyBump_involutiveClock_profileGain_eq_doubleCommutator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : GreedyBumpInvolutiveClockData E) (Q : PositiveSignal) :
    greedyBumpProfile Q A.toFiniteClock.erasedTangent
        (greedyBumpDisplacement Q A.toFiniteClock.erasedTangent) =
      ‖_root_.HTGeometry.finiteInvolutiveClockDoubleCommutator
        A.evolution A.observable A.state‖ ^ (2 : ℕ) / (32 * (Q : ℝ)) := by
  rw [greedyBump_finiteClock_profileGain_eq_qfi]
  unfold GreedyBumpFiniteClockData.erasedQuantumFisher
    GreedyBumpFiniteClockData.erasedTangent
    GreedyBumpInvolutiveClockData.toFiniteClock
  rw [_root_.HTGeometry.finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_quarter_doubleCommutatorNormSq
    A.evolution A.observable A.isometry A.involutive A.state_norm A.state_fixed]
  ring

end

end GaloisForLFunctions.HTGeometry
