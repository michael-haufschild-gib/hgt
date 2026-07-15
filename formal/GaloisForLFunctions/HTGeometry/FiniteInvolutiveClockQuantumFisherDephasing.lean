import GaloisForLFunctions.HTGeometry.FiniteClockQuantumFisher
import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockDephasing

/-!
# Quantum Fisher information equals involutive-clock dephasing energy

For a normalized stationary state, the pure-state QFI hidden by a two-reading clock is exactly
the squared clock--observable commutator.  Equivalently, it is one quarter of the squared norm
of the relational-clock double commutator.

This combines the static finite-clock QFI identity with the double-commutator dephasing law.  It
does not introduce a Hamiltonian trajectory: both values are determined by the observer's
invariant-sector projection.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- On a stationary unit state, the QFI erased by an involutive clock is exactly the squared
clock--observable commutator. -/
theorem finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
    (U X : E →L[𝕜] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hX : IsSelfAdjoint X)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U 2) (X ψ))‖)
        (‖(1 - finiteCyclicGaugeAverage U 2) (X ψ)‖ ^ 2) =
      ‖((X * U - U * X) : E →L[𝕜] E) ψ‖ ^ 2 := by
  rw [finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_observabilityVariance
    U X 2 two_ne_zero hadjoint_mul hsq hX hψnorm hψ]
  change 4 * RCLike.re
      (inner 𝕜 ψ (finiteInvolutiveObservableTwirlKadisonDefect U X ψ)) = _
  rw [re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq_of_fixed
    U X hadjoint_mul hsq hX.star_eq hψ]
  ring

/-- **QFI/dephasing value relation.**  On a stationary unit state, the hidden-clock QFI is one
quarter of the squared relational-clock double-commutator value. -/
theorem finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_quarter_doubleCommutatorNormSq
    (U X : E →L[𝕜] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hX : IsSelfAdjoint X)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U 2) (X ψ))‖)
        (‖(1 - finiteCyclicGaugeAverage U 2) (X ψ)‖ ^ 2) =
      (4 : ℝ)⁻¹ * ‖finiteInvolutiveClockDoubleCommutator U X ψ‖ ^ 2 := by
  rw [finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
    U X hadjoint_mul hsq hX hψnorm hψ,
    finiteInvolutiveClockDoubleCommutator_apply_of_fixed U X hsq hψ,
    norm_smul]
  have htwoNorm : ‖(2 : 𝕜)‖ = (2 : ℝ) := by norm_num
  rw [htwoNorm]
  ring

end

end HTGeometry
