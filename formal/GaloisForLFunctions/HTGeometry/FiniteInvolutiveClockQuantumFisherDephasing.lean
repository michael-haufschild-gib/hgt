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

/-- On a stationary state, the complete star-Kadison energy of an involutive clock is one
quarter of the squared clock--observable commutator.  This holds for every bounded operator. -/
theorem re_inner_finiteInvolutiveObservableTwirlStarKadisonDefect_eq_quarter_commutatorNormSq_of_fixed
    (U X : E →L[𝕜] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) {ψ : E} (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect U X 2 ψ)) =
      (4 : ℝ)⁻¹ * ‖((X * U - U * X) : E →L[𝕜] E) ψ‖ ^ 2 := by
  rw [re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_erasedNormSq
    U X 2 two_ne_zero hadjoint_mul hsq hψ]
  have herased :
      (1 - finiteCyclicGaugeAverage U 2) (X ψ) =
        ((2 : 𝕜)⁻¹) • ((X * U - U * X) ψ) := by
    rw [_root_.sub_apply, one_apply_eq_self,
      ← finiteCyclicObservableTwirl_apply_of_fixed U X 2 hψ,
      ← _root_.sub_apply,
      sub_finiteInvolutiveObservableTwirl_eq_half_commutator_mul U X hsq,
      _root_.smul_apply, mul_apply_eq_comp, hψ]
  rw [herased, norm_smul, norm_inv]
  have htwoNorm : ‖(2 : 𝕜)‖ = (2 : ℝ) := by norm_num
  rw [htwoNorm]
  ring

/-- On a stationary unit state, the QFI erased by an involutive clock is exactly the squared
clock--observable commutator.  The observable need not be self-adjoint. -/
theorem finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
    (U X : E →L[𝕜] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U 2) (X ψ))‖)
        (‖(1 - finiteCyclicGaugeAverage U 2) (X ψ)‖ ^ 2) =
      ‖((X * U - U * X) : E →L[𝕜] E) ψ‖ ^ 2 := by
  rw [finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_starObservabilityEnergy
    U X 2 two_ne_zero hadjoint_mul hsq hψnorm hψ,
    re_inner_finiteInvolutiveObservableTwirlStarKadisonDefect_eq_quarter_commutatorNormSq_of_fixed
      U X hadjoint_mul hsq hψ]
  ring

/-- **QFI/dephasing value relation.**  On a stationary unit state, the hidden-clock QFI is one
quarter of the squared relational-clock double-commutator value. -/
theorem finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_quarter_doubleCommutatorNormSq
    (U X : E →L[𝕜] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U 2) (X ψ))‖)
        (‖(1 - finiteCyclicGaugeAverage U 2) (X ψ)‖ ^ 2) =
      (4 : ℝ)⁻¹ * ‖finiteInvolutiveClockDoubleCommutator U X ψ‖ ^ 2 := by
  rw [finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
    U X hadjoint_mul hsq hψnorm hψ,
    finiteInvolutiveClockDoubleCommutator_apply_of_fixed U X hsq hψ,
    norm_smul]
  have htwoNorm : ‖(2 : 𝕜)‖ = (2 : ℝ) := by norm_num
  rw [htwoNorm]
  ring

end

end HTGeometry
