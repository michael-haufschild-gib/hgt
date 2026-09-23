import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockFidelityAsymmetry
import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockQuantumFisherDephasing

/-!
# Involutive-clock fidelity--Fisher sector factorization

The homogeneous fidelity deficit of an observed stationary state is exactly its visible-sector
mass times the quantum Fisher information erased by the two-reading clock.  This eliminates the
anti-invariant sector coordinate between the corpus's fidelity and QFI identities.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Involutive-clock fidelity--Fisher sector-factorization law.**  For an isometric
involution and a stationary unit state, every bounded observation has homogeneous clock
infidelity equal to invariant observed mass times hidden-clock QFI.  The observation need not be
self-adjoint or nonzero. -/
theorem finiteInvolutiveClock_homogeneousFidelityDeficit_eq_invariantWeight_mul_erasedQFI
    (U X : E →L[ℂ] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ (2 : ℕ) = 1)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    ‖X ψ‖ ^ (4 : ℕ) - ‖inner ℂ (X ψ) (U (X ψ))‖ ^ (2 : ℕ) =
      ‖finiteCyclicGaugeAverage U 2 (X ψ)‖ ^ (2 : ℕ) *
        pureStateQuantumFisherValue (‖ψ‖ ^ (2 : ℕ))
          (‖inner ℂ ψ ((1 - finiteCyclicGaugeAverage U 2) (X ψ))‖)
          (‖(1 - finiteCyclicGaugeAverage U 2) (X ψ)‖ ^ (2 : ℕ)) := by
  have hcomm :
      ((X * U - U * X) : E →L[ℂ] E) ψ =
        (2 : ℂ) • ((1 - finiteCyclicGaugeAverage U 2) (X ψ)) := by
    rw [_root_.sub_apply, mul_apply_eq_comp,
      mul_apply_eq_comp, hψ, _root_.sub_apply,
      one_apply_eq_self, finiteInvolutiveGaugeAverage_apply]
    norm_num
    module
  rw [finiteInvolutiveClock_homogeneousFidelityDeficit_eq_four_mul_sectorWeights
      U hadjoint_mul hsq (X ψ),
    finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
      U X hadjoint_mul hsq hψnorm hψ,
    hcomm, norm_smul]
  norm_num
  ring

end

end HTGeometry
