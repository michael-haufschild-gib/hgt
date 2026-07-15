import GaloisForLFunctions.HTGeometry.FiniteClockResolutionVariance
import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue

/-!
# Finite-clock observability as pure-state quantum Fisher information

For a state fixed by a finite periodic clock, the component of an observable value erased by
clock averaging is automatically orthogonal to the state.  Hence its projective overlap term is
zero and its pure-state quantum Fisher value is exactly four times the static Kadison
observability variance.  No temporal trajectory, Hamiltonian generator, or independent
orthogonality hypothesis is introduced.

This is the finite-clock value relation suggested by the information-balance viewpoint of
P. Faist, M. P. Woods, V. V. Albert, J. M. Renes, J. Eisert, and J. Preskill,
*Time-energy uncertainty relation for noisy quantum metrology*, PRX Quantum 4, 040336 (2023),
arXiv:2207.13707.  Their channel theorem equates clock-time QFI lost to an environment with QFI
gained about a complementary energy parameter.  The formal result below is the static
orthogonal-projection specialization needed by the finite observer-algebra API: clock averaging
itself proves that the erased tangent has no gauge/phase component.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A stationary clock state is orthogonal to every tangent erased by the finite clock average.
This discharges the projective-overlap input in the pure-state QFI value. -/
theorem inner_finiteClockErasedTangent_eq_zero
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψ : U ψ = ψ) (y : E) :
    inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U N) y) = 0 := by
  let P : E →L[𝕜] E := finiteCyclicGaugeAverage U N
  have hPadj : P.adjoint = P := by
    simpa only [P, ContinuousLinearMap.star_eq_adjoint] using
      (finiteCyclicGaugeAverage_isSelfAdjoint_of_periodic_isometry
        U N hN hadjoint_mul hperiod).star_eq
  have hP2 : P * P = P :=
    finiteCyclicGaugeAverage_idempotent U N hN hperiod
  have hPψ : P ψ = ψ :=
    finiteCyclicGaugeAverage_apply_of_fixed U N hN hψ
  have hPcomp : P ((1 - P) y) = 0 := by
    rw [← ContinuousLinearMap.mul_apply]
    have : P * (1 - P) = 0 := by noncomm_ring [hP2]
    rw [this]
    simp
  change inner 𝕜 ψ ((1 - P) y) = 0
  calc
    inner 𝕜 ψ ((1 - P) y) = inner 𝕜 (P ψ) ((1 - P) y) := by rw [hPψ]
    _ = inner 𝕜 ψ (P.adjoint ((1 - P) y)) :=
      (P.adjoint_inner_right ψ ((1 - P) y)).symm
    _ = 0 := by rw [hPadj, hPcomp, inner_zero_right]

/-- On a unit stationary state, finite-clock Kadison observability variance is exactly the
projective Gram energy of the erased observable tangent. -/
theorem finiteClock_observabilityVariance_eq_projectiveQuantumTangentEnergy
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)) =
      projectiveGramTangentEnergy (𝕜 := 𝕜) ψ
        ((1 - finiteCyclicGaugeAverage U N) (X ψ)) := by
  rw [re_inner_finiteCyclicObservableTwirlKadisonDefect_eq_erasedNormSq
    U X N hN hadjoint_mul hperiod hX hψ]
  have horth := inner_finiteClockErasedTangent_eq_zero
    U N hN hadjoint_mul hperiod hψ (X ψ)
  unfold projectiveGramTangentEnergy
  rw [hψnorm, horth]
  simp

/-- **Finite-clock QFI/observability identity.**  The QFI of the tangent hidden by a finite
clock observer is four times the clock's Kadison observability variance.  Stationarity supplies
the vanishing overlap automatically. -/
theorem finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_observabilityVariance
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U N) (X ψ))‖)
        (‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ 2) =
      4 * RCLike.re
        (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)) := by
  rw [pureStateQuantumFisherValue,
    ← projectiveGramTangentEnergy_eq_value (𝕜 := 𝕜)]
  rw [← finiteClock_observabilityVariance_eq_projectiveQuantumTangentEnergy
    U X N hN hadjoint_mul hperiod hX hψnorm hψ]
  rw [hψnorm]
  norm_num

end

end HTGeometry
