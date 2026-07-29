import GaloisForLFunctions.HTGeometry.FiniteClockStarKadison
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
    rw [← mul_apply_eq_comp]
    have : P * (1 - P) = 0 := by noncomm_ring [hP2]
    rw [this]
    simp
  change inner 𝕜 ψ ((1 - P) y) = 0
  calc
    inner 𝕜 ψ ((1 - P) y) = inner 𝕜 (P ψ) ((1 - P) y) := by rw [hPψ]
    _ = inner 𝕜 ψ (P.adjoint ((1 - P) y)) :=
      (P.adjoint_inner_right ψ ((1 - P) y)).symm
    _ = 0 := by rw [hPadj, hPcomp, inner_zero_right]

/-- On a unit stationary state, arbitrary-operator star-Kadison observability energy is exactly
the projective Gram energy of the erased observable tangent. -/
theorem finiteClock_starObservabilityEnergy_eq_projectiveQuantumTangentEnergy
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect U X N ψ)) =
      projectiveGramTangentEnergy (𝕜 := 𝕜) ψ
        ((1 - finiteCyclicGaugeAverage U N) (X ψ)) := by
  rw [re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_erasedNormSq
    U X N hN hadjoint_mul hperiod hψ]
  have horth := inner_finiteClockErasedTangent_eq_zero
    U N hN hadjoint_mul hperiod hψ (X ψ)
  unfold projectiveGramTangentEnergy
  rw [hψnorm, horth, norm_zero]
  ring

/-- On a unit stationary state, finite-clock squared-Kadison observability variance is exactly
the projective Gram energy of the erased self-adjoint observable tangent. -/
theorem finiteClock_observabilityVariance_eq_projectiveQuantumTangentEnergy
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hX : IsSelfAdjoint X) {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    RCLike.re
        (inner 𝕜 ψ (finiteCyclicObservableTwirlKadisonDefect U X N ψ)) =
      projectiveGramTangentEnergy (𝕜 := 𝕜) ψ
        ((1 - finiteCyclicGaugeAverage U N) (X ψ)) := by
  rw [← finiteCyclicObservableTwirlStarKadisonDefect_eq_of_isSelfAdjoint
    U X N hN hadjoint_mul hperiod hX]
  exact finiteClock_starObservabilityEnergy_eq_projectiveQuantumTangentEnergy
    U X N hN hadjoint_mul hperiod hψnorm hψ

/-- **Arbitrary-operator finite-clock QFI/star-observability identity.**  The QFI of the tangent
hidden by a finite clock observer is four times its star-Kadison observability energy.  No
self-adjointness premise on the observed operator is required. -/
theorem finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_starObservabilityEnergy
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U N) (X ψ))‖)
        (‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ 2) =
      4 * RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect U X N ψ)) := by
  rw [pureStateQuantumFisherValue,
    ← projectiveGramTangentEnergy_eq_value (𝕜 := 𝕜)]
  rw [← finiteClock_starObservabilityEnergy_eq_projectiveQuantumTangentEnergy
    U X N hN hadjoint_mul hperiod hψnorm hψ]
  rw [hψnorm]
  norm_num

/-- **Arbitrary-operator law of total finite-clock QFI.**  Refining a power subclock to the full
clock adds exactly four times the squared norm of the newly erased resolution layer.  No
self-adjointness premise on the observed operator is required. -/
theorem finiteClockResolution_erasedPureStateQuantumFisherValue
    (U X : E →L[𝕜] E) (d M : ℕ) (hd : d ≠ 0) (hM : M ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ (d * M) = 1)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U (d * M)) (X ψ))‖)
        (‖(1 - finiteCyclicGaugeAverage U (d * M)) (X ψ)‖ ^ 2) =
      pureStateQuantumFisherValue (‖ψ‖ ^ 2)
          (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage (U ^ d) M) (X ψ))‖)
          (‖(1 - finiteCyclicGaugeAverage (U ^ d) M) (X ψ)‖ ^ 2) +
        4 * ‖(finiteCyclicGaugeAverage (U ^ d) M -
          finiteCyclicGaugeAverage U (d * M)) (X ψ)‖ ^ 2 := by
  have hfullN : d * M ≠ 0 := Nat.mul_ne_zero hd hM
  have hsubadjoint : (U ^ d).adjoint * U ^ d = 1 :=
    adjoint_pow_mul_pow_eq_one_of_adjoint_mul_self U d hadjoint_mul
  have hsubperiod : (U ^ d) ^ M = 1 := by
    rw [← pow_mul]
    exact hperiod
  have hsubψ : (U ^ d) ψ = ψ :=
    pow_apply_eq_self_of_apply_eq_self U hψ d
  rw [finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_starObservabilityEnergy
      U X (d * M) hfullN hadjoint_mul hperiod hψnorm hψ,
    finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_starObservabilityEnergy
      (U ^ d) X M hM hsubadjoint hsubperiod hψnorm hsubψ,
    finiteClockResolution_starObservabilityVariance
      U X d M hd hM hadjoint_mul hperiod hψ]
  ring

/-- **Finite-clock QFI physicality detector.**  For an arbitrary bounded operator, zero erased QFI
is equivalent to preservation of the finite-clock physical constraint on the observed state. -/
theorem finiteClock_erasedPureStateQuantumFisherValue_eq_zero_iff_physical
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U N) (X ψ))‖)
        (‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ 2) = 0 ↔
      GaloisForLFunctions.PhysicalState (U - 1).toLinearMap (X ψ) := by
  rw [finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_starObservabilityEnergy
    U X N hN hadjoint_mul hperiod hψnorm hψ]
  norm_num
  exact re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_physical
    U X N hN hadjoint_mul hperiod hψ

/-- Zero erased finite-clock QFI is equivalently the statewise clock--observable commutator
condition, for arbitrary bounded operators and arbitrary finite periods. -/
theorem finiteClock_erasedPureStateQuantumFisherValue_eq_zero_iff_commutator
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ) :
    pureStateQuantumFisherValue (‖ψ‖ ^ 2)
        (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U N) (X ψ))‖)
        (‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ 2) = 0 ↔
      (U * X - X * U) ψ = 0 := by
  rw [finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_starObservabilityEnergy
    U X N hN hadjoint_mul hperiod hψnorm hψ]
  norm_num
  exact re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_zero_iff_commutator
    U X N hN hadjoint_mul hperiod hψ

/-- Zero erased finite-clock QFI supplies every positive-master Ward identity for the observed
state, with no self-adjointness premise on the observed operator. -/
theorem finiteClock_zeroQFI_WardValue_eq_zero
    (U X A : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) (hψ : U ψ = ψ)
    (hzero : pureStateQuantumFisherValue (‖ψ‖ ^ 2)
      (‖inner 𝕜 ψ ((1 - finiteCyclicGaugeAverage U N) (X ψ))‖)
      (‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ 2) = 0) :
    inner 𝕜 (X ψ) (quantumMasterConstraint (U - 1) (A (X ψ))) = 0 := by
  apply quantumMasterConstraint_WardValue_eq_zero (U - 1) A
  exact (finiteClock_erasedPureStateQuantumFisherValue_eq_zero_iff_physical
    U X N hN hadjoint_mul hperiod hψnorm hψ).mp hzero

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
  rw [← finiteCyclicObservableTwirlStarKadisonDefect_eq_of_isSelfAdjoint
    U X N hN hadjoint_mul hperiod hX]
  exact finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_starObservabilityEnergy
    U X N hN hadjoint_mul hperiod hψnorm hψ

end

end HTGeometry
