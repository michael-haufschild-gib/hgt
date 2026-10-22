import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMovingHorizonWardCarrier
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPhysicalEndpointCompletedResponseWardBridge

/-!
# Moving-horizon theta carrier in the completed physical response

The forced normalization in the completed-response Ward bridge acts on the same coefficient,
prime by prime, as the physical moving-horizon theta construction.  This file records that literal
identification and audits functional-equation folding at the resulting non-diagonal source.

Reflection annihilates the two normalized carrier vectors labelwise, but every quadratic
completed-response term is reflection-even.  Cancellation is recovered only after inserting the
missing mixed-copy terms.  Thus a reflected direct sum cannot be the source producer; a successful
law must generate a coefficient-faithful cross-copy incidence before quadratic scalarization.
-/

open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- The literal physical Ward coefficient is the oriented moving-horizon boundary atom plus its
same-carrier twisted residual. -/
theorem thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_movingHorizonCarrier
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q =
      thetaWardHorizontalOrientation q * thetaMovingHorizonUniversalAmplitude p +
        thetaWardMovingHorizonResidual p q := by
  rw [thetaWardMovingHorizonResidual]
  ring

/-- P-G25's forced physical-endpoint normalization is exactly the normalized physical theta
moving-horizon carrier, without changing a prime or divisor label. -/
theorem thetaPhysicalEndpointNormalizedHalfDensity_eq_movingHorizonCarrier
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointNormalizedHalfDensity p q =
      Real.sqrt ((p : ℝ) / Real.log (p : ℝ)) *
        (thetaWardHorizontalOrientation q * thetaMovingHorizonUniversalAmplitude p +
          thetaWardMovingHorizonResidual p q) := by
  rw [thetaPhysicalEndpointNormalizedHalfDensity,
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_movingHorizonCarrier]

/-- Functional-equation reflection negates the complete physical half-density, including its
twisted residual, not only the universal principal term. -/
theorem thetaMobiusPrimeNormalProfileHalfDensityAmplitude_copyReflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude p
        (xiZeroCopyReflectEquiv q) =
      -thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q := by
  rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude,
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude,
    thetaMobiusPrimeNormalReflectionProfile_eq,
    thetaMobiusPrimeNormalReflectionProfile_eq,
    primeDepthBVWoldXiCenteredRate_copyReflect, abs_neg]
  simp only [neg_neg]
  ring

/-- The completed-response normalization retains the same exact reflection orientation. -/
theorem thetaPhysicalEndpointNormalizedHalfDensity_copyReflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointNormalizedHalfDensity p
        (xiZeroCopyReflectEquiv q) =
      -thetaPhysicalEndpointNormalizedHalfDensity p q := by
  rw [thetaPhysicalEndpointNormalizedHalfDensity,
    thetaPhysicalEndpointNormalizedHalfDensity,
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude_copyReflect]
  ring

/-- Both retained orientations annihilate labelwise before the completed response is paired. -/
theorem thetaPhysicalEndpointNormalizedHalfDensity_reflection_add_eq_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointNormalizedHalfDensity p q +
      thetaPhysicalEndpointNormalizedHalfDensity p
        (xiZeroCopyReflectEquiv q) = 0 := by
  rw [thetaPhysicalEndpointNormalizedHalfDensity_copyReflect]
  ring

/-- The completed non-diagonal response pairing is nevertheless reflection-even. -/
theorem thetaPhysicalEndpointCompletedResponsePairing_copyReflect
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointCompletedResponsePairing P
        (xiZeroCopyReflectEquiv q) =
      thetaPhysicalEndpointCompletedResponsePairing P q := by
  unfold thetaPhysicalEndpointCompletedResponsePairing
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro r hr
  rw [thetaPhysicalEndpointNormalizedHalfDensity_copyReflect,
    thetaPhysicalEndpointNormalizedHalfDensity_copyReflect]
  ring

/-- The signed prime-ratio Dirichlet term is also reflection-even. -/
theorem thetaPhysicalEndpointCompletedResponseDirichletEnergy_copyReflect
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointCompletedResponseDirichletEnergy P
        (xiZeroCopyReflectEquiv q) =
      thetaPhysicalEndpointCompletedResponseDirichletEnergy P q := by
  unfold thetaPhysicalEndpointCompletedResponseDirichletEnergy
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro r hr
  rw [thetaPhysicalEndpointNormalizedHalfDensity_copyReflect,
    thetaPhysicalEndpointNormalizedHalfDensity_copyReflect]
  ring

/-- The mixed reflected response is exactly the negative of the same-copy response.  This is the
cross-copy term absent from a reflected direct sum. -/
theorem thetaPhysicalEndpointCompletedResponse_mixedReflection_eq_neg
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    (∑ p ∈ P, ∑ r ∈ P,
      xiPhysicalEndpointCompletedBalancedCoupling P p r *
        thetaPhysicalEndpointNormalizedHalfDensity p q *
        thetaPhysicalEndpointNormalizedHalfDensity r
          (xiZeroCopyReflectEquiv q)) =
      -thetaPhysicalEndpointCompletedResponsePairing P q := by
  rw [thetaPhysicalEndpointCompletedResponsePairing]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [thetaPhysicalEndpointNormalizedHalfDensity_copyReflect]
  ring

/-- The mixed reflected Dirichlet term is likewise the negative of the same-copy term. -/
theorem thetaPhysicalEndpointCompletedResponse_mixedReflectionDirichlet_eq_neg
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    (∑ p ∈ P, ∑ r ∈ P,
      xiPhysicalEndpointCompletedBalancedCoupling P p r *
        (thetaPhysicalEndpointNormalizedHalfDensity p q -
          thetaPhysicalEndpointNormalizedHalfDensity r q) *
        (thetaPhysicalEndpointNormalizedHalfDensity p
            (xiZeroCopyReflectEquiv q) -
          thetaPhysicalEndpointNormalizedHalfDensity r
            (xiZeroCopyReflectEquiv q))) =
      -thetaPhysicalEndpointCompletedResponseDirichletEnergy P q := by
  rw [thetaPhysicalEndpointCompletedResponseDirichletEnergy]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [thetaPhysicalEndpointNormalizedHalfDensity_copyReflect,
    thetaPhysicalEndpointNormalizedHalfDensity_copyReflect]
  ring

/-- **Quadratic folding obstruction.**  Source reflection cancels the vector but doubles the
separate completed-response budget.  Hence reflection can neutralize Route P only through the
mixed-copy incidence above, not through direct-sum aggregation. -/
theorem thetaPhysicalEndpointCompletedResponse_reflectedBudgets_eq_two_mul
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    (thetaPhysicalEndpointCompletedResponsePairing P q +
        (1 / 2 : ℝ) * thetaPhysicalEndpointCompletedResponseDirichletEnergy P q) +
      (thetaPhysicalEndpointCompletedResponsePairing P (xiZeroCopyReflectEquiv q) +
        (1 / 2 : ℝ) * thetaPhysicalEndpointCompletedResponseDirichletEnergy P
          (xiZeroCopyReflectEquiv q)) =
      2 * thetaMobiusPrimeNormalProfilePacketEnergy q P := by
  rw [thetaPhysicalEndpointCompletedResponsePairing_copyReflect,
    thetaPhysicalEndpointCompletedResponseDirichletEnergy_copyReflect,
    ← thetaMobiusPrimeNormalProfilePacketEnergy_eq_completedResponseBudget]
  ring

end

end RHTower.HedenmalmThetaSource
