import GaloisForLFunctions.HTGeometry.RydbergProjectorDephasing
import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockDephasing
noncomputable section

namespace HTGeometry

variable {k E : Type*} [RCLike k]
  [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Projective dephasing by an involutive clock's invariant-sector projection is exactly
minus one eighth of the clock double commutator. -/
theorem projectorDephasingGenerator_finiteInvolutiveGaugeAverage_eq
    (U X : E →L[k] E) (hsq : U ^ (2 : ℕ) = 1) :
    projectorDephasingGenerator (k := k) (finiteCyclicGaugeAverage U 2) X =
      -(8 : k)⁻¹ • finiteInvolutiveClockDoubleCommutator U X := by
  rw [projectorDephasingGenerator_eq_half_pinching_sub (k := k)
      (finiteCyclicGaugeAverage U 2) X
      (finiteInvolutiveGaugeAverage_isIdempotentElem U hsq),
    twoOutcomePinching_finiteInvolutiveGaugeAverage_eq_observableTwirl U X hsq,
    finiteInvolutiveClockDoubleCommutator_eq_four_smul_disturbance U X hsq]
  module

omit [CompleteSpace E] in
/-- The clock-projector dissipator has exactly the clock commutant as kernel. -/
theorem projectorDephasingGenerator_finiteInvolutiveGaugeAverage_eq_zero_iff
    (U X : E →L[k] E) (hsq : U ^ (2 : ℕ) = 1) :
    projectorDephasingGenerator (k := k) (finiteCyclicGaugeAverage U 2) X = 0 ↔
      U * X = X * U := by
  rw [projectorDephasingGenerator_finiteInvolutiveGaugeAverage_eq U X hsq]
  constructor
  · intro h
    have hdouble : finiteInvolutiveClockDoubleCommutator U X = 0 := by
      exact (smul_eq_zero.mp h).resolve_left (by norm_num)
    exact (finiteInvolutiveClockDoubleCommutator_eq_zero_iff_commutes U X hsq).mp hdouble
  · intro h
    rw [(finiteInvolutiveClockDoubleCommutator_eq_zero_iff_commutes U X hsq).mpr h,
      smul_zero]

end HTGeometry
