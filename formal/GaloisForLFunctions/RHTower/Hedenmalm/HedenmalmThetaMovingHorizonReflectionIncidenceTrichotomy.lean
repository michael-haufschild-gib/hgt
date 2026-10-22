import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMovingHorizonCompletedResponseWeld

/-!
# Reflection-incidence trichotomy for the moving-horizon Route P carrier

The physical moving-horizon half-density is reflection-odd, whereas its completed quadratic
budget is reflection-even.  This file inserts every constant two-copy incidence before quadratic
scalarization and classifies the result exactly.

For copy coefficients `α, β`, the full same-copy and mixed-copy budget is
`(α - β)²` times the original Route P packet energy.  Consequently the symmetric channel
annihilates every divisor copy, not merely neutral copies, while every nonsymmetric channel retains
the full RH-equivalent Ward obstruction up to a fixed positive scalar.  No constant reflection
incidence can select the critical-line grade.
-/

open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Cross-copy completed response between a divisor copy and its functional-equation reflection. -/
def thetaPhysicalEndpointCompletedResponseMixedReflectionPairing
    (P : Finset Nat.Primes) (q : XiZeroCopy) : ℝ :=
  ∑ p ∈ P, ∑ r ∈ P,
    xiPhysicalEndpointCompletedBalancedCoupling P p r *
      thetaPhysicalEndpointNormalizedHalfDensity p q *
      thetaPhysicalEndpointNormalizedHalfDensity r (xiZeroCopyReflectEquiv q)

/-- Cross-copy signed Dirichlet term between a copy and its reflection. -/
def thetaPhysicalEndpointCompletedResponseMixedReflectionDirichletEnergy
    (P : Finset Nat.Primes) (q : XiZeroCopy) : ℝ :=
  ∑ p ∈ P, ∑ r ∈ P,
    xiPhysicalEndpointCompletedBalancedCoupling P p r *
      (thetaPhysicalEndpointNormalizedHalfDensity p q -
        thetaPhysicalEndpointNormalizedHalfDensity r q) *
      (thetaPhysicalEndpointNormalizedHalfDensity p (xiZeroCopyReflectEquiv q) -
        thetaPhysicalEndpointNormalizedHalfDensity r (xiZeroCopyReflectEquiv q))

/-- Full completed mixed-copy budget. -/
def thetaPhysicalEndpointCompletedResponseMixedReflectionBudget
    (P : Finset Nat.Primes) (q : XiZeroCopy) : ℝ :=
  thetaPhysicalEndpointCompletedResponseMixedReflectionPairing P q +
    (1 / 2 : ℝ) *
      thetaPhysicalEndpointCompletedResponseMixedReflectionDirichletEnergy P q

/-- Reflection reverses the complete mixed budget, including its Dirichlet correction. -/
theorem thetaPhysicalEndpointCompletedResponseMixedReflectionBudget_eq_neg_packetEnergy
    (P : Finset Nat.Primes) (q : XiZeroCopy) :
    thetaPhysicalEndpointCompletedResponseMixedReflectionBudget P q =
      -thetaMobiusPrimeNormalProfilePacketEnergy q P := by
  rw [thetaPhysicalEndpointCompletedResponseMixedReflectionBudget,
    thetaPhysicalEndpointCompletedResponseMixedReflectionPairing,
    thetaPhysicalEndpointCompletedResponseMixedReflectionDirichletEnergy,
    thetaPhysicalEndpointCompletedResponse_mixedReflection_eq_neg,
    thetaPhysicalEndpointCompletedResponse_mixedReflectionDirichlet_eq_neg,
    thetaMobiusPrimeNormalProfilePacketEnergy_eq_completedResponseBudget]
  ring

/-- Completed quadratic budget after inserting arbitrary constant coefficients on the copy and
reflected-copy channels, including both ordered mixed incidences. -/
def thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget
    (P : Finset Nat.Primes) (q : XiZeroCopy) (α β : ℝ) : ℝ :=
  α ^ (2 : ℕ) *
      (thetaPhysicalEndpointCompletedResponsePairing P q +
        (1 / 2 : ℝ) * thetaPhysicalEndpointCompletedResponseDirichletEnergy P q) +
    β ^ (2 : ℕ) *
      (thetaPhysicalEndpointCompletedResponsePairing P (xiZeroCopyReflectEquiv q) +
        (1 / 2 : ℝ) * thetaPhysicalEndpointCompletedResponseDirichletEnergy P
          (xiZeroCopyReflectEquiv q)) +
    2 * α * β * thetaPhysicalEndpointCompletedResponseMixedReflectionBudget P q

/-- **P-G33 reflection-incidence classification.** Every constant two-copy incidence sees only
the antisymmetric copy-space coordinate. -/
theorem thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget_eq_sub_sq_mul_packetEnergy
    (P : Finset Nat.Primes) (q : XiZeroCopy) (α β : ℝ) :
    thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget P q α β =
      (α - β) ^ (2 : ℕ) * thetaMobiusPrimeNormalProfilePacketEnergy q P := by
  rw [thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget,
    thetaPhysicalEndpointCompletedResponsePairing_copyReflect,
    thetaPhysicalEndpointCompletedResponseDirichletEnergy_copyReflect,
    thetaPhysicalEndpointCompletedResponseMixedReflectionBudget_eq_neg_packetEnergy,
    ← thetaMobiusPrimeNormalProfilePacketEnergy_eq_completedResponseBudget]
  ring

/-- Symmetric reflection incidence annihilates every fibre and every prime packet. -/
theorem thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget_self_eq_zero
    (P : Finset Nat.Primes) (q : XiZeroCopy) (α : ℝ) :
    thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget P q α α = 0 := by
  rw [thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget_eq_sub_sq_mul_packetEnergy]
  ring

/-- Antisymmetric reflection incidence amplifies the original packet by `4 α²`. -/
theorem thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget_neg_eq_four_mul_sq
    (P : Finset Nat.Primes) (q : XiZeroCopy) (α : ℝ) :
    thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget P q α (-α) =
      4 * α ^ (2 : ℕ) * thetaMobiusPrimeNormalProfilePacketEnergy q P := by
  rw [thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget_eq_sub_sq_mul_packetEnergy]
  ring

/-- Finite-packet Ward admission after fixed two-copy reflection incidence. -/
def ThetaPhysicalEndpointCompletedResponseCopyIncidenceWardBoundAt
    (α β : ℝ) (q : XiZeroCopy) : Prop :=
  ∃ C : ℝ, ∀ P : Finset Nat.Primes,
    thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget P q α β ≤ C

/-- Every nonsymmetric fixed incidence retains exactly the original pointwise Ward contract. -/
theorem thetaPhysicalEndpointCompletedResponseCopyIncidenceWardBoundAt_iff
    {α β : ℝ} (hαβ : α ≠ β) (q : XiZeroCopy) :
    ThetaPhysicalEndpointCompletedResponseCopyIncidenceWardBoundAt α β q ↔
      ThetaMobiusPrimeNormalWardBoundAt q := by
  have hk : 0 < (α - β) ^ (2 : ℕ) := sq_pos_of_ne_zero (sub_ne_zero.mpr hαβ)
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C / (α - β) ^ (2 : ℕ), fun P => ?_⟩
    apply (le_div_iff₀ hk).2
    calc
      thetaMobiusPrimeNormalProfilePacketEnergy q P * (α - β) ^ (2 : ℕ) =
          thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget P q α β := by
            rw [thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget_eq_sub_sq_mul_packetEnergy]
            ring
      _ ≤ C := hC P
  · rintro ⟨C, hC⟩
    refine ⟨(α - β) ^ (2 : ℕ) * C, fun P => ?_⟩
    rw [thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget_eq_sub_sq_mul_packetEnergy]
    exact mul_le_mul_of_nonneg_left (hC P) hk.le

/-- Global Ward admission after fixed two-copy reflection incidence. -/
def ThetaPhysicalEndpointCompletedResponseCopyIncidenceWardBound
    (α β : ℝ) : Prop :=
  ∀ q : XiZeroCopy,
    ThetaPhysicalEndpointCompletedResponseCopyIncidenceWardBoundAt α β q

/-- **Constant-incidence no-go.** Every nonsymmetric fixed reflection incidence is RH-equivalent;
the sole symmetric incidence is identically blind. -/
theorem thetaPhysicalEndpointCompletedResponseCopyIncidenceWardBound_iff_riemannHypothesis
    {α β : ℝ} (hαβ : α ≠ β) :
    ThetaPhysicalEndpointCompletedResponseCopyIncidenceWardBound α β ↔
      RiemannHypothesis := by
  rw [← thetaMobiusPrimeNormalWardBound_iff_riemannHypothesis]
  exact forall_congr' (thetaPhysicalEndpointCompletedResponseCopyIncidenceWardBoundAt_iff hαβ)

end

end RHTower.HedenmalmThetaSource
