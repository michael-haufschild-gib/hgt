import GaloisForLFunctions.RHTower.SuzukiRelativeTiltReciprocalConcavity

/-!
# Positive-resolvent parity no-go for Suzuki's two-jet gate

This file tests whether the abstract operator features of Suzuki's source can force the relative
tilt wall.  The answer is no, in a class-complete finite-dimensional sense.

For every `E,O>0` and every pair of tilts `alpha,beta`, there is an explicit four-dimensional
real model with

* a positive-definite, self-adjoint, parity-preserving resolvent `R`;
* a positive-definite self-adjoint inverse source operator `T`, with `RT=TR=I`;
* a self-adjoint position operator `X` reversing parity;
* even and odd source vectors `c,s`;

such that

`<c,Rc>=E`, `<s,Rs>=O`, `<Rc,Xs>=alpha`, `<Rs,Xc>=beta`.

Therefore positive resolvent geometry, parity, invertibility, and position self-adjointness impose
no constraint on the Suzuki relative tilt gap.  Away from parity-energy balance, even fixing the
position torque `alpha-beta` leaves the Schur numerator surjective onto all of `R`.

This does not obstruct Suzuki's concrete restricted-Weil operator.  It proves that any successful
argument must use additional arithmetic kernel structure rather than generic positive-resolvent
axioms.  No Riemann-hypothesis assumption or numerical computation occurs.
-/

namespace RHTower

noncomputable section

/-! ## Explicit positive two-dimensional blocks -/

/-- Euclidean pairing on one real two-plane. -/
def suzukiPairDot (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- Positive block with prescribed upper-left energy and off-diagonal tilt. -/
def suzukiResolventBlockApply
    (energy tilt : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (energy * v.1 + tilt * v.2,
    tilt * v.1 + (tilt ^ (2 : ℕ) / energy + 1) * v.2)

/-- Explicit inverse of `suzukiResolventBlockApply`.  Its determinant is `energy`. -/
def suzukiSourceBlockApply
    (energy tilt : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (((tilt ^ (2 : ℕ) / energy + 1) / energy) * v.1 -
      (tilt / energy) * v.2,
    -(tilt / energy) * v.1 + v.2)

/-- Completed-square identity proving positivity of the resolvent block. -/
theorem suzukiPairDot_resolventBlock_eq
    {energy : ℝ} (henergy : energy ≠ 0) (tilt : ℝ) (v : ℝ × ℝ) :
    suzukiPairDot v (suzukiResolventBlockApply energy tilt v) =
      (energy * v.1 + tilt * v.2) ^ (2 : ℕ) / energy + v.2 ^ (2 : ℕ) := by
  rw [suzukiPairDot, suzukiResolventBlockApply]
  field_simp [henergy]
  ring

/-- Completed-square identity proving positivity of the inverse source block. -/
theorem suzukiPairDot_sourceBlock_eq
    {energy : ℝ} (henergy : energy ≠ 0) (tilt : ℝ) (v : ℝ × ℝ) :
    suzukiPairDot v (suzukiSourceBlockApply energy tilt v) =
      (v.2 - tilt / energy * v.1) ^ (2 : ℕ) + v.1 ^ (2 : ℕ) / energy := by
  rw [suzukiPairDot, suzukiSourceBlockApply]
  field_simp [henergy]
  ring

theorem suzukiResolventBlock_pos
    {energy : ℝ} (henergy : 0 < energy) (tilt : ℝ)
    {v : ℝ × ℝ} (hv : v ≠ 0) :
    0 < suzukiPairDot v (suzukiResolventBlockApply energy tilt v) := by
  rw [suzukiPairDot_resolventBlock_eq henergy.ne']
  by_cases hv2 : v.2 = 0
  · have hv1 : v.1 ≠ 0 := by
      intro hv1
      apply hv
      exact Prod.ext hv1 hv2
    rw [hv2]
    norm_num
    exact div_pos (sq_pos_of_ne_zero (by
      exact mul_ne_zero henergy.ne' hv1)) henergy
  · exact add_pos_of_nonneg_of_pos
      (div_nonneg (sq_nonneg _) henergy.le)
      (sq_pos_of_ne_zero hv2)

theorem suzukiSourceBlock_pos
    {energy : ℝ} (henergy : 0 < energy) (tilt : ℝ)
    {v : ℝ × ℝ} (hv : v ≠ 0) :
    0 < suzukiPairDot v (suzukiSourceBlockApply energy tilt v) := by
  rw [suzukiPairDot_sourceBlock_eq henergy.ne']
  by_cases hv1 : v.1 = 0
  · have hv2 : v.2 ≠ 0 := by
      intro hv2
      apply hv
      exact Prod.ext hv1 hv2
    rw [hv1]
    norm_num
    exact sq_pos_of_ne_zero hv2
  · exact add_pos_of_nonneg_of_pos
      (sq_nonneg _)
      (div_pos (sq_pos_of_ne_zero hv1) henergy)

theorem suzukiResolventBlock_selfAdjoint
    (energy tilt : ℝ) (u v : ℝ × ℝ) :
    suzukiPairDot u (suzukiResolventBlockApply energy tilt v) =
      suzukiPairDot (suzukiResolventBlockApply energy tilt u) v := by
  simp only [suzukiPairDot, suzukiResolventBlockApply]
  ring

theorem suzukiSourceBlock_selfAdjoint
    (energy tilt : ℝ) (u v : ℝ × ℝ) :
    suzukiPairDot u (suzukiSourceBlockApply energy tilt v) =
      suzukiPairDot (suzukiSourceBlockApply energy tilt u) v := by
  simp only [suzukiPairDot, suzukiSourceBlockApply]
  ring

theorem suzukiResolventBlock_sourceBlock
    {energy : ℝ} (henergy : energy ≠ 0) (tilt : ℝ) (v : ℝ × ℝ) :
    suzukiResolventBlockApply energy tilt
        (suzukiSourceBlockApply energy tilt v) = v := by
  apply Prod.ext <;>
    simp only [suzukiResolventBlockApply, suzukiSourceBlockApply] <;>
    field_simp [henergy] <;>
    ring

theorem suzukiSourceBlock_resolventBlock
    {energy : ℝ} (henergy : energy ≠ 0) (tilt : ℝ) (v : ℝ × ℝ) :
    suzukiSourceBlockApply energy tilt
        (suzukiResolventBlockApply energy tilt v) = v := by
  apply Prod.ext <;>
    simp only [suzukiResolventBlockApply, suzukiSourceBlockApply] <;>
    field_simp [henergy] <;>
    ring

/-! ## Four-dimensional parity model -/

/-- Two real parity planes: even block followed by odd block. -/
abbrev SuzukiParityFourSpace := (ℝ × ℝ) × (ℝ × ℝ)

/-- Orthogonal direct-sum pairing. -/
def suzukiParityDot (u v : SuzukiParityFourSpace) : ℝ :=
  suzukiPairDot u.1 v.1 + suzukiPairDot u.2 v.2

/-- Block-diagonal parity-preserving resolvent. -/
def suzukiParityResolvent
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ)
    (v : SuzukiParityFourSpace) : SuzukiParityFourSpace :=
  (suzukiResolventBlockApply evenEnergy evenTilt v.1,
    suzukiResolventBlockApply oddEnergy oddTilt v.2)

/-- Positive inverse source operator. -/
def suzukiParitySource
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ)
    (v : SuzukiParityFourSpace) : SuzukiParityFourSpace :=
  (suzukiSourceBlockApply evenEnergy evenTilt v.1,
    suzukiSourceBlockApply oddEnergy oddTilt v.2)

/-- Parity involution. -/
def suzukiParityReflection
    (v : SuzukiParityFourSpace) : SuzukiParityFourSpace :=
  (v.1, -v.2)

/-- Coordinate swap on one two-plane. -/
def suzukiPairSwap (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, v.1)

/-- Self-adjoint position model interchanging the even and odd parity planes. -/
def suzukiParityPosition
    (v : SuzukiParityFourSpace) : SuzukiParityFourSpace :=
  (suzukiPairSwap v.2, suzukiPairSwap v.1)

/-- Canonical even source vector. -/
def suzukiParityEvenSource : SuzukiParityFourSpace :=
  ((1, 0), (0, 0))

/-- Canonical odd source vector. -/
def suzukiParityOddSource : SuzukiParityFourSpace :=
  ((0, 0), (1, 0))

theorem suzukiParityResolvent_pos
    {evenEnergy oddEnergy : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy)
    (evenTilt oddTilt : ℝ)
    {v : SuzukiParityFourSpace} (hv : v ≠ 0) :
    0 < suzukiParityDot v
      (suzukiParityResolvent evenEnergy oddEnergy evenTilt oddTilt v) := by
  change
    0 <
      suzukiPairDot v.1
          (suzukiResolventBlockApply evenEnergy evenTilt v.1) +
        suzukiPairDot v.2
          (suzukiResolventBlockApply oddEnergy oddTilt v.2)
  by_cases he : v.1 = 0
  · have ho : v.2 ≠ 0 := by
      intro ho
      apply hv
      exact Prod.ext he ho
    rw [he]
    simpa [suzukiPairDot, suzukiResolventBlockApply] using
      suzukiResolventBlock_pos hodd oddTilt ho
  · exact add_pos_of_pos_of_nonneg
      (suzukiResolventBlock_pos heven evenTilt he)
      (by
        by_cases ho : v.2 = 0
        · rw [ho]
          simp [suzukiPairDot, suzukiResolventBlockApply]
        · exact (suzukiResolventBlock_pos hodd oddTilt ho).le)

theorem suzukiParitySource_pos
    {evenEnergy oddEnergy : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy)
    (evenTilt oddTilt : ℝ)
    {v : SuzukiParityFourSpace} (hv : v ≠ 0) :
    0 < suzukiParityDot v
      (suzukiParitySource evenEnergy oddEnergy evenTilt oddTilt v) := by
  change
    0 <
      suzukiPairDot v.1
          (suzukiSourceBlockApply evenEnergy evenTilt v.1) +
        suzukiPairDot v.2
          (suzukiSourceBlockApply oddEnergy oddTilt v.2)
  by_cases he : v.1 = 0
  · have ho : v.2 ≠ 0 := by
      intro ho
      apply hv
      exact Prod.ext he ho
    rw [he]
    simpa [suzukiPairDot, suzukiSourceBlockApply] using
      suzukiSourceBlock_pos hodd oddTilt ho
  · exact add_pos_of_pos_of_nonneg
      (suzukiSourceBlock_pos heven evenTilt he)
      (by
        by_cases ho : v.2 = 0
        · rw [ho]
          simp [suzukiPairDot, suzukiSourceBlockApply]
        · exact (suzukiSourceBlock_pos hodd oddTilt ho).le)

theorem suzukiParityResolvent_selfAdjoint
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ)
    (u v : SuzukiParityFourSpace) :
    suzukiParityDot u
        (suzukiParityResolvent evenEnergy oddEnergy evenTilt oddTilt v) =
      suzukiParityDot
        (suzukiParityResolvent evenEnergy oddEnergy evenTilt oddTilt u) v := by
  change
    suzukiPairDot u.1
          (suzukiResolventBlockApply evenEnergy evenTilt v.1) +
        suzukiPairDot u.2
          (suzukiResolventBlockApply oddEnergy oddTilt v.2) =
      suzukiPairDot
          (suzukiResolventBlockApply evenEnergy evenTilt u.1) v.1 +
        suzukiPairDot
          (suzukiResolventBlockApply oddEnergy oddTilt u.2) v.2
  rw [
    suzukiResolventBlock_selfAdjoint,
    suzukiResolventBlock_selfAdjoint]

theorem suzukiParitySource_selfAdjoint
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ)
    (u v : SuzukiParityFourSpace) :
    suzukiParityDot u
        (suzukiParitySource evenEnergy oddEnergy evenTilt oddTilt v) =
      suzukiParityDot
        (suzukiParitySource evenEnergy oddEnergy evenTilt oddTilt u) v := by
  change
    suzukiPairDot u.1
          (suzukiSourceBlockApply evenEnergy evenTilt v.1) +
        suzukiPairDot u.2
          (suzukiSourceBlockApply oddEnergy oddTilt v.2) =
      suzukiPairDot
          (suzukiSourceBlockApply evenEnergy evenTilt u.1) v.1 +
        suzukiPairDot
          (suzukiSourceBlockApply oddEnergy oddTilt u.2) v.2
  rw [
    suzukiSourceBlock_selfAdjoint,
    suzukiSourceBlock_selfAdjoint]

theorem suzukiParityResolvent_source
    {evenEnergy oddEnergy : ℝ}
    (heven : evenEnergy ≠ 0) (hodd : oddEnergy ≠ 0)
    (evenTilt oddTilt : ℝ) (v : SuzukiParityFourSpace) :
    suzukiParityResolvent evenEnergy oddEnergy evenTilt oddTilt
        (suzukiParitySource evenEnergy oddEnergy evenTilt oddTilt v) = v := by
  apply Prod.ext
  · exact suzukiResolventBlock_sourceBlock heven evenTilt v.1
  · exact suzukiResolventBlock_sourceBlock hodd oddTilt v.2

theorem suzukiParitySource_resolvent
    {evenEnergy oddEnergy : ℝ}
    (heven : evenEnergy ≠ 0) (hodd : oddEnergy ≠ 0)
    (evenTilt oddTilt : ℝ) (v : SuzukiParityFourSpace) :
    suzukiParitySource evenEnergy oddEnergy evenTilt oddTilt
        (suzukiParityResolvent evenEnergy oddEnergy evenTilt oddTilt v) = v := by
  apply Prod.ext
  · exact suzukiSourceBlock_resolventBlock heven evenTilt v.1
  · exact suzukiSourceBlock_resolventBlock hodd oddTilt v.2

theorem suzukiParityResolvent_commutes_reflection
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ)
    (v : SuzukiParityFourSpace) :
    suzukiParityResolvent evenEnergy oddEnergy evenTilt oddTilt
        (suzukiParityReflection v) =
      suzukiParityReflection
        (suzukiParityResolvent evenEnergy oddEnergy evenTilt oddTilt v) := by
  rcases v with ⟨⟨v₀, v₁⟩, ⟨v₂, v₃⟩⟩
  simp [suzukiParityResolvent, suzukiParityReflection,
    suzukiResolventBlockApply]
  constructor <;> ring

theorem suzukiParityPosition_selfAdjoint
    (u v : SuzukiParityFourSpace) :
    suzukiParityDot u (suzukiParityPosition v) =
      suzukiParityDot (suzukiParityPosition u) v := by
  simp [suzukiParityDot, suzukiPairDot, suzukiParityPosition,
    suzukiPairSwap]
  ring

theorem suzukiParityPosition_anticommutes_reflection
    (v : SuzukiParityFourSpace) :
    suzukiParityPosition (suzukiParityReflection v) =
      -suzukiParityReflection (suzukiParityPosition v) := by
  apply Prod.ext <;>
    simp [suzukiParityPosition, suzukiParityReflection, suzukiPairSwap]

/-! ## Exact realization of all source coordinates -/

theorem suzukiPositiveParityResolvent_evenEnergy
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) :
    suzukiParityDot suzukiParityEvenSource
        (suzukiParityResolvent
          evenEnergy oddEnergy evenTilt oddTilt suzukiParityEvenSource) =
      evenEnergy := by
  simp [suzukiParityDot, suzukiPairDot, suzukiParityEvenSource,
    suzukiParityResolvent, suzukiResolventBlockApply]

theorem suzukiPositiveParityResolvent_oddEnergy
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) :
    suzukiParityDot suzukiParityOddSource
        (suzukiParityResolvent
          evenEnergy oddEnergy evenTilt oddTilt suzukiParityOddSource) =
      oddEnergy := by
  simp [suzukiParityDot, suzukiPairDot, suzukiParityOddSource,
    suzukiParityResolvent, suzukiResolventBlockApply]

theorem suzukiPositiveParityResolvent_evenTilt
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) :
    suzukiParityDot
        (suzukiParityResolvent
          evenEnergy oddEnergy evenTilt oddTilt suzukiParityEvenSource)
        (suzukiParityPosition suzukiParityOddSource) =
      evenTilt := by
  simp [suzukiParityDot, suzukiPairDot, suzukiParityEvenSource,
    suzukiParityOddSource, suzukiParityResolvent,
    suzukiResolventBlockApply, suzukiParityPosition, suzukiPairSwap]

theorem suzukiPositiveParityResolvent_oddTilt
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) :
    suzukiParityDot
        (suzukiParityResolvent
          evenEnergy oddEnergy evenTilt oddTilt suzukiParityOddSource)
        (suzukiParityPosition suzukiParityEvenSource) =
      oddTilt := by
  simp [suzukiParityDot, suzukiPairDot, suzukiParityEvenSource,
    suzukiParityOddSource, suzukiParityResolvent,
    suzukiResolventBlockApply, suzukiParityPosition, suzukiPairSwap]

/-- Exact package of generic operator axioms realized by the explicit model. -/
structure SuzukiPositiveParityResolventModel
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) : Prop where
  resolventPositive :
    ∀ v : SuzukiParityFourSpace, v ≠ 0 →
      0 < suzukiParityDot v
        (suzukiParityResolvent
          evenEnergy oddEnergy evenTilt oddTilt v)
  sourcePositive :
    ∀ v : SuzukiParityFourSpace, v ≠ 0 →
      0 < suzukiParityDot v
        (suzukiParitySource
          evenEnergy oddEnergy evenTilt oddTilt v)
  resolventSelfAdjoint :
    ∀ u v : SuzukiParityFourSpace,
      suzukiParityDot u
          (suzukiParityResolvent
            evenEnergy oddEnergy evenTilt oddTilt v) =
        suzukiParityDot
          (suzukiParityResolvent
            evenEnergy oddEnergy evenTilt oddTilt u) v
  sourceSelfAdjoint :
    ∀ u v : SuzukiParityFourSpace,
      suzukiParityDot u
          (suzukiParitySource
            evenEnergy oddEnergy evenTilt oddTilt v) =
        suzukiParityDot
          (suzukiParitySource
            evenEnergy oddEnergy evenTilt oddTilt u) v
  leftInverse :
    ∀ v : SuzukiParityFourSpace,
      suzukiParityResolvent
        evenEnergy oddEnergy evenTilt oddTilt
        (suzukiParitySource evenEnergy oddEnergy evenTilt oddTilt v) = v
  rightInverse :
    ∀ v : SuzukiParityFourSpace,
      suzukiParitySource
        evenEnergy oddEnergy evenTilt oddTilt
        (suzukiParityResolvent evenEnergy oddEnergy evenTilt oddTilt v) = v
  parityPreserving :
    ∀ v : SuzukiParityFourSpace,
      suzukiParityResolvent evenEnergy oddEnergy evenTilt oddTilt
          (suzukiParityReflection v) =
        suzukiParityReflection
          (suzukiParityResolvent evenEnergy oddEnergy evenTilt oddTilt v)
  positionSelfAdjoint :
    ∀ u v : SuzukiParityFourSpace,
      suzukiParityDot u (suzukiParityPosition v) =
        suzukiParityDot (suzukiParityPosition u) v
  positionParityReversing :
    ∀ v : SuzukiParityFourSpace,
      suzukiParityPosition (suzukiParityReflection v) =
        -suzukiParityReflection (suzukiParityPosition v)
  realizesEvenEnergy :
    suzukiParityDot suzukiParityEvenSource
        (suzukiParityResolvent
          evenEnergy oddEnergy evenTilt oddTilt suzukiParityEvenSource) =
      evenEnergy
  realizesOddEnergy :
    suzukiParityDot suzukiParityOddSource
        (suzukiParityResolvent
          evenEnergy oddEnergy evenTilt oddTilt suzukiParityOddSource) =
      oddEnergy
  realizesEvenTilt :
    suzukiParityDot
        (suzukiParityResolvent
          evenEnergy oddEnergy evenTilt oddTilt suzukiParityEvenSource)
        (suzukiParityPosition suzukiParityOddSource) =
      evenTilt
  realizesOddTilt :
    suzukiParityDot
        (suzukiParityResolvent
          evenEnergy oddEnergy evenTilt oddTilt suzukiParityOddSource)
        (suzukiParityPosition suzukiParityEvenSource) =
      oddTilt

/-- Every positive energy pair and every two tilts are realized by a literal positive invertible
parity resolvent model. -/
theorem suzukiPositiveParityResolventModel_of_positive
    {evenEnergy oddEnergy : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy)
    (evenTilt oddTilt : ℝ) :
    SuzukiPositiveParityResolventModel
      evenEnergy oddEnergy evenTilt oddTilt where
  resolventPositive := fun _ hv =>
    suzukiParityResolvent_pos heven hodd evenTilt oddTilt hv
  sourcePositive := fun _ hv =>
    suzukiParitySource_pos heven hodd evenTilt oddTilt hv
  resolventSelfAdjoint :=
    suzukiParityResolvent_selfAdjoint
      evenEnergy oddEnergy evenTilt oddTilt
  sourceSelfAdjoint :=
    suzukiParitySource_selfAdjoint
      evenEnergy oddEnergy evenTilt oddTilt
  leftInverse :=
    suzukiParityResolvent_source heven.ne' hodd.ne' evenTilt oddTilt
  rightInverse :=
    suzukiParitySource_resolvent heven.ne' hodd.ne' evenTilt oddTilt
  parityPreserving :=
    suzukiParityResolvent_commutes_reflection
      evenEnergy oddEnergy evenTilt oddTilt
  positionSelfAdjoint := suzukiParityPosition_selfAdjoint
  positionParityReversing := suzukiParityPosition_anticommutes_reflection
  realizesEvenEnergy :=
    suzukiPositiveParityResolvent_evenEnergy
      evenEnergy oddEnergy evenTilt oddTilt
  realizesOddEnergy :=
    suzukiPositiveParityResolvent_oddEnergy
      evenEnergy oddEnergy evenTilt oddTilt
  realizesEvenTilt :=
    suzukiPositiveParityResolvent_evenTilt
      evenEnergy oddEnergy evenTilt oddTilt
  realizesOddTilt :=
    suzukiPositiveParityResolvent_oddTilt
      evenEnergy oddEnergy evenTilt oddTilt

/-- **Class-complete positive-resolvent/parity no-go.**  Away from exact energy balance, fixing
positive energies and the position torque still permits every real Suzuki Schur numerator, even
inside positive invertible parity-resolvent models with self-adjoint parity-reversing position. -/
theorem suzukiPositiveParityResolvent_slack_surjective_at_fixed_torque
    {evenEnergy oddEnergy torque target : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy)
    (hbalance : oddEnergy ≠ evenEnergy) :
    ∃ evenTilt oddTilt : ℝ,
      evenTilt - oddTilt = torque ∧
      oddEnergy * (evenEnergy + evenTilt) -
          evenEnergy * oddTilt = target ∧
      SuzukiPositiveParityResolventModel
        evenEnergy oddEnergy evenTilt oddTilt := by
  obtain ⟨evenTilt, oddTilt, htorque, htarget⟩ :=
    suzukiParity_twoJetSlack_surjective_at_fixed_torque
      (evenEnergy := evenEnergy) (oddEnergy := oddEnergy)
      (torque := torque) (target := target) hbalance
  exact ⟨evenTilt, oddTilt, htorque, htarget,
    suzukiPositiveParityResolventModel_of_positive
      heven hodd evenTilt oddTilt⟩

end

end RHTower
