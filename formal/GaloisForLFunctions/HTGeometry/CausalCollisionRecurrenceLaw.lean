import GaloisForLFunctions.HTGeometry.RelativeWeightedHistoryCompletion
import GaloisForLFunctions.HTGeometry.ConstitutiveEntropicAlternatingFormation

/-!
# Causal collision recurrence law

A completed error may retain arbitrary internal difference while having no dissipative transverse
charge.  This file separates those two statements.  A collision is a pair of source states, a
source-defined additive reporter reads only its transverse difference, and squared norm is the
generated collision action.

If a completion history has an exact nonnegative action ledger and its source potential returns
cofinally to its initial value, every transverse collision action vanishes.  Differences in the
kernel of the transverse reporter remain unrestricted.  No divisor, zero set, spectral operator,
or target charge occurs in the construction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

variable {H K : Type*} [AddCommGroup H]

/-- Transverse charge of a collision pair.  The full difference may retain kernel-valued internal
data even when this charge vanishes. -/
def collisionTransverseCharge [AddCommGroup K]
    (tau : H →+ K) (collision : H × H) : K :=
  tau (collision.1 - collision.2)

/-- Nonnegative dissipative action seen by the transverse collision reporter. -/
def collisionTransverseAction [NormedAddCommGroup K]
    (tau : H →+ K) (collision : H × H) : ℝ :=
  ‖collisionTransverseCharge tau collision‖ ^ 2

theorem collisionTransverseAction_nonneg [NormedAddCommGroup K]
    (tau : H →+ K) (collision : H × H) :
    0 ≤ collisionTransverseAction tau collision := by
  simp only [collisionTransverseAction]
  positivity

/-- Transverse action vanishes exactly when the reported collision charge vanishes. -/
theorem collisionTransverseAction_eq_zero_iff [NormedAddCommGroup K]
    (tau : H →+ K) (collision : H × H) :
    collisionTransverseAction tau collision = 0 ↔
      collisionTransverseCharge tau collision = 0 := by
  simp [collisionTransverseAction]

/-- Zero transverse action means precisely that the full collision difference lies in the
reporter's kernel; it does not force equality of the two source states. -/
theorem collisionTransverseAction_eq_zero_iff_difference_mem_ker
    [NormedAddCommGroup K]
    (tau : H →+ K) (collision : H × H) :
    collisionTransverseAction tau collision = 0 ↔
      collision.1 - collision.2 ∈ tau.ker := by
  rw [collisionTransverseAction_eq_zero_iff]
  rfl

/-- Exact completion accounting: source potential after one step plus the current transverse
collision action equals source potential before the step. -/
def IsCausalCollisionActionLedger [NormedAddCommGroup K]
    (tau : H →+ K) (potential : H × H → ℝ)
    (history : ℕ → H × H) : Prop :=
  ∀ n, IsRealActionRepairStep potential history
    (fun j => collisionTransverseAction tau (history j)) n

/-- Cofinal recurrence is required of the unprojected source potential, not merely of a finite or
scalar observer unrelated to the action ledger. -/
def IsCofinalCollisionPotentialRecurrent
    (potential : H × H → ℝ) (history : ℕ → H × H) : Prop :=
  ∀ ε > 0, ∀ N, ∃ n, N ≤ n ∧
    |potential (history n) - potential (history 0)| < ε

/-- **Recurrent collision dissipation rigidity.** Exact nonnegative source accounting and cofinal
return force every dissipative transverse collision charge to vanish.  Kernel-valued soliton or
multiplicity data may survive at every stage. -/
theorem collisionTransverseCharge_eq_zero_of_actionLedger_of_recurrent
    [NormedAddCommGroup K]
    (tau : H →+ K) (potential : H × H → ℝ)
    (history : ℕ → H × H)
    (hledger : IsCausalCollisionActionLedger tau potential history)
    (hrecurrent : IsCofinalCollisionPotentialRecurrent potential history) :
    ∀ n, collisionTransverseCharge tau (history n) = 0 := by
  have hstationary : ∀ n, collisionTransverseAction tau (history n) = 0 :=
    recurrentRealActionRepairHistory_stationary potential history
      (fun j => collisionTransverseAction tau (history j))
      hledger
      (fun j => collisionTransverseAction_nonneg tau (history j))
      hrecurrent
  intro n
  exact (collisionTransverseAction_eq_zero_iff tau (history n)).mp (hstationary n)

/-- Kernel form of recurrent collision rigidity.  This is the exact survivor needed for defects
whose transverse migration vanishes while internal topological information remains. -/
theorem collisionDifference_mem_ker_of_actionLedger_of_recurrent
    [NormedAddCommGroup K]
    (tau : H →+ K) (potential : H × H → ℝ)
    (history : ℕ → H × H)
    (hledger : IsCausalCollisionActionLedger tau potential history)
    (hrecurrent : IsCofinalCollisionPotentialRecurrent potential history) :
    ∀ n, (history n).1 - (history n).2 ∈ tau.ker := by
  intro n
  exact (collisionTransverseAction_eq_zero_iff_difference_mem_ker tau (history n)).mp
    ((collisionTransverseAction_eq_zero_iff tau (history n)).mpr
      (collisionTransverseCharge_eq_zero_of_actionLedger_of_recurrent
        tau potential history hledger hrecurrent n))

/-- Every prescribed kernel difference is a zero-action collision.  Recurrent dissipation removes
only transverse charge, not the collision itself. -/
theorem collisionTransverseAction_pair_zero_eq_zero_of_mem_ker
    [NormedAddCommGroup K]
    (tau : H →+ K) {z : H} (hz : z ∈ tau.ker) :
    collisionTransverseAction tau (z, 0) = 0 := by
  rw [collisionTransverseAction_eq_zero_iff_difference_mem_ker]
  simpa

/-- A transverse collision charge is replayed cofinally when arbitrarily late collision arrows
approximate it in the unprojected transverse norm. -/
def IsCofinalCollisionChargeRecurrent [NormedAddCommGroup K]
    (tau : H →+ K) (history : ℕ → H × H) (collision : H × H) : Prop :=
  ∀ ε > 0, ∀ N, ∃ n, N ≤ n ∧
    ‖collisionTransverseCharge tau (history n) -
      collisionTransverseCharge tau collision‖ < ε

/-- **Cofinal collision-replication rigidity.** A finite total relative action cannot contain
arbitrarily late approximate replicas of one positive transverse charge.  Unlike pointwise
successor invariance, the collision may move through history; unlike potential recurrence, no
monotone state potential is assumed. -/
theorem collisionTransverseCharge_eq_zero_of_summableAction_of_cofinallyRecurrent
    [NormedAddCommGroup K]
    (tau : H →+ K) (history : ℕ → H × H) (collision : H × H)
    (hsummable : Summable (fun n => collisionTransverseAction tau (history n)))
    (hrecurrent : IsCofinalCollisionChargeRecurrent tau history collision) :
    collisionTransverseCharge tau collision = 0 := by
  have haction : Tendsto
      (fun n => collisionTransverseAction tau (history n)) atTop (𝓝 0) :=
    hsummable.tendsto_atTop_zero
  have hnorm : Tendsto
      (fun n => ‖collisionTransverseCharge tau (history n)‖) atTop (𝓝 0) := by
    have hsqrt : Tendsto
        (fun n => Real.sqrt (collisionTransverseAction tau (history n)))
        atTop (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp haction
    simpa only [collisionTransverseAction,
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  by_contra hcharge
  have hchargePos : 0 < ‖collisionTransverseCharge tau collision‖ :=
    norm_pos_iff.mpr hcharge
  let ε : ℝ := ‖collisionTransverseCharge tau collision‖ / 3
  have hε : 0 < ε := div_pos hchargePos (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hnorm) ε hε
  obtain ⟨n, hnN, hnclose⟩ := hrecurrent ε hε N
  have hnsmallMetric := hN n hnN
  have hnsmall : ‖collisionTransverseCharge tau (history n)‖ < ε := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (norm_nonneg _)] using hnsmallMetric
  have hnclose' :
      ‖collisionTransverseCharge tau collision -
        collisionTransverseCharge tau (history n)‖ < ε := by
    calc
      ‖collisionTransverseCharge tau collision -
          collisionTransverseCharge tau (history n)‖ =
          ‖-(collisionTransverseCharge tau collision -
            collisionTransverseCharge tau (history n))‖ := (norm_neg _).symm
      _ = ‖collisionTransverseCharge tau (history n) -
          collisionTransverseCharge tau collision‖ := by
            congr 1
            abel
      _ < ε := hnclose
  have htriangle :
      ‖collisionTransverseCharge tau collision‖ ≤
        ‖collisionTransverseCharge tau collision -
          collisionTransverseCharge tau (history n)‖ +
        ‖collisionTransverseCharge tau (history n)‖ := by
    calc
      ‖collisionTransverseCharge tau collision‖ =
          ‖(collisionTransverseCharge tau collision -
            collisionTransverseCharge tau (history n)) +
            collisionTransverseCharge tau (history n)‖ := by
              congr 1
              abel
      _ ≤ _ := norm_add_le _ _
  have hlt : ‖collisionTransverseCharge tau collision‖ < ε + ε :=
    htriangle.trans_lt (add_lt_add hnclose' hnsmall)
  dsimp only [ε] at hlt
  linarith

end

end GaloisForLFunctions.HTGeometry
