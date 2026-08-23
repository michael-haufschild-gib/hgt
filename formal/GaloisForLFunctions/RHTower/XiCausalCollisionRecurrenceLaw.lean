import GaloisForLFunctions.HTGeometry.CausalCollisionRecurrenceLaw
import GaloisForLFunctions.RHTower.XiGlobalReflectionDefectEnergy

/-!
# Xi causal-collision recurrence endpoint

The global Xi reflection-defect energy is already an exact late scalarization: it is nonnegative
and vanishes exactly under the Riemann hypothesis.  This file does not assume a spectral or
zero-generated physical system.  It records the precise interface by which a divisor-free recurrent
completion-action ledger would force that late scalar defect to vanish.

The potential, history, and action remain arbitrary here.  A successful source construction must
define them independently of the Xi divisor and prove the ledger, recurrence, and landing theorem;
none of those inputs is asserted by this endpoint.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Recurrent completion-error endpoint.**  If a source-defined exact action ledger returns
cofinally in its own potential and its initial generated action later identifies with the global Xi
reflection-defect energy, then RH follows. -/
theorem riemannHypothesis_of_xiGlobalReflectionDefect_recurrentActionLedger
    {S : Type*}
    (potential : S → ℝ) (history : ℕ → S) (action : ℕ → ℝ)
    (hledger : ∀ n, IsRealActionRepairStep potential history action n)
    (haction : ∀ n, 0 ≤ action n)
    (hrecurrent : ∀ ε > 0, ∀ K, ∃ N, K ≤ N ∧
      |potential (history N) - potential (history 0)| < ε)
    (hlanding : action 0 = xiGlobalReflectionDefectEnergy) :
    RiemannHypothesis := by
  have hzero : action 0 = 0 :=
    recurrentRealActionRepairHistory_stationary
      potential history action hledger haction hrecurrent 0
  apply xiGlobalReflectionDefectEnergy_eq_zero_iff_rh.mp
  rw [← hlanding]
  exact hzero

/-- **Cofinal collision-replay endpoint.**  If one divisor-free relative collision carrier has
summable total transverse action, an arbitrarily late replay of its marked collision, and a late
landing of that marked action as the global Xi reflection defect, then RH follows. -/
theorem riemannHypothesis_of_xiGlobalReflectionDefect_summableCollisionReplay
    {H K : Type*} [AddCommGroup H] [NormedAddCommGroup K]
    (tau : H →+ K) (history : ℕ → H × H) (collision : H × H)
    (hsummable : Summable (fun n => collisionTransverseAction tau (history n)))
    (hrecurrent : IsCofinalCollisionChargeRecurrent tau history collision)
    (hlanding : collisionTransverseAction tau collision =
      xiGlobalReflectionDefectEnergy) :
    RiemannHypothesis := by
  have hcharge : collisionTransverseCharge tau collision = 0 :=
    collisionTransverseCharge_eq_zero_of_summableAction_of_cofinallyRecurrent
      tau history collision hsummable hrecurrent
  have haction : collisionTransverseAction tau collision = 0 :=
    (collisionTransverseAction_eq_zero_iff tau collision).mpr hcharge
  apply xiGlobalReflectionDefectEnergy_eq_zero_iff_rh.mp
  rw [← hlanding]
  exact haction

end

end RHTower
