import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalPrimeOnlyPolarCanonicalClock

/-!
# Causal wall transport of the literal CCM--FU prime--polar codiagonal

At a logarithmic arithmetic wall, the newly active prime--polar cell has zero literal
triangular weight.  Consequently the wall-to-wall increment of the actual valuation-one
codiagonal is driven only by its already accumulated reciprocal-wall slope.  Iterating gives
an exact finite Volterra law.  This is not a boundedness theorem: it identifies the precise
inherited signed quantity which any source-faithful CCM--FU producer must control.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- At consecutive logarithmic walls, the literal prime-only action changes only through the
previously accumulated reciprocal-wall slope.  The newly entering prime--polar cell has zero
weight at its own wall. -/
theorem ccmFUCriticalPrimeOnlyPolarAction_log_succ_sub_log_eq_inheritedSlope
    {N : ℕ} (hN : 3 ≤ N) :
    suzukiCheckpointCriticalPrimeOnlyPolarAction (Real.log ((N + 1 : ℕ) : ℝ)) -
        suzukiCheckpointCriticalPrimeOnlyPolarAction (Real.log (N : ℝ)) =
      ccmFUCriticalPrimeOnlyPolarSlopeAction N *
        (1 / Real.log (N : ℝ) - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  rw [ccmFUCriticalPrimeOnlyPolarAction_log_succ_eq_static_sub_slope_div hN,
    ccmFUCriticalPrimeOnlyPolarAction_log_eq_static_sub_slope_div hN]
  ring

/-- The literal wall action is the causal Volterra accumulation of inherited slopes.  Every
summand is a finite source history already present before its wall; no endpoint prime is used
instantaneously. -/
theorem ccmFUCriticalPrimeOnlyPolarAction_log_eq_initial_add_inheritedSlopeVolterra
    {N : ℕ} (hN : 3 ≤ N) :
    suzukiCheckpointCriticalPrimeOnlyPolarAction (Real.log (N : ℝ)) =
      suzukiCheckpointCriticalPrimeOnlyPolarAction (Real.log (3 : ℝ)) +
        ∑ k ∈ Finset.Ico 3 N,
          ccmFUCriticalPrimeOnlyPolarSlopeAction k *
            (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top (by omega : 3 ≤ N)]
      linarith [ccmFUCriticalPrimeOnlyPolarAction_log_succ_sub_log_eq_inheritedSlope hN]

end

end RHTower
