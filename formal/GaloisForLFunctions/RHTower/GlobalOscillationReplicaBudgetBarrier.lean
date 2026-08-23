import GaloisForLFunctions.RHTower.PairQubitProjectiveSeedOscillationQuantitativeLaw

/-!
# Fixed-error barrier for global oscillation replica budgets

The global oscillation compiler cannot be rescued by increasing replica order
when its one-copy contraction is no smaller than the operational fidelity
threshold.  This module proves the exact necessity: every successful budget
forces strict one-copy contraction before any replica power is taken.

For the explicit oscillation base `max 0 (1 - activation / scale²)`, success
therefore forces `error² < activation / scale²`.  Replica growth amplifies an
existing strict gap; it cannot manufacture one.  A fixed-error plateau for
extensive local systems consequently needs a blockwise/incidence-normalized
pseudodeterminant estimate, not the globally normalized oscillation base.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The Gaussian density floor used by the first-return compiler is strictly
smaller than one. -/
theorem gaussianFloorTwo_lt_one : gaussianFloorTwo < 1 := by
  rw [gaussianFloorTwo]
  have hpi : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three]
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 hpi
  have hexp : Real.exp (-2) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-2) ≤
        1 * Real.exp (-2) := by gcongr
    _ < 1 := by simp only [one_mul]; exact hexp

/-- **Replica amplification cannot create a fixed-error contraction.**
Whenever the generic first-return budget succeeds, its one-copy contraction
`q` was already strictly below the fidelity threshold `1 - epsw²`.  The
conclusion is independent of replica order and of every nonnegative remainder
term. -/
theorem globalOscillationReplicaBudget_forces_strict_oneCopyContraction
    {r : ℕ} {rank other q epsn epsw speed T : ℝ}
    (hrank : 1 ≤ rank) (hother : 0 ≤ other)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw) (hepsw : epsw < 1)
    (hspeed : 0 < speed) (hTpos : 0 < T)
    (hT : epsw / speed ≤ T)
    (hbudget : rank * (other + q ^ r) <
      gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)) *
        (1 - epsw ^ 2) ^ r) :
    q < 1 - epsw ^ 2 := by
  have hepsw0 : 0 < epsw := hepsn.trans_lt hgap
  have ha : 0 < 1 - epsw ^ 2 := by
    nlinarith [sq_nonneg epsw]
  have hmeshT : (epsw - epsn) / speed ≤ T := by
    calc
      (epsw - epsn) / speed ≤ epsw / speed := by
        exact div_le_div_of_nonneg_right
          (sub_le_self epsw hepsn) hspeed.le
      _ ≤ T := hT
  have hmeshHalf : (epsw - epsn) / speed / (2 * T) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * T)]
    linarith
  have hprefactor :
      gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)) < 1 := by
    calc
      gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)) ≤
          1 * ((epsw - epsn) / speed / (2 * T)) := by
            gcongr
            exact gaussianFloorTwo_lt_one.le
      _ ≤ 1 / 2 := by simp only [one_mul]; exact hmeshHalf
      _ < 1 := by norm_num
  by_contra hnq
  push Not at hnq
  have hq0 : 0 ≤ q := ha.le.trans hnq
  have hpow : (1 - epsw ^ 2) ^ r ≤ q ^ r :=
    pow_le_pow_left₀ ha.le hnq r
  have hleft : (1 - epsw ^ 2) ^ r ≤ rank * (other + q ^ r) := by
    calc
      (1 - epsw ^ 2) ^ r ≤ q ^ r := hpow
      _ ≤ other + q ^ r := le_add_of_nonneg_left hother
      _ ≤ rank * (other + q ^ r) := by
        have hsum0 : 0 ≤ other + q ^ r :=
          add_nonneg hother (pow_nonneg hq0 r)
        have hrankSub : 0 ≤ rank - 1 := by linarith
        nlinarith [mul_nonneg hrankSub hsum0]
  have hright :
      gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)) *
          (1 - epsw ^ 2) ^ r < (1 - epsw ^ 2) ^ r := by
    have hpowpos : 0 < (1 - epsw ^ 2) ^ r := pow_pos ha r
    simpa using mul_lt_mul_of_pos_right hprefactor hpowpos
  linarith

/-- For the explicit clipped oscillation base, a successful replica budget
forces squared operational error below normalized activation. -/
theorem explicitGlobalOscillationReplicaBudget_forces_errorSq_lt_activationRatio
    {r : ℕ} {rank other activationRatio epsn epsw speed T : ℝ}
    (hrank : 1 ≤ rank) (hother : 0 ≤ other)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw) (hepsw : epsw < 1)
    (hspeed : 0 < speed) (hTpos : 0 < T)
    (hT : epsw / speed ≤ T)
    (hbudget : rank *
        (other + (max 0 (1 - activationRatio)) ^ r) <
      gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)) *
        (1 - epsw ^ 2) ^ r) :
    epsw ^ 2 < activationRatio := by
  have hstrict :=
    globalOscillationReplicaBudget_forces_strict_oneCopyContraction
      hrank hother hepsn hgap hepsw hspeed hTpos hT hbudget
  have hraw : 1 - activationRatio < 1 - epsw ^ 2 :=
    (le_max_right 0 (1 - activationRatio)).trans_lt hstrict
  linarith

end

end RHTower
