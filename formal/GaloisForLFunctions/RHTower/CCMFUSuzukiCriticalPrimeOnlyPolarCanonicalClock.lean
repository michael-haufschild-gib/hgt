import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalPrimeOnlyAbsoluteVariationNoGo

/-!
# Canonical-clock dynamics of the literal CCM--FU prime--polar codiagonal

The unresolved CCM--FU source is the valuation-one prime-minus-polar action with its
literal moving triangular cutoff.  This file proves its exact dynamics between consecutive
logarithmic arithmetic walls.  On the cell with active endpoint `N`, it is `S_N - T_N / H`,
with both finite sums retaining every prime and polar contribution.  The entering cell vanishes
at the next wall, so adjacent formulae join without a boundary debt.

No estimate is made.  In particular, this removes no signed term and does not claim boundedness:
it identifies the genuine remaining cancellation problem as a canonical discrete-clock problem.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- Constant component of the literal valuation-one prime--polar codiagonal on the
logarithmic cell with active endpoint `N`. -/
def ccmFUCriticalPrimeOnlyPolarStaticAction (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N - 2),
    suzukiCheckpointCriticalPrimeOnlyPolarCell (j + 3) *
      (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
        Real.log ((j + 3 : ℕ) : ℝ) ^ (3 : ℕ))

/-- Reciprocal-wall component of the same literal codiagonal. -/
def ccmFUCriticalPrimeOnlyPolarSlopeAction (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N - 2),
    suzukiCheckpointCriticalPrimeOnlyPolarCell (j + 3) *
      (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
        Real.log ((j + 3 : ℕ) : ℝ) ^ (2 : ℕ))

/-- The actual floor clock is constant on each half-open logarithmic arithmetic cell. -/
theorem suzukiCheckpointEventIndex_eq_of_log_cell
    {N : ℕ} (hN : 1 ≤ N) {H : ℝ}
    (hlo : Real.log (N : ℝ) ≤ H)
    (hhi : H < Real.log ((N + 1 : ℕ) : ℝ)) :
    suzukiCheckpointEventIndex H = N := by
  unfold suzukiCheckpointEventIndex
  apply (Nat.floor_eq_iff (Real.exp_pos H).le).2
  constructor
  · calc
      (N : ℝ) = Real.exp (Real.log (N : ℝ)) :=
        (Real.exp_log (by exact_mod_cast Nat.zero_lt_of_lt hN)).symm
      _ ≤ Real.exp H := Real.exp_le_exp.mpr hlo
  · calc
      Real.exp H < Real.exp (Real.log ((N + 1 : ℕ) : ℝ)) :=
        Real.exp_lt_exp.mpr hhi
      _ = ((N + 1 : ℕ) : ℝ) := Real.exp_log (by positivity)
      _ = (N : ℝ) + 1 := by push_cast; ring

/-- Between consecutive logarithmic arithmetic walls, the literal moving prime--polar
codiagonal is affine in the reciprocal wall. -/
theorem ccmFUCriticalPrimeOnlyPolarAction_eq_static_sub_slope_div
    {N : ℕ} (_hN : 3 ≤ N) {H : ℝ}
    (hindex : suzukiCheckpointEventIndex H = N) (hH : H ≠ 0) :
    suzukiCheckpointCriticalPrimeOnlyPolarAction H =
      ccmFUCriticalPrimeOnlyPolarStaticAction N -
        ccmFUCriticalPrimeOnlyPolarSlopeAction N / H := by
  rw [suzukiCheckpointCriticalPrimeOnlyPolarAction, hindex]
  unfold ccmFUCriticalPrimeOnlyPolarStaticAction
    ccmFUCriticalPrimeOnlyPolarSlopeAction
  change (∑ j ∈ Finset.range (N - 2),
    suzukiCheckpointCriticalPrimeOnlyPolarCell (j + 3) *
      suzukiCheckpointCriticalTriangularMultiplier H j) = _
  calc
    _ = ∑ j ∈ Finset.range (N - 2),
        (suzukiCheckpointCriticalPrimeOnlyPolarCell (j + 3) *
          (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
            Real.log ((j + 3 : ℕ) : ℝ) ^ (3 : ℕ)) -
        (suzukiCheckpointCriticalPrimeOnlyPolarCell (j + 3) *
          (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
            Real.log ((j + 3 : ℕ) : ℝ) ^ (2 : ℕ))) / H) := by
          apply Finset.sum_congr rfl
          intro j _hj
          have hn : (1 : ℝ) < ((j + 3 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 1 < j + 3)
          have hlog : Real.log ((j + 3 : ℕ) : ℝ) ≠ 0 :=
            ne_of_gt (Real.log_pos hn)
          unfold suzukiCheckpointCriticalTriangularMultiplier
            ccmGuinandWeilThirdGradeCesaroTriangularWeight
            ccmGuinandWeilThirdGradeWeight
          field_simp [hH, hlog]
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div]

/-- At a new logarithmic wall, the entering literal codiagonal cell has zero triangular
weight, so the reciprocal-wall formula has no jump. -/
theorem ccmFUCriticalPrimeOnlyPolarStatic_succ_sub_slope_div
    {N : ℕ} (hN : 3 ≤ N) :
    ccmFUCriticalPrimeOnlyPolarStaticAction (N + 1) -
        ccmFUCriticalPrimeOnlyPolarSlopeAction (N + 1) /
          Real.log ((N + 1 : ℕ) : ℝ) =
      ccmFUCriticalPrimeOnlyPolarStaticAction N -
        ccmFUCriticalPrimeOnlyPolarSlopeAction N /
          Real.log ((N + 1 : ℕ) : ℝ) := by
  have hlog : Real.log ((N + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < N + 1)))
  unfold ccmFUCriticalPrimeOnlyPolarStaticAction
    ccmFUCriticalPrimeOnlyPolarSlopeAction
  rw [show N + 1 - 2 = (N - 2) + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show N - 2 + 3 = N + 1 by omega]
  have hlast :
      suzukiCheckpointCriticalPrimeOnlyPolarCell (N + 1) *
          (32 * Real.sqrt ((N + 1 : ℕ) : ℝ) /
            Real.log ((N + 1 : ℕ) : ℝ) ^ (3 : ℕ)) =
        (suzukiCheckpointCriticalPrimeOnlyPolarCell (N + 1) *
          (32 * Real.sqrt ((N + 1 : ℕ) : ℝ) /
            Real.log ((N + 1 : ℕ) : ℝ) ^ (2 : ℕ))) /
          Real.log ((N + 1 : ℕ) : ℝ) := by
    field_simp [hlog]
  rw [hlast, add_div]
  ring

/-- Canonical left-wall value of the literal codiagonal. -/
theorem ccmFUCriticalPrimeOnlyPolarAction_log_eq_static_sub_slope_div
    {N : ℕ} (hN : 3 ≤ N) :
    suzukiCheckpointCriticalPrimeOnlyPolarAction (Real.log (N : ℝ)) =
      ccmFUCriticalPrimeOnlyPolarStaticAction N -
        ccmFUCriticalPrimeOnlyPolarSlopeAction N / Real.log (N : ℝ) := by
  apply ccmFUCriticalPrimeOnlyPolarAction_eq_static_sub_slope_div hN
  · apply suzukiCheckpointEventIndex_eq_of_log_cell (by omega : 1 ≤ N)
    · exact le_rfl
    · have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      exact Real.strictMonoOn_log hNpos hNp1pos
        (by exact_mod_cast (by omega : N < N + 1))
  · exact ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))

/-- Canonical right-wall value uses the same completed source as the left cell because the
newly active term vanishes exactly. -/
theorem ccmFUCriticalPrimeOnlyPolarAction_log_succ_eq_static_sub_slope_div
    {N : ℕ} (hN : 3 ≤ N) :
    suzukiCheckpointCriticalPrimeOnlyPolarAction (Real.log ((N + 1 : ℕ) : ℝ)) =
      ccmFUCriticalPrimeOnlyPolarStaticAction N -
        ccmFUCriticalPrimeOnlyPolarSlopeAction N /
          Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [ccmFUCriticalPrimeOnlyPolarAction_log_eq_static_sub_slope_div
    (by omega : 3 ≤ N + 1),
    ccmFUCriticalPrimeOnlyPolarStatic_succ_sub_slope_div hN]

end
