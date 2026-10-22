import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarCoordinateTransport

/-!
# Actual-head matched polar adjacent codiagonal

The finite matched-cell coverage seam has a literal source decomposition that preserves its
signed prime--polar geometry.  In exponential polar mass coordinate, the quantile cells concatenate
exactly, while adjacent matched cells need neither do so nor have a fixed orientation.  The residual
is therefore a marked codiagonal: one oriented interval from the lower endpoint of cell `n + 1`
to the upper endpoint of cell `n`, plus two literal boundary intervals.

This module proves that exact finite identity.  It deliberately proves no sign or boundedness
claim: controlling the displayed codiagonal against the actual translation-defect profile is the
remaining arithmetic problem.
-/

open scoped BigOperators
open Finset ArithmeticFunction MeasureTheory

noncomputable section

namespace RHTower

/-- Adjacent displacement increment is exactly the oriented raw matched-cell overlap/gap. -/
theorem ccmActualHeadMatchedQuantilePolarDisplacement_succ_sub_eq_adjacentGap (n : ℕ) :
    ccmActualHeadMatchedQuantilePolarDisplacement (n + 1) -
        ccmActualHeadMatchedQuantilePolarDisplacement n =
      ccmActualHeadMatchedPolarUpperCoordinate n -
        ccmActualHeadMatchedPolarLowerCoordinate (n + 1) := by
  unfold ccmActualHeadMatchedQuantilePolarDisplacement
  have hquantile := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  have hmatched := ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight n
  linarith

/-- Finite oriented interval codiagonal.  The interior terms are literal adjacent overlap/gap
windows; no ordering assumption is imposed. -/
theorem sum_interval_cells_sub_quantile_eq_adjacentCodiagonal
    (F : ℝ → ℝ) (L U q : ℕ → ℝ)
    (hF : ∀ {x y : ℝ}, 0 < x → 0 < y → IntervalIntegrable F volume x y)
    (hL : ∀ n, 0 < L n) (hU : ∀ n, 0 < U n) (hq : ∀ n, 0 < q n) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), ∫ y in L n..U n, F y) -
        (∫ y in q 0..q (N + 1), F y) =
      (∑ n ∈ Finset.range N, ∫ y in L (n + 1)..U n, F y) +
        (∫ y in q (N + 1)..U N, F y) + (∫ y in L 0..q 0, F y) := by
  induction N with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have hsplit₁ : (∫ y in L 0..q 1, F y) =
          (∫ y in L 0..q 0, F y) + ∫ y in q 0..q 1, F y := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals
          (hF (hL 0) (hq 0))
          (hF (hq 0) (hq 1))
      have hsplit₂ : (∫ y in L 0..U 0, F y) =
          (∫ y in L 0..q 1, F y) + ∫ y in q 1..U 0, F y := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals
          (hF (hL 0) (hq 1))
          (hF (hq 1) (hU 0))
      calc
        (∫ y in L 0..U 0, F y) - (∫ y in q 0..q 1, F y) =
            ((∫ y in L 0..q 0, F y) + (∫ y in q 0..q 1, F y) +
              (∫ y in q 1..U 0, F y)) - (∫ y in q 0..q 1, F y) := by
                rw [hsplit₂, hsplit₁]
        _ = (∫ y in q 1..U 0, F y) + (∫ y in L 0..q 0, F y) := by ring
  | succ N ih =>
      change
        (∑ n ∈ Finset.range (N + 2), ∫ y in L n..U n, F y) -
            (∫ y in q 0..q (N + 2), F y) =
          (∑ n ∈ Finset.range (N + 1), ∫ y in L (n + 1)..U n, F y) +
            (∫ y in q (N + 2)..U (N + 1), F y) + (∫ y in L 0..q 0, F y)
      have hquantile : (∫ y in q 0..q (N + 2), F y) =
          (∫ y in q 0..q (N + 1), F y) + ∫ y in q (N + 1)..q (N + 2), F y := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals
          (hF (hq 0) (hq (N + 1)))
          (hF (hq (N + 1)) (hq (N + 2)))
      have hcell₁ : (∫ y in L (N + 1)..q (N + 2), F y) =
          (∫ y in L (N + 1)..q (N + 1), F y) +
            ∫ y in q (N + 1)..q (N + 2), F y := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals
          (hF (hL (N + 1)) (hq (N + 1)))
          (hF (hq (N + 1)) (hq (N + 2)))
      have hcell₂ : (∫ y in L (N + 1)..U (N + 1), F y) =
          (∫ y in L (N + 1)..q (N + 2), F y) +
            ∫ y in q (N + 2)..U (N + 1), F y := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals
          (hF (hL (N + 1)) (hq (N + 2)))
          (hF (hq (N + 2)) (hU (N + 1)))
      have hedge : (∫ y in L (N + 1)..U N, F y) =
          (∫ y in L (N + 1)..q (N + 1), F y) +
            ∫ y in q (N + 1)..U N, F y := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals
          (hF (hL (N + 1)) (hq (N + 1)))
          (hF (hq (N + 1)) (hU N))
      calc
        (∑ n ∈ Finset.range (N + 2), ∫ y in L n..U n, F y) -
            (∫ y in q 0..q (N + 2), F y) =
            ((∑ n ∈ Finset.range (N + 1), ∫ y in L n..U n, F y) +
              (∫ y in L (N + 1)..U (N + 1), F y)) -
                (∫ y in q 0..q (N + 2), F y) := by
              rw [Finset.sum_range_succ]
        _ = ((∑ n ∈ Finset.range (N + 1), ∫ y in L n..U n, F y) -
              (∫ y in q 0..q (N + 1), F y)) +
                ((∫ y in L (N + 1)..U (N + 1), F y) -
                  (∫ y in q (N + 1)..q (N + 2), F y)) := by
              rw [hquantile]
              ring
        _ = ((∑ n ∈ Finset.range N, ∫ y in L (n + 1)..U n, F y) +
              (∫ y in q (N + 1)..U N, F y) + (∫ y in L 0..q 0, F y)) +
                ((∫ y in L (N + 1)..U (N + 1), F y) -
                  (∫ y in q (N + 1)..q (N + 2), F y)) := by rw [ih]
        _ = (∑ n ∈ Finset.range N, ∫ y in L (n + 1)..U n, F y) +
            (∫ y in L (N + 1)..U N, F y) +
              (∫ y in q (N + 2)..U (N + 1), F y) + (∫ y in L 0..q 0, F y) := by
              rw [hcell₂, hcell₁]
              linarith [hedge]
        _ = (∑ n ∈ Finset.range (N + 1), ∫ y in L (n + 1)..U n, F y) +
            (∫ y in q (N + 2)..U (N + 1), F y) + (∫ y in L 0..q 0, F y) := by
              rw [Finset.sum_range_succ]

/-- The actual defect profile is interval-integrable on every strictly positive mass-coordinate
interval.  No continuity at the logarithmic coordinate singularity `0` is used. -/
theorem ccmActualHeadPolarMassDefectProfile_intervalIntegrable_of_pos
    (f : SoninL2) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (ccmActualHeadPolarMassDefectProfile f) volume x y := by
  have hcont : ContinuousOn (ccmActualHeadPolarMassDefectProfile f) (Set.Ioi 0) := by
    intro z hz
    unfold ccmActualHeadPolarMassDefectProfile ccmActualHeadPolarHeightCoordinate
    have hdiv : ContinuousAt (fun w : ℝ => w / 2) z := continuousAt_id.div_const 2
    have hlog : ContinuousAt Real.log (z / 2) :=
      Real.continuousAt_log
        (div_ne_zero (ne_of_gt hz) (by norm_num : (2 : ℝ) ≠ 0))
    have hlogdiv : ContinuousAt (fun w : ℝ => Real.log (w / 2)) z :=
      hlog.comp' (f := fun w : ℝ => w / 2) (x := z) hdiv
    have hheight : ContinuousAt (fun w : ℝ => 2 * Real.log (w / 2)) z :=
      by simpa [mul_comm] using hlogdiv.const_mul 2
    exact ((((continuous_logTranslationCLM f).continuousAt.comp hheight).sub
      continuousAt_const).norm.pow 2).continuousWithinAt
  apply ContinuousOn.intervalIntegrable
  rcases le_total x y with hxy | hyx
  · rw [Set.uIcc_of_le hxy]
    exact hcont.mono fun z hz => Set.mem_Ioi.mpr (lt_of_lt_of_le hx hz.1)
  · rw [Set.uIcc_comm, Set.uIcc_of_le hyx]
    exact hcont.mono fun z hz => Set.mem_Ioi.mpr (lt_of_lt_of_le hy hz.1)

/-- Shifted finite-range enumeration of the literal integer head. -/
theorem sum_range_shift_two_eq_sum_Icc_two (K : ℕ) (H : ℕ → ℝ) :
    (∑ n ∈ Finset.range (K + 1), H (n + 2)) =
      ∑ n ∈ Finset.Icc 2 (K + 2), H n := by
  refine Finset.sum_bij (fun n _ => n + 2) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_Icc] at hn ⊢
    omega
  · intro a _ha b _hb hab
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n - 2, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro n _hn
    rfl

/-- Adjacent codiagonal acting on an arbitrary mass-coordinate test profile. -/
def ccmActualHeadMatchedPolarAdjacentCodiagonalProfile (K : ℕ) (F : ℝ → ℝ) : ℝ :=
  (∑ n ∈ Finset.range K,
    ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
        ccmActualHeadMatchedPolarUpperCoordinate (n + 2), F y) +
    (∫ y in ccmActualHeadQuantilePolarCoordinate (K + 3)..
        ccmActualHeadMatchedPolarUpperCoordinate (K + 2), F y) +
    (∫ y in ccmActualHeadMatchedPolarLowerCoordinate 2..
        ccmActualHeadQuantilePolarCoordinate 2, F y)

/-- The profile codiagonal is exactly the finite matched-minus-quantile coverage difference. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_eq_cells_sub_quantile
    (K : ℕ) (F : ℝ → ℝ)
    (hF : ∀ {x y : ℝ}, 0 < x → 0 < y → IntervalIntegrable F volume x y) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K F =
      (∑ n ∈ Finset.range (K + 1),
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 2)..
            ccmActualHeadMatchedPolarUpperCoordinate (n + 2), F y) -
        (∫ y in ccmActualHeadQuantilePolarCoordinate 2..
            ccmActualHeadQuantilePolarCoordinate (K + 3), F y) := by
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonalProfile]
  symm
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (sum_interval_cells_sub_quantile_eq_adjacentCodiagonal
      (F := F)
      (L := fun n => ccmActualHeadMatchedPolarLowerCoordinate (n + 2))
      (U := fun n => ccmActualHeadMatchedPolarUpperCoordinate (n + 2))
      (q := fun n => ccmActualHeadQuantilePolarCoordinate (n + 2))
      (hF := hF)
      (hL := fun n => by
        unfold ccmActualHeadMatchedPolarLowerCoordinate
        positivity)
      (hU := fun n => by
        unfold ccmActualHeadMatchedPolarUpperCoordinate
        positivity)
      (hq := fun n => by
        unfold ccmActualHeadQuantilePolarCoordinate
        positivity)
      K)

/-- Exact zero-clock conservation: the marked adjacent codiagonal annihilates constants. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_one (K : ℕ) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun _ : ℝ => 1) = 0 := by
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_eq_cells_sub_quantile]
  · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    have hlength (n : ℕ) :
        ccmActualHeadMatchedPolarUpperCoordinate n -
            ccmActualHeadMatchedPolarLowerCoordinate n =
          ccmActualHeadQuantilePolarCoordinate (n + 1) -
            ccmActualHeadQuantilePolarCoordinate n := by
      rw [ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight,
        ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight]
    simp_rw [hlength]
    have htel :
        (∑ n ∈ Finset.range (K + 1),
          (ccmActualHeadQuantilePolarCoordinate (n + 3) -
            ccmActualHeadQuantilePolarCoordinate (n + 2))) =
          ccmActualHeadQuantilePolarCoordinate (K + 3) -
            ccmActualHeadQuantilePolarCoordinate 2 := by
      induction K with
      | zero => simp
      | succ K ih =>
          rw [Finset.sum_range_succ]
          norm_num at ih ⊢
          linarith
    rw [htel]
    ring
  · intro x y hx hy
    exact continuous_const.intervalIntegrable x y

/-- The lower endpoint of each quantile cell is the rigid translation of its matched-cell
lower endpoint. -/
theorem ccmActualHeadMatchedQuantilePolar_lower_eq_lower_add_displacement (n : ℕ) :
    ccmActualHeadQuantilePolarCoordinate n =
      ccmActualHeadMatchedPolarLowerCoordinate n +
        ccmActualHeadMatchedQuantilePolarDisplacement n := by
  unfold ccmActualHeadMatchedQuantilePolarDisplacement
  ring

/-- Equal atom masses force the same rigid translation at the upper endpoint. -/
theorem ccmActualHeadMatchedQuantilePolar_upper_eq_upper_add_displacement (n : ℕ) :
    ccmActualHeadQuantilePolarCoordinate (n + 1) =
      ccmActualHeadMatchedPolarUpperCoordinate n +
        ccmActualHeadMatchedQuantilePolarDisplacement n := by
  have hquantile := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  have hmatched := ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight n
  unfold ccmActualHeadMatchedQuantilePolarDisplacement
  linarith

/-- Literal quantile cells concatenate, including their signed first mass-coordinate moment. -/
theorem ccmActualHeadMatchedQuantilePolar_sum_massCoordinate (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1),
      ∫ y in ccmActualHeadQuantilePolarCoordinate (n + 2)..
          ccmActualHeadQuantilePolarCoordinate (n + 3), y) =
      ∫ y in ccmActualHeadQuantilePolarCoordinate 2..
          ccmActualHeadQuantilePolarCoordinate (K + 3), y := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      exact intervalIntegral.integral_add_adjacent_intervals
        (continuous_id.intervalIntegrable (μ := volume) _ _)
        (continuous_id.intervalIntegrable (μ := volume) _ _)

/-- The first nonconstant mass-coordinate mode of the literal codiagonal is precisely the
atom-weighted signed matched-to-quantile displacement.  Thus it is neither a cellwise positive
quantity nor the zero-clock mass already annihilated by the preceding conservation law. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_massCoordinate (K : ℕ) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun y : ℝ => y) =
      - ∑ n ∈ Finset.range (K + 1),
        ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) *
          criticalMellinAtomWeight (n + 2) := by
  have htranslate (a b d : ℝ) :
      (∫ y in a..b, y) - (∫ y in a + d..b + d, y) = -d * (b - a) := by
    rw [integral_id, integral_id]
    ring
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_eq_cells_sub_quantile]
  · rw [← ccmActualHeadMatchedQuantilePolar_sum_massCoordinate]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    calc
      (∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 2)..
          ccmActualHeadMatchedPolarUpperCoordinate (n + 2), y) -
          (∫ y in ccmActualHeadQuantilePolarCoordinate (n + 2)..
            ccmActualHeadQuantilePolarCoordinate (n + 3), y) =
          (∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 2)..
            ccmActualHeadMatchedPolarUpperCoordinate (n + 2), y) -
          (∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 2) +
            ccmActualHeadMatchedQuantilePolarDisplacement (n + 2)..
            ccmActualHeadMatchedPolarUpperCoordinate (n + 2) +
              ccmActualHeadMatchedQuantilePolarDisplacement (n + 2), y) := by
            rw [ccmActualHeadMatchedQuantilePolar_lower_eq_lower_add_displacement,
              ccmActualHeadMatchedQuantilePolar_upper_eq_upper_add_displacement]
      _ = -ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) *
          (ccmActualHeadMatchedPolarUpperCoordinate (n + 2) -
            ccmActualHeadMatchedPolarLowerCoordinate (n + 2)) :=
          htranslate _ _ _
      _ = -(ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) *
          criticalMellinAtomWeight (n + 2)) := by
          rw [ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight]
          ring
  · intro x y hx hy
    exact continuous_id.intervalIntegrable x y

/-- The unrenormalized first mode contains the completed node error plus a literal positive
raw-upper-endpoint excess.  Hence this scalar mode is not, by itself, a cancellation-faithful
completed-source reporter. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_massCoordinate_eq_error_add_upperExcess
    (K : ℕ) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun y : ℝ => y) =
      ∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          (ccmActualHeadOutgoingNodeError (n + 2) +
            (ccmActualHeadMatchedPolarUpperCoordinate (n + 2) -
              2 * Real.exp (Real.log (n + 2) / 2))) := by
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_massCoordinate,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hpositive : 0 < n + 2 := by omega
  rw [ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess
    (n + 2) hpositive]
  norm_num [Nat.cast_add]
  ring

/-- The raw upper-endpoint mark forced by the literal matched-cell geometry.  It is kept as a
separate channel so the completed-source cancellation cannot be silently discarded. -/
def ccmActualHeadMatchedPolarAdjacentCodiagonalEndpointCounterterm (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    criticalMellinAtomWeight (n + 2) *
      (ccmActualHeadMatchedPolarUpperCoordinate (n + 2) -
        2 * Real.exp (Real.log (n + 2) / 2))

/-- Endpoint-renormalized first codiagonal mode.  This is an exact source readout only; no
boundedness, positivity, or RH implication is asserted here. -/
def ccmActualHeadMatchedPolarAdjacentCodiagonalEndpointRenormalizedFirstMoment
    (K : ℕ) : ℝ :=
  ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun y : ℝ => y) -
    ccmActualHeadMatchedPolarAdjacentCodiagonalEndpointCounterterm K

/-- After retaining and subtracting its marked endpoint channel, the first codiagonal mode is
exactly the signed, critical-Mellin-atom-weighted outgoing completed error. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalEndpointRenormalizedFirstMoment_eq_error
    (K : ℕ) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalEndpointRenormalizedFirstMoment K =
      ∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * ccmActualHeadOutgoingNodeError (n + 2) := by
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonalEndpointRenormalizedFirstMoment,
    ccmActualHeadMatchedPolarAdjacentCodiagonalEndpointCounterterm,
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_massCoordinate_eq_error_add_upperExcess]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Direct marked codiagonal of literal matched polar cells.  Each interior term retains its
prime index and its orientation records a gap versus an overlap. -/
def ccmActualHeadMatchedPolarAdjacentCodiagonal (K : ℕ) (f : SoninL2) : ℝ :=
  (∑ n ∈ Finset.range K,
    ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 3)..
        ccmActualHeadMatchedPolarUpperCoordinate (n + 2),
      ccmActualHeadPolarMassDefectProfile f y) +
    (∫ y in ccmActualHeadQuantilePolarCoordinate (K + 3)..
        ccmActualHeadMatchedPolarUpperCoordinate (K + 2),
      ccmActualHeadPolarMassDefectProfile f y) +
    (∫ y in ccmActualHeadMatchedPolarLowerCoordinate 2..
        ccmActualHeadQuantilePolarCoordinate 2,
      ccmActualHeadPolarMassDefectProfile f y)

theorem ccmActualHeadMatchedPolarAdjacentCodiagonal_eq_profile
    (K : ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPolarAdjacentCodiagonal K f =
      ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K
        (ccmActualHeadPolarMassDefectProfile f) := rfl

/-- The marked adjacent codiagonal is exactly the finite matched-minus-quantile coverage
difference in mass coordinate. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonal_eq_cells_sub_quantile
    (K : ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPolarAdjacentCodiagonal K f =
      (∑ n ∈ Finset.range (K + 1),
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 2)..
            ccmActualHeadMatchedPolarUpperCoordinate (n + 2),
          ccmActualHeadPolarMassDefectProfile f y) -
        (∫ y in ccmActualHeadQuantilePolarCoordinate 2..
            ccmActualHeadQuantilePolarCoordinate (K + 3),
          ccmActualHeadPolarMassDefectProfile f y) := by
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonal]
  symm
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (sum_interval_cells_sub_quantile_eq_adjacentCodiagonal
      (F := ccmActualHeadPolarMassDefectProfile f)
      (L := fun n => ccmActualHeadMatchedPolarLowerCoordinate (n + 2))
      (U := fun n => ccmActualHeadMatchedPolarUpperCoordinate (n + 2))
      (q := fun n => ccmActualHeadQuantilePolarCoordinate (n + 2))
      (hF := ccmActualHeadPolarMassDefectProfile_intervalIntegrable_of_pos f)
      (hL := fun n => by
        unfold ccmActualHeadMatchedPolarLowerCoordinate
        positivity)
      (hU := fun n => by
        unfold ccmActualHeadMatchedPolarUpperCoordinate
        positivity)
      (hq := fun n => by
        unfold ccmActualHeadQuantilePolarCoordinate
        positivity)
      K)

/-- Same exact producer with the literal head index set `2, ..., K + 2`. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonal_eq_IccCells_sub_quantile
    (K : ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPolarAdjacentCodiagonal K f =
      (∑ n ∈ Finset.Icc 2 (K + 2),
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
            ccmActualHeadMatchedPolarUpperCoordinate n,
          ccmActualHeadPolarMassDefectProfile f y) -
        (∫ y in ccmActualHeadQuantilePolarCoordinate 2..
            ccmActualHeadQuantilePolarCoordinate (K + 3),
          ccmActualHeadPolarMassDefectProfile f y) := by
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonal_eq_cells_sub_quantile]
  congr 1
  exact sum_range_shift_two_eq_sum_Icc_two K
    (fun n => ∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
      ccmActualHeadMatchedPolarUpperCoordinate n,
        ccmActualHeadPolarMassDefectProfile f y)

end RHTower
