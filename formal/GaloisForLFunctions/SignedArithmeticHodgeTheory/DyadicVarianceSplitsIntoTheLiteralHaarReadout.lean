import GaloisForLFunctions.SignedArithmeticHodgeTheory.OneGammaReservePaysAllDyadicParentVariances
import GaloisForLFunctions.SignedArithmeticHodgeTheory.BalancedCellDetailsFormTheWanderingBasis

/-!
# Actual Haar readouts in the exact dyadic variance recursion

The normalized balanced readout is the square-root parallel mass times the
difference of the actual child means. Its square is precisely the mean term
in adjacent variance splitting. Dyadic children identify the remaining two
variances with the preceding level of the same logarithmic source.
-/

noncomputable section

open MeasureTheory Set RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open ArithmeticCastelnuovoSeveri.IntervalVariance ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

/-- The normalized balanced Haar coefficient of the original source on a literal dyadic pair. -/
def logCellHaarReadout (t : ℝ) (i : ℕ × ℕ+) (f : ℝ → ℝ) : ℝ :=
  Real.sqrt (haarMass i.2) *
    (intervalMean (logCellSiblingLeft (t + i.1 * Real.log 2) i.2)
        (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2) f -
      intervalMean (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2)
        (logCellSiblingRight (t + i.1 * Real.log 2) i.2) f)

private theorem raw_shift_mul_indicator (s : ℝ) (n : ℕ) (f : ℝ → ℝ) :
    (fun x => rawCell n (x - s) * f x) =
      (Ico (s + Real.log (n : ℝ)) (s + Real.log ((n + 1 : ℕ) : ℝ))).indicator f := by
  funext x
  have hm : x - s ∈ Ico (Real.log (n : ℝ)) (Real.log ((n + 1 : ℕ) : ℝ)) ↔
      x ∈ Ico (s + Real.log (n : ℝ)) (s + Real.log ((n + 1 : ℕ) : ℝ)) := by
    constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
  simp only [rawCell, indicator_apply, hm]
  split_ifs <;> simp

private theorem integrable_raw_shift_mul (s : ℝ) (n : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) : Integrable (fun x => rawCell n (x - s) * f x) := by
  rw [raw_shift_mul_indicator]
  exact ((hf.restrict _).integrable one_le_two).integrable_indicator measurableSet_Ico

private theorem integral_raw_shift_mul (s : ℝ) (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ) :
    (∫ x, rawCell n (x - s) * f x) = logCellWidth n *
      intervalMean (s + Real.log (n : ℝ)) (s + Real.log ((n + 1 : ℕ) : ℝ)) f := by
  rw [raw_shift_mul_indicator, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo]
  have hw : s + Real.log ((n + 1 : ℕ) : ℝ) - (s + Real.log (n : ℝ)) =
      logCellWidth n := by simp only [logCellWidth, Nat.cast_add, Nat.cast_one]; ring
  rw [intervalMean, hw, mul_div_cancel₀ _ (logCellWidth_pos hn).ne']

/-- The readout uses the existing physical Haar profile, with its exact square-root mass. -/
theorem integral_translated_haarProfile_mul (t : ℝ) (i : ℕ × ℕ+)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    (∫ x, haarProfile i.2 (x - (t + i.1 * Real.log 2)) * f x) =
      Real.sqrt (haarMass i.2) * logCellHaarReadout t i f := by
  have ha := i.2.pos
  have hfun : (fun x => haarProfile i.2 (x - (t + i.1 * Real.log 2)) * f x) =
      fun x => haarLeftCoeff i.2 * (rawCell (2 * (i.2 : ℕ)) (x - (t + i.1 * Real.log 2)) * f x) -
        haarRightCoeff i.2 * (rawCell (2 * (i.2 : ℕ) + 1) (x - (t + i.1 * Real.log 2)) * f x) := by
    funext x; unfold haarProfile; ring
  rw [hfun, integral_sub ((integrable_raw_shift_mul _ _ hf).const_mul _)
    ((integrable_raw_shift_mul _ _ hf).const_mul _), integral_const_mul, integral_const_mul,
    integral_raw_shift_mul _ _ (by omega), integral_raw_shift_mul _ _ (by omega)]
  simp only [← mul_assoc, (haarCoeff_mass i.2).1, (haarCoeff_mass i.2).2,
    logCellHaarReadout, logCellSiblingLeft, logCellSiblingMiddle, logCellSiblingRight,
    Nat.add_assoc]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (haarMass_pos ha).le]
  ring

/-- The actual normalized readout square is the parallel-mass mean term. -/
theorem logCellHaarReadout_sq (t : ℝ) (i : ℕ × ℕ+) (f : ℝ → ℝ) :
    logCellHaarReadout t i f ^ 2 =
      (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2 -
          logCellSiblingLeft (t + i.1 * Real.log 2) i.2) *
        (logCellSiblingRight (t + i.1 * Real.log 2) i.2 -
          logCellSiblingMiddle (t + i.1 * Real.log 2) i.2) /
        (logCellSiblingRight (t + i.1 * Real.log 2) i.2 -
          logCellSiblingLeft (t + i.1 * Real.log 2) i.2) *
        (intervalMean (logCellSiblingLeft (t + i.1 * Real.log 2) i.2)
            (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2) f -
          intervalMean (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2)
            (logCellSiblingRight (t + i.1 * Real.log 2) i.2) f) ^ 2 := by
  obtain ⟨hl, hr, hp⟩ := logCellSibling_widths (t + i.1 * Real.log 2) i.2
  have hwidth : logCellWidth (2 * (i.2 : ℕ)) + logCellWidth (2 * (i.2 : ℕ) + 1) =
      logCellWidth i.2 := by
    rw [← hl, ← hr, ← hp]
    ring
  rw [logCellHaarReadout, mul_pow, Real.sq_sqrt (haarMass_pos i.2.pos).le, hl, hr, hp,
    haarMass, hwidth]

private theorem log_two_shift_endpoint (t : ℝ) (n : ℕ) (hn : 0 < n) :
    (t + Real.log 2) + Real.log (n : ℝ) = t + Real.log ((2 * n : ℕ) : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_ofNat,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast (Nat.ne_of_gt hn))]
  ring

/-- The two preceding-level parents are the literal children of the current parent. -/
theorem logCellSibling_children (t : ℝ) (a : ℕ+) :
    logCellSiblingLeft (t + Real.log 2) a = logCellSiblingLeft t (dyadicLeftCell a) ∧
    logCellSiblingMiddle (t + Real.log 2) a = logCellSiblingRight t (dyadicLeftCell a) ∧
    logCellSiblingMiddle (t + Real.log 2) a = logCellSiblingLeft t (dyadicRightCell a) ∧
    logCellSiblingRight (t + Real.log 2) a = logCellSiblingRight t (dyadicRightCell a) := by
  have ha := a.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (t + Real.log 2) + Real.log ((2 * (a : ℕ) : ℕ) : ℝ) =
      t + Real.log ((2 * (2 * (a : ℕ)) : ℕ) : ℝ)
    exact log_two_shift_endpoint t _ (by omega)
  · change (t + Real.log 2) + Real.log ((2 * (a : ℕ) + 1 : ℕ) : ℝ) =
      t + Real.log ((2 * (2 * (a : ℕ)) + 2 : ℕ) : ℝ)
    rw [show 2 * (2 * (a : ℕ)) + 2 = 2 * (2 * (a : ℕ) + 1) by omega]
    exact log_two_shift_endpoint t _ (by omega)
  · change (t + Real.log 2) + Real.log ((2 * (a : ℕ) + 1 : ℕ) : ℝ) =
      t + Real.log ((2 * (2 * (a : ℕ) + 1) : ℕ) : ℝ)
    exact log_two_shift_endpoint t _ (by omega)
  · change (t + Real.log 2) + Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ) =
      t + Real.log ((2 * (2 * (a : ℕ) + 1) + 2 : ℕ) : ℝ)
    rw [show 2 * (2 * (a : ℕ) + 1) + 2 = 2 * (2 * (a : ℕ) + 2) by omega]
    exact log_two_shift_endpoint t _ (by omega)

private theorem sibling_order (t : ℝ) (a : ℕ+) :
    logCellSiblingLeft t a < logCellSiblingMiddle t a ∧
      logCellSiblingMiddle t a < logCellSiblingRight t a := by
  obtain ⟨hl, hr, _⟩ := logCellSibling_widths t a
  have ha := a.pos
  constructor
  · apply sub_pos.mp
    rw [hl]
    exact logCellWidth_pos (by omega)
  · apply sub_pos.mp
    rw [hr]
    exact logCellWidth_pos (by omega)

/-- Every readout is paid by its original parent variance, without a local mean constraint. -/
theorem logCellHaarReadout_sq_le_variance (t : ℝ) (i : ℕ × ℕ+)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    logCellHaarReadout t i f ^ 2 ≤ logCellDyadicParentVariance t i f := by
  obtain ⟨hl, hr⟩ := sibling_order (t + i.1 * Real.log 2) i.2
  have h := intervalVariance_adjacent_eq hl hr hf
  rw [← logCellHaarReadout_sq t i f] at h
  have hL := intervalVariance_nonneg (logCellSiblingLeft (t + i.1 * Real.log 2) i.2)
    (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2) f
  have hR := intervalVariance_nonneg (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2)
    (logCellSiblingRight (t + i.1 * Real.log 2) i.2) f
  change _ ≤ intervalVariance _ _ f
  linarith only [h, hL, hR]

/-- Exact conservation of variance between the original dyadic source levels. -/
theorem logCellDyadicParentVariance_split (t : ℝ) (j : ℕ) (a : ℕ+)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    logCellDyadicParentVariance t (j + 1, a) f =
      logCellDyadicParentVariance t (j, dyadicLeftCell a) f +
        logCellDyadicParentVariance t (j, dyadicRightCell a) f +
        logCellHaarReadout t (j + 1, a) f ^ 2 := by
  obtain ⟨hl, hr⟩ := sibling_order (t + (j + 1 : ℕ) * Real.log 2) a
  have h := intervalVariance_adjacent_eq hl hr hf
  rw [← logCellHaarReadout_sq t (j + 1, a) f] at h
  have ht : t + ((j + 1 : ℕ) : ℝ) * Real.log 2 = (t + j * Real.log 2) + Real.log 2 := by
    push_cast
    ring
  obtain ⟨hL, hML, hMR, hR⟩ := logCellSibling_children (t + j * Real.log 2) a
  have hleft : intervalVariance (logCellSiblingLeft (t + (j + 1 : ℕ) * Real.log 2) a)
      (logCellSiblingMiddle (t + (j + 1 : ℕ) * Real.log 2) a) f =
      logCellDyadicParentVariance t (j, dyadicLeftCell a) f := by
    rw [ht, hL, hML]
    rfl
  have hright : intervalVariance (logCellSiblingMiddle (t + (j + 1 : ℕ) * Real.log 2) a)
      (logCellSiblingRight (t + (j + 1 : ℕ) * Real.log 2) a) f =
      logCellDyadicParentVariance t (j, dyadicRightCell a) f := by
    rw [ht, hMR, hR]
    rfl
  rw [hleft, hright] at h
  exact h

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellHaarReadout_sq_le_variance
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellDyadicParentVariance_split
