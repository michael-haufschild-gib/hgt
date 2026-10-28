import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellPrimeCompression

/-!
# Pair averages and the triangular prime action

Every complete adjacent cell pair splits into its weighted average and its
balanced detail. Integer dilation preserves the average block, so its pairing
into the balanced block vanishes. The opposite mixed orientation is retained.
-/

noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry HTGeometry

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-- The constant profile on two complete adjacent cells. -/
def coarseAtom (a : ℕ) : L²₊ := cellAtom (2 * a) + cellAtom (2 * a + 1)

/-- The weighted average of the two independent cell coefficients. -/
def pairAverage (a : ℕ) (u v : ℝ) : ℝ := haarRightCoeff a * u + haarLeftCoeff a * v

/-- Every complete pair is its actual average plus its jump-one balanced detail. -/
theorem cellPair_eq_average_add_detail {a : ℕ} (ha : 1 ≤ a) (u v : ℝ) :
    (u : ℂ) • cellAtom (2 * a) + (v : ℂ) • cellAtom (2 * a + 1) =
      (pairAverage a u v : ℂ) • coarseAtom a + ((u - v : ℝ) : ℂ) • haarAtom a := by
  have hl : pairAverage a u v + (u - v) * haarLeftCoeff a = u := by
    calc
      _ = u * (haarLeftCoeff a + haarRightCoeff a) := by unfold pairAverage; ring
      _ = u := by rw [haarCoeff_sum ha, mul_one]
  have hr : pairAverage a u v - (u - v) * haarRightCoeff a = v := by
    calc
      _ = v * (haarLeftCoeff a + haarRightCoeff a) := by unfold pairAverage; ring
      _ = v := by rw [haarCoeff_sum ha, mul_one]
  symm
  calc
    _ = ((pairAverage a u v + (u - v) * haarLeftCoeff a : ℝ) : ℂ) • cellAtom (2 * a) +
        ((pairAverage a u v - (u - v) * haarRightCoeff a : ℝ) : ℂ) • cellAtom (2 * a + 1) := by
      simp only [coarseAtom, haarAtom, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        smul_add, smul_sub, smul_smul, add_smul, sub_smul]
      abel
    _ = _ := by rw [hl, hr]

/-- The average cell is the original cell translated by `log 2`. -/
theorem coarseAtom_eq_shift {a : ℕ} (ha : 1 ≤ a) :
    coarseAtom a = halfLineRightShift (Real.log 2) (cellAtom a) := by
  have h := halfLineRightShift_cellAtom (m := 2) ha (by omega)
  rw [Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0)] at h
  simpa only [Nat.cast_ofNat, sum_range_zero, zero_add,
    Nat.mul_comm a 2, Nat.add_zero, coarseAtom] using h.symm

private def cellReading (lo hi n : ℕ) : ℝ := if lo ≤ n ∧ n < hi then 1 else 0

private theorem cellReading_difference {lo hi : ℕ} (h : lo ≤ hi) (n : ℕ) :
    cellReading lo hi n - cellReading lo hi (n + 1) =
      (if hi = n + 1 then 1 else 0) - (if lo = n + 1 then 1 else 0) := by
  unfold cellReading
  split_ifs <;> norm_num at * <;> omega

private theorem inner_shift_cellAtom_reading {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : 2 ≤ m) :
    inner ℂ (halfLineRightShift (Real.log m) (cellAtom a)) (cellAtom b) =
      ((logCellWidth b * cellReading (a * m) ((a + 1) * m) b : ℝ) : ℂ) := by
  rw [inner_shift_cellAtom_entry ha hb hm]
  unfold cellReading
  split_ifs <;> simp only [mul_one, mul_zero, Complex.ofReal_zero]

/-- Only the translated endpoint jumps of a complete cell can meet a balanced detail. -/
theorem inner_shift_cellAtom_haarAtom {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : 2 ≤ m) :
    (inner ℂ (halfLineRightShift (Real.log m) (cellAtom a)) (haarAtom b)).re =
      haarMass b * ((if (a + 1) * m = 2 * b + 1 then 1 else 0) -
        (if a * m = 2 * b + 1 then 1 else 0)) := by
  rw [haarAtom, inner_sub_right, inner_smul_right, inner_smul_right,
    inner_shift_cellAtom_reading ha (by omega) hm,
    inner_shift_cellAtom_reading ha (by omega) hm]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [← mul_assoc, (haarCoeff_mass b).1, ← mul_assoc, (haarCoeff_mass b).2,
    ← mul_sub]
  congr 1
  exact cellReading_difference (Nat.mul_le_mul_right m (Nat.le_succ a)) (2 * b)

/-- Integer prime translations send no pair-average component into a balanced detail. -/
theorem inner_shift_coarseAtom_haarAtom {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : 2 ≤ m) :
    (inner ℂ (halfLineRightShift (Real.log m) (coarseAtom a)) (haarAtom b)).re = 0 := by
  have hlo : (2 * a) * m ≠ 2 * b + 1 := by rw [Nat.mul_assoc]; omega
  have hhi : (2 * a + 1 + 1) * m ≠ 2 * b + 1 := by
    rw [show (2 * a + 1 + 1) * m = 2 * (a * m + m) by ring]
    omega
  rw [coarseAtom, map_add, inner_add_left, Complex.add_re,
    inner_shift_cellAtom_haarAtom (by omega) hb hm,
    inner_shift_cellAtom_haarAtom (by omega) hb hm,
    if_neg hlo, if_neg hhi]
  ring

/-- Finite pair-average sections with arbitrary signed coefficients. -/
def coarseSection (c : ℕ → ℝ) (X : ℕ) : L²₊ :=
  ∑ a ∈ Icc 1 X, (c a : ℂ) • coarseAtom a

/-- The entire average-to-detail prime block vanishes before summing prime weights. -/
theorem inner_shift_coarseSection_haarSection (c d : ℕ → ℝ) (X Y : ℕ) {m : ℕ}
    (hm : 2 ≤ m) :
    (inner ℂ (halfLineRightShift (Real.log m) (coarseSection c X)) (haarSection d Y)).re = 0 := by
  unfold coarseSection haarSection
  rw [map_sum, sum_inner, Complex.re_sum]
  apply sum_eq_zero
  intro a ha
  rw [inner_sum, Complex.re_sum]
  apply sum_eq_zero
  intro b hb
  simp only [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [inner_shift_coarseAtom_haarAtom (mem_Icc.mp ha).1 (mem_Icc.mp hb).1 hm]
  ring

#print axioms cellPair_eq_average_add_detail
#print axioms coarseAtom_eq_shift
#print axioms inner_shift_cellAtom_haarAtom
#print axioms inner_shift_coarseAtom_haarAtom
#print axioms inner_shift_coarseSection_haarSection

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
