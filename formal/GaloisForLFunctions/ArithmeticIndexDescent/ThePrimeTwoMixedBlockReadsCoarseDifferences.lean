import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellCoarseSplitting
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellGammaPayment

/-!
# The reverse prime-two block reads coarse differences

Prime translation sends a balanced detail into two adjacent pair averages.
Its original mixed pairing is therefore a weighted difference of those
averages. The other mixed orientation vanishes. An adjustable signed payment
retains this variation instead of replacing it by the whole coarse mass.
-/

noncomputable section

open MeasureTheory Finset Complex
open scoped InnerProduct
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

private theorem adjacent_logCellWidths {a : ℕ} (ha : 1 ≤ a) :
    logCellWidth (2 * a) + logCellWidth (2 * a + 1) = logCellWidth a := by
  calc
    _ = Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ) := by
      unfold logCellWidth
      push_cast
      rw [show (2 : ℝ) * a + 1 + 1 = 2 * a + 2 by ring]
      ring
    _ = _ := haarPairWidth ha

/-- Pair averages are orthogonal with the square masses of the original coarse cells. -/
theorem inner_coarseAtom {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    inner ℂ (coarseAtom a) (coarseAtom b) = if a = b then (logCellWidth a : ℂ) else 0 := by
  have ha0 : 1 ≤ 2 * a := by omega
  have ha1 : 1 ≤ 2 * a + 1 := by omega
  have hb0 : 1 ≤ 2 * b := by omega
  have hb1 : 1 ≤ 2 * b + 1 := by omega
  unfold coarseAtom
  rw [inner_add_left, inner_add_right, inner_add_right,
    inner_cellAtom ha0 hb0, inner_cellAtom ha0 hb1,
    inner_cellAtom ha1 hb0, inner_cellAtom ha1 hb1]
  by_cases hab : a = b
  · subst b
    simp only [if_pos rfl, if_neg (by omega : 2 * a ≠ 2 * a + 1),
      if_neg (by omega : 2 * a + 1 ≠ 2 * a), add_zero, zero_add]
    rw [← Complex.ofReal_add, adjacent_logCellWidths ha]
  · simp only [if_neg hab, if_neg (by omega : 2 * a ≠ 2 * b),
      if_neg (by omega : 2 * a ≠ 2 * b + 1),
      if_neg (by omega : 2 * a + 1 ≠ 2 * b),
      if_neg (by omega : 2 * a + 1 ≠ 2 * b + 1), add_zero]

theorem inner_coarseAtom_coarseSection (q : ℕ → ℝ) {a X : ℕ}
    (ha : 1 ≤ a) (haX : a ≤ X) :
    inner ℂ (coarseAtom a) (coarseSection q X) = ((logCellWidth a * q a : ℝ) : ℂ) := by
  classical
  rw [coarseSection, inner_sum, Finset.sum_eq_single a]
  · rw [inner_smul_right, inner_coarseAtom ha ha, if_pos rfl]
    push_cast
    ring
  · intro b hb hba
    rw [inner_smul_right, inner_coarseAtom ha (Finset.mem_Icc.mp hb).1,
      if_neg hba.symm, mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_Icc.mpr ⟨ha, haX⟩))

/-- The prime-two translation lands in the actual adjacent pair-average cells. -/
theorem halfLineRightShift_two_haarAtom {a : ℕ} (ha : 1 ≤ a) :
    halfLineRightShift (Real.log 2) (haarAtom a) =
      (haarLeftCoeff a : ℂ) • coarseAtom (2 * a) -
        (haarRightCoeff a : ℂ) • coarseAtom (2 * a + 1) := by
  rw [haarAtom, map_sub, map_smul, map_smul,
    ← coarseAtom_eq_shift (by omega : 1 ≤ 2 * a),
    ← coarseAtom_eq_shift (by omega : 1 ≤ 2 * a + 1)]

/-- One translated detail reads the difference of the two complete coarse coefficients. -/
theorem inner_shift_two_haarAtom_coarseSection (q : ℕ → ℝ) {a X : ℕ}
    (ha : 1 ≤ a) (haX : 2 * a + 1 ≤ X) :
    (inner ℂ (halfLineRightShift (Real.log 2) (haarAtom a)) (coarseSection q X)).re =
      haarMass a * (q (2 * a) - q (2 * a + 1)) := by
  rw [halfLineRightShift_two_haarAtom ha, inner_sub_left, inner_smul_left, inner_smul_left,
    inner_coarseAtom_coarseSection q (by omega : 1 ≤ 2 * a) (by omega : 2 * a ≤ X),
    inner_coarseAtom_coarseSection q (by omega : 1 ≤ 2 * a + 1) haX]
  simp only [Complex.sub_re, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← mul_assoc, (haarCoeff_mass a).1, ← mul_assoc, (haarCoeff_mass a).2]
  ring

/-- The entire surviving mixed block retains its signed adjacent differences. -/
theorem inner_shift_two_haarSection_coarseSection (d q : ℕ → ℝ) {Y X : ℕ}
    (hYX : 2 * Y + 1 ≤ X) :
    (inner ℂ (halfLineRightShift (Real.log 2) (haarSection d Y)) (coarseSection q X)).re =
      ∑ a ∈ Finset.Icc 1 Y, haarMass a * d a * (q (2 * a) - q (2 * a + 1)) := by
  unfold haarSection
  rw [map_sum, sum_inner, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_smul, inner_smul_left]
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [inner_shift_two_haarAtom_coarseSection q (Finset.mem_Icc.mp ha).1
    (by have := (Finset.mem_Icc.mp ha).2; omega)]
  ring

/-- The original prime-two coefficient multiplying both mixed source orientations. -/
def primeTwoMixedSource (d q : ℕ → ℝ) (Y X : ℕ) : ℝ :=
  (2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
    ((inner ℂ (halfLineRightShift (Real.log 2) (haarSection d Y)) (coarseSection q X)).re +
      (inner ℂ (halfLineRightShift (Real.log 2) (coarseSection q X)) (haarSection d Y)).re)

/-- Square mass of the actual detail coefficients. -/
def primeTwoDetailMass (d : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 Y, haarMass a * d a ^ 2

/-- Coarse variation seen by the surviving prime-two orientation. -/
def primeTwoCoarseVariation (q : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 Y, haarMass a * (q (2 * a) - q (2 * a + 1)) ^ 2

/-- The other prime orientation vanishes before the arithmetic weight is applied. -/
theorem primeTwoMixedSource_eq (d q : ℕ → ℝ) {Y X : ℕ} (hYX : 2 * Y + 1 ≤ X) :
    primeTwoMixedSource d q Y X =
      (2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
        ∑ a ∈ Finset.Icc 1 Y, haarMass a * d a * (q (2 * a) - q (2 * a + 1)) := by
  rw [primeTwoMixedSource, inner_shift_coarseSection_haarSection q d X Y (by norm_num : 2 ≤ 2),
    add_zero, inner_shift_two_haarSection_coarseSection d q hYX]

private theorem signed_young {ε : ℝ} (hε : 0 < ε) (d q ell : ℝ) :
    |2 * ell * d * q| ≤ ε * d ^ 2 + (ell ^ 2 / ε) * q ^ 2 := by
  have hupper (x : ℝ) : 2 * ell * x * q ≤ ε * x ^ 2 + (ell ^ 2 / ε) * q ^ 2 := by
    have h := div_nonneg (sq_nonneg (ε * x - ell * q)) hε.le
    have he : (ε * x - ell * q) ^ 2 / ε =
        ε * x ^ 2 + (ell ^ 2 / ε) * q ^ 2 - 2 * ell * x * q := by
      field_simp [hε.ne']
      ring
    rw [he] at h
    linarith only [h]
  refine abs_le.mpr ⟨?_, hupper d⟩
  have h := hupper (-d)
  simp only [neg_sq] at h
  linarith only [h]

/-- Signed payment charges only the coarse differences actually read by the prime source. -/
theorem abs_primeTwoMixedSource_le_variation (d q : ℕ → ℝ) {Y X : ℕ}
    (hYX : 2 * Y + 1 ≤ X) {ε : ℝ} (hε : 0 < ε) :
    |primeTwoMixedSource d q Y X| ≤ ε * primeTwoDetailMass d Y +
      ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) ^ 2 / ε) * primeTwoCoarseVariation q Y := by
  let ell : ℝ := ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2
  rw [primeTwoMixedSource_eq d q hYX,
    show 2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 = 2 * ell by dsimp only [ell]; ring,
    Finset.mul_sum]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 Y, |2 * ell * (haarMass a * d a * (q (2 * a) - q (2 * a + 1)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 Y,
        (ε * (haarMass a * d a ^ 2) + (ell ^ 2 / ε) *
          (haarMass a * (q (2 * a) - q (2 * a + 1)) ^ 2)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hw := (haarMass_pos (Finset.mem_Icc.mp ha).1).le
      have h := mul_le_mul_of_nonneg_left
        (signed_young hε (d a) (q (2 * a) - q (2 * a + 1)) ell) hw
      rw [show 2 * ell * (haarMass a * d a * (q (2 * a) - q (2 * a + 1))) =
        haarMass a * (2 * ell * d a * (q (2 * a) - q (2 * a + 1))) by ring,
        abs_mul, abs_of_nonneg hw]
      convert h using 1 <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.inner_shift_two_haarSection_coarseSection
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.primeTwoMixedSource_eq
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_primeTwoMixedSource_le_variation
