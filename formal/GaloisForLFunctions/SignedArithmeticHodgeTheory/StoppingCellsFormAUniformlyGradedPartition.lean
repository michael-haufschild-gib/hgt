import GaloisForLFunctions.SignedArithmeticHodgeTheory.GeneratorCutoffsAreLogarithmicBlockAverages

/-!
# The logarithmic stopping grid has uniformly comparable widths

A zero padding cell precedes the original logarithmic cells. Beyond label A,
the widths repeat the band A through 2A-1. Prefix sums give the actual stopping
boundaries. Every width is at most one, and consecutive widths differ by at
most a factor of three, independently of the cutoff and translation level.
-/

noncomputable section
open RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

/-- The original label determining a stopping-grid width. -/
def stoppingGridLabel (A : ℕ+) (k : ℕ) : ℕ :=
  if k < (A : ℕ) then k else (A : ℕ) + k % (A : ℕ)

/-- The first width pads the half-line by one zero cell; all others are logarithmic widths. -/
def stoppingGridWidth (A : ℕ+) (k : ℕ) : ℝ :=
  if k = 0 then Real.log 2 else logCell (stoppingGridLabel A k)

/-- Ordered boundaries of the padded stopping partition. -/
def stoppingGridBoundary (A : ℕ+) (k : ℕ) : ℝ :=
  -Real.log 2 + ∑ r ∈ Finset.range k, stoppingGridWidth A r

theorem stoppingGridLabel_of_le (A : ℕ+) {k : ℕ} (hk : k ≤ (A : ℕ)) :
    stoppingGridLabel A k = k := by
  rcases lt_or_eq_of_le hk with h | h
  · exact if_pos h
  · subst k
    simp only [stoppingGridLabel, lt_self_iff_false, if_false, Nat.mod_self, Nat.add_zero]

theorem stoppingGridLabel_band (A : ℕ+) {k : ℕ} (hk : (A : ℕ) ≤ k) :
    (A : ℕ) ≤ stoppingGridLabel A k ∧ stoppingGridLabel A k < 2 * (A : ℕ) := by
  rw [stoppingGridLabel, if_neg (not_lt_of_ge hk)]
  have h := Nat.mod_lt k A.pos
  omega

theorem stoppingGridLabel_pos (A : ℕ+) {k : ℕ} (hk : 0 < k) :
    0 < stoppingGridLabel A k := by
  by_cases h : k ≤ (A : ℕ)
  · rwa [stoppingGridLabel_of_le A h]
  · exact A.pos.trans_le (stoppingGridLabel_band A (by omega)).1

theorem stoppingGridWidth_pos (A : ℕ+) (k : ℕ) : 0 < stoppingGridWidth A k := by
  by_cases hk : k = 0
  · rw [stoppingGridWidth, if_pos hk]
    exact Real.log_pos (by norm_num)
  · rw [stoppingGridWidth, if_neg hk]
    exact logCell_pos (stoppingGridLabel_pos A (by omega))

theorem stoppingGridWidth_le_one (A : ℕ+) (k : ℕ) : stoppingGridWidth A k ≤ 1 := by
  have hl : Real.log 2 ≤ (1 : ℝ) := by
    simpa only [logCell, Nat.cast_one, one_add_one_eq_two, Real.log_one, sub_zero, div_one]
      using logCell_le (show 0 < (1 : ℕ) by omega)
  by_cases hk : k = 0
  · simpa only [stoppingGridWidth, hk, if_true] using hl
  · rw [stoppingGridWidth, if_neg hk]
    have hn := stoppingGridLabel_pos A (by omega : 0 < k)
    refine (logCell_le hn).trans ?_
    apply (div_le_one (by exact_mod_cast hn : (0 : ℝ) < stoppingGridLabel A k)).mpr
    exact_mod_cast hn

private theorem logCell_le_three {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hnm : n + 1 ≤ 3 * m) : logCell m ≤ 3 * logCell n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc
    _ ≤ 1 / (m : ℝ) := logCell_le hm
    _ ≤ 3 * (1 / ((n : ℝ) + 1)) := by
      rw [mul_one_div, div_le_div_iff₀ hmR hnR]
      simpa only [one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
        using (show (n : ℝ) + 1 ≤ 3 * (m : ℝ) by exact_mod_cast hnm)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_logCell hn) (by norm_num)

/-- Consecutive stopping widths have two-sided ratio at most three. -/
theorem stoppingGridWidth_adjacent (A : ℕ+) (k : ℕ) :
    stoppingGridWidth A k ≤ 3 * stoppingGridWidth A (k + 1) ∧
      stoppingGridWidth A (k + 1) ≤ 3 * stoppingGridWidth A k := by
  by_cases hk : k = 0
  · subst k
    have hlabel := stoppingGridLabel_of_le A (show 1 ≤ (A : ℕ) from A.pos)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    simp only [stoppingGridWidth, if_true, Nat.zero_add, Nat.one_ne_zero, if_false,
      hlabel, logCell, Nat.cast_one, one_add_one_eq_two, Real.log_one, sub_zero]
    constructor <;> linarith only [hlog]
  · have hk0 : 0 < k := by omega
    rw [stoppingGridWidth, if_neg hk, stoppingGridWidth, if_neg (by omega : k + 1 ≠ 0)]
    by_cases hka : k + 1 ≤ (A : ℕ)
    · rw [stoppingGridLabel_of_le A (by omega : k ≤ (A : ℕ)), stoppingGridLabel_of_le A hka]
      exact ⟨logCell_le_three hk0 (by omega) (by omega),
        logCell_le_three (by omega) hk0 (by omega)⟩
    · have ha := stoppingGridLabel_band A (show (A : ℕ) ≤ k by omega)
      have hb := stoppingGridLabel_band A (show (A : ℕ) ≤ k + 1 by omega)
      have hA := A.pos
      exact ⟨logCell_le_three (by omega) (by omega) (by omega),
        logCell_le_three (by omega) (by omega) (by omega)⟩

theorem stoppingGridBoundary_zero (A : ℕ+) : stoppingGridBoundary A 0 = -Real.log 2 := by
  simp only [stoppingGridBoundary, Finset.range_zero, Finset.sum_empty, add_zero]

theorem stoppingGridBoundary_succ (A : ℕ+) (k : ℕ) :
    stoppingGridBoundary A (k + 1) = stoppingGridBoundary A k + stoppingGridWidth A k := by
  simp only [stoppingGridBoundary, Finset.sum_range_succ]
  ring

theorem stoppingGridBoundary_strictMono (A : ℕ+) : StrictMono (stoppingGridBoundary A) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [stoppingGridBoundary_succ]
  exact lt_add_of_pos_right _ (stoppingGridWidth_pos A k)

/-- The initial grid boundaries are the original logarithmic endpoints. -/
theorem stoppingGridBoundary_initial (A : ℕ+) {k : ℕ} (hk : 1 ≤ k) (hkA : k ≤ (A : ℕ)) :
    stoppingGridBoundary A k = Real.log (k : ℝ) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst k
      simp only [Nat.zero_add, stoppingGridBoundary, Finset.sum_range_one,
        stoppingGridWidth, if_true, neg_add_cancel, Nat.cast_one, Real.log_one]
    · have hp : 1 ≤ k := by omega
      rw [stoppingGridBoundary_succ, ih hp (by omega), stoppingGridWidth, if_neg hk0,
        stoppingGridLabel_of_le A (by omega), logCell]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

theorem stoppingGridBoundary_add (A : ℕ+) (k r : ℕ) :
    stoppingGridBoundary A (k + r) = stoppingGridBoundary A k +
      ∑ s ∈ Finset.range r, stoppingGridWidth A (k + s) := by
  simp only [stoppingGridBoundary, Finset.sum_range_add]
  ring

/-- Each translated band has the same logarithmic widths. -/
theorem stoppingGridWidth_band (A : ℕ+) (j r : ℕ) (hr : r < (A : ℕ)) :
    stoppingGridWidth A ((A : ℕ) + j * (A : ℕ) + r) = logCell ((A : ℕ) + r) := by
  have hp : 0 < (A : ℕ) + j * (A : ℕ) + r := by have := A.pos; omega
  rw [stoppingGridWidth, if_neg (by omega), stoppingGridLabel, if_neg (by omega)]
  simp only [Nat.add_mod, Nat.mod_self, Nat.mul_mod, Nat.zero_mod, Nat.mul_zero,
    Nat.zero_add, Nat.mod_eq_of_lt hr]

private theorem sum_logCell_add (a r : ℕ) :
    (∑ s ∈ Finset.range r, logCell (a + s)) =
      Real.log ((a + r : ℕ) : ℝ) - Real.log (a : ℝ) := by
  induction r with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero, sub_self]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, logCell]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

private theorem stoppingGridBoundary_band_offset (A : ℕ+) (j r : ℕ) (hr : r ≤ (A : ℕ)) :
    stoppingGridBoundary A ((A : ℕ) + j * (A : ℕ) + r) =
      stoppingGridBoundary A ((A : ℕ) + j * (A : ℕ)) +
        (Real.log (((A : ℕ) + r : ℕ) : ℝ) - Real.log (A : ℝ)) := by
  rw [stoppingGridBoundary_add]
  congr 1
  rw [← sum_logCell_add]
  apply Finset.sum_congr rfl
  intro s hs
  exact stoppingGridWidth_band A j s ((Finset.mem_range.mp hs).trans_le hr)

/-- The start of each repeated band is a literal dyadic translate of log A. -/
theorem stoppingGridBoundary_band_start (A : ℕ+) (j : ℕ) :
    stoppingGridBoundary A ((A : ℕ) + j * (A : ℕ)) =
      (j : ℝ) * Real.log 2 + Real.log (A : ℝ) := by
  induction j with
  | zero =>
    simpa only [Nat.zero_mul, Nat.add_zero, Nat.cast_zero, zero_mul, zero_add] using
      stoppingGridBoundary_initial A A.pos le_rfl
  | succ j ih =>
    rw [show (A : ℕ) + (j + 1) * (A : ℕ) = (A : ℕ) + j * (A : ℕ) + (A : ℕ) by
        simp only [Nat.add_mul, Nat.one_mul]; omega,
      stoppingGridBoundary_band_offset A j (A : ℕ) le_rfl, ih]
    have hAA : Real.log (((A : ℕ) + (A : ℕ) : ℕ) : ℝ) =
        Real.log 2 + Real.log (A : ℝ) := by
      rw [show (A : ℕ) + (A : ℕ) = 2 * (A : ℕ) by omega, Nat.cast_mul, Nat.cast_ofNat,
        Real.log_mul (by norm_num) (by exact_mod_cast A.pos.ne' : (A : ℝ) ≠ 0)]
    rw [hAA]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- Every repeated grid endpoint is exactly a stopping-cell endpoint. -/
theorem stoppingGridBoundary_band (A : ℕ+) (j r : ℕ) (hr : r ≤ (A : ℕ)) :
    stoppingGridBoundary A ((A : ℕ) + j * (A : ℕ) + r) =
      (j : ℝ) * Real.log 2 + Real.log (((A : ℕ) + r : ℕ) : ℝ) := by
  rw [stoppingGridBoundary_band_offset A j r hr, stoppingGridBoundary_band_start]
  ring

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.stoppingGridWidth_adjacent
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.stoppingGridBoundary_strictMono
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.stoppingGridBoundary_band
