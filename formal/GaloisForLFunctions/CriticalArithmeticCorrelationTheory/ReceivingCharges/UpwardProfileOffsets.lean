import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmallWidthKeepsPrimeGeometryPolynomial

/-!
# Literal upward rows in a linear offset strip

For arbitrary arithmetic profiles, small physical width turns the infinite
prime-power row into finitely many positive and negative integer offsets.
All positivity and horizon cutoffs remain in the exact identity.
-/

noncomputable section
open MeasureTheory Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence

/-- Small physical width confines each active product to a strip linear in overlap. -/
theorem upward_product_distance_le_small_width {c : ℝ} (hc : 0 < c) {N T j : ℕ}
    (hT : 1 ≤ T) (hj : j ∈ Icc 1 N)
    (hlog : |Real.log T - Real.log j| ≤ c / N) (hwidth : c / N ≤ 1) :
    |(T : ℝ) - j| ≤ linearPrimeStrip c := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hj).2
  have hN0 : (0 : ℝ) < N := hj0.trans_le hjN
  calc
    _ ≤ (j : ℝ) * (Real.exp (c / N) - 1) := abs_sub_le_of_abs_log_le hT0 hj0 hlog
    _ ≤ (j : ℝ) * (c / N * Real.exp (c / N)) :=
      mul_le_mul_of_nonneg_left exp_sub_one_le_mul_exp hj0.le
    _ ≤ (N : ℝ) * (c / N * Real.exp (c / N)) :=
      mul_le_mul_of_nonneg_right hjN (by positivity)
    _ = c * Real.exp (c / N) := by field_simp
    _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hwidth) hc.le
    _ ≤ _ := Nat.le_ceil _

/-- The positive offset contribution, with its actual horizon cutoff. -/
def positiveUpwardProfileOffset (g : ℝ → ℝ) (N : ℕ) (F : ℕ → ℝ) (n k h : ℕ) : ℝ :=
  if k * n + h ≤ N then F (k * n + h) / Real.sqrt (k * n + h : ℕ) *
    bumpCorr g (Real.log (k * n : ℕ) - Real.log (k * n + h : ℕ)) else 0

/-- The negative offset contribution, with both positivity and horizon cutoffs. -/
def negativeUpwardProfileOffset (g : ℝ → ℝ) (N : ℕ) (F : ℕ → ℝ) (n k h : ℕ) : ℝ :=
  if h < k * n ∧ k * n - h ≤ N then
    F (k * n - h) / Real.sqrt (k * n - h : ℕ) *
      bumpCorr g (Real.log (k * n : ℕ) - Real.log (k * n - h : ℕ)) else 0

/-- Exact offset reindexing of the literal infinite upward prime-power action. -/
theorem upwardProfileRow_eq_offsets_small_width {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N n : ℕ} (hn : n ∈ Icc 1 N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0) (hwidth : c / N ≤ 1) (F : ℕ → ℝ) :
    upwardPrimeRow g N (fun j => F j / Real.sqrt j) n =
      ∑ k ∈ Icc 1 (N + linearPrimeStrip c), _root_.RHTower.vonMangoldtAtom k *
        ∑ h ∈ Icc 1 (linearPrimeStrip c),
          (positiveUpwardProfileOffset g N F n k h + negativeUpwardProfileOffset g N F n k h) := by
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  let B := linearPrimeStrip c
  have hinner (k : ℕ) (hk : 1 ≤ k) :
      (∑ j ∈ Icc 1 N, F j / Real.sqrt j *
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) =
      ∑ h ∈ Icc 1 B, (positiveUpwardProfileOffset g N F n k h + negativeUpwardProfileOffset g N F n k h) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hT : 1 ≤ k * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hlog (j : ℕ) : Real.log k - (Real.log j - Real.log n) =
        Real.log (k * n : ℕ) - Real.log j := by
      rw [Nat.cast_mul, Real.log_mul hk0.ne' hn0.ne']
      ring
    let G : ℕ → ℝ := fun j => F j / Real.sqrt j *
      bumpCorr g (Real.log (k * n : ℕ) - Real.log j)
    have hband : ∀ j ∈ Icc 1 N, k * n + B < j ∨ j + B < k * n → G j = 0 := by
      intro j hj hout
      have hgap : c / N < |Real.log (k * n : ℕ) - Real.log j| := by
        by_contra h
        have hd := upward_product_distance_le_small_width hc hT hj (le_of_not_gt h) hwidth
        have hlow := (abs_le.mp hd).1
        have hhigh := (abs_le.mp hd).2
        have h1 : j ≤ k * n + B := by
          have : (j : ℝ) ≤ (k * n : ℕ) + B := by linarith only [hlow]
          exact_mod_cast this
        have h2 : k * n ≤ j + B := by
          have : ((k * n : ℕ) : ℝ) ≤ j + B := by linarith only [hhigh]
          exact_mod_cast this
        omega
      dsimp only [G]
      rw [bumpCorr_eq_zero hgsupp hgap, mul_zero]
    calc
      _ = ∑ j ∈ Icc 1 N, if j = k * n then 0 else G j := by
        apply sum_congr rfl
        intro j _
        rw [hlog]
        split_ifs <;> simp only [mul_zero, G]
      _ = _ := by
        rw [sum_offDiagonal_eq_offset_sums G N (k * n) B hT hband, ← sum_add_distrib]
        exact sum_congr rfl fun h _ => rfl
  rw [upwardPrimeRow]
  have hrew : (∑' k : ℕ, _root_.RHTower.vonMangoldtAtom k * ∑ j ∈ Icc 1 N,
      F j / Real.sqrt j *
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) =
      ∑' k : ℕ, _root_.RHTower.vonMangoldtAtom k * ∑ h ∈ Icc 1 B,
        (positiveUpwardProfileOffset g N F n k h + negativeUpwardProfileOffset g N F n k h) := by
    apply tsum_congr
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [vonMangoldtAtom_eq_zero_of_lt_two (by norm_num : (0 : ℕ) < 2), zero_mul]
    · rw [hinner k hk]
  rw [hrew]
  apply tsum_eq_sum
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [vonMangoldtAtom_eq_zero_of_lt_two (by norm_num : (0 : ℕ) < 2), zero_mul]
  · have hbig : N + B < k := by
      by_contra h
      exact hk (mem_Icc.mpr ⟨hk0, by omega⟩)
    have hkn : k ≤ k * n := by simpa only [mul_one] using Nat.mul_le_mul_left k hn1
    have hzero : (∑ h ∈ Icc 1 B,
        (positiveUpwardProfileOffset g N F n k h + negativeUpwardProfileOffset g N F n k h)) = 0 := by
      apply sum_eq_zero
      intro h hh
      have hhB := (mem_Icc.mp hh).2
      have hpos : ¬ k * n + h ≤ N := by omega
      have hneg : ¬ (h < k * n ∧ k * n - h ≤ N) := by omega
      simp only [positiveUpwardProfileOffset, negativeUpwardProfileOffset, if_neg hpos, if_neg hneg, add_zero]
    rw [hzero, mul_zero]


#print axioms upwardProfileRow_eq_offsets_small_width

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
