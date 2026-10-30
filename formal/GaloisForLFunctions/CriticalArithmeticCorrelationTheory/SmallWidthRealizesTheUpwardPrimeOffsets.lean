import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmallWidthKeepsPrimeGeometryPolynomial
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsRealizeTheCompletedShellCorrection

/-!
# Exact upward prime offsets at small physical width

When `c/N≤1`, every nonzero upward interaction lies within `ceil(ec)`
integer offsets of its prime product. Reindexing both directions retains
the exact horizon cutoff and identifies the normalized logarithmic source.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- An upward product touching a horizon atom lies in a fixed integer offset strip. -/
theorem upward_product_distance_le_small_width {c : ℝ} (hc : 0 < c) {N T j : ℕ}
    (hT : 1 ≤ T) (hj : j ∈ Icc 1 N)
    (hlog : |Real.log T - Real.log j| ≤ c / N) (hw : c / N ≤ 1) :
    |(T : ℝ) - j| ≤ linearPrimeStrip c := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hj).1.trans (mem_Icc.mp hj).2
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  calc
    _ ≤ (j : ℝ) * (Real.exp (c / N) - 1) := abs_sub_le_of_abs_log_le hT0 hj0 hlog
    _ ≤ (j : ℝ) * (c / N * Real.exp (c / N)) :=
      mul_le_mul_of_nonneg_left exp_sub_one_le_mul_exp hj0.le
    _ ≤ (N : ℝ) * (c / N * Real.exp (c / N)) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (mem_Icc.mp hj).2) (by positivity)
    _ = c * Real.exp (c / N) := by field_simp
    _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hw) hc.le
    _ ≤ _ := Nat.le_ceil _

/-- Exact offset reindexing of the literal infinite upward prime-power action. -/
theorem upwardRamanujanRow_eq_offsets_small_width {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N n : ℕ} (hn : n ∈ Icc 1 N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0) (hw : c / N ≤ 1) (m : ℕ) :
    upwardPrimeRow g N (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n =
      ∑ k ∈ Icc 1 (N + linearPrimeStrip c), _root_.RHTower.vonMangoldtAtom k *
        ∑ h ∈ Icc 1 (linearPrimeStrip c),
          (positiveUpwardOffset g N m n k h + negativeUpwardOffset g N m n k h) := by
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  let B := linearPrimeStrip c
  have hinner (k : ℕ) (hk : 1 ≤ k) :
      (∑ j ∈ Icc 1 N, ramanujanLagCoefficient m j / Real.sqrt j *
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) =
      ∑ h ∈ Icc 1 B, (positiveUpwardOffset g N m n k h + negativeUpwardOffset g N m n k h) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hT : 1 ≤ k * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hlog (j : ℕ) : Real.log k - (Real.log j - Real.log n) =
        Real.log (k * n : ℕ) - Real.log j := by
      rw [Nat.cast_mul, Real.log_mul hk0.ne' hn0.ne']
      ring
    let F : ℕ → ℝ := fun j => ramanujanLagCoefficient m j / Real.sqrt j *
      bumpCorr g (Real.log (k * n : ℕ) - Real.log j)
    have hband : ∀ j ∈ Icc 1 N, k * n + B < j ∨ j + B < k * n → F j = 0 := by
      intro j hj hout
      have hgap : c / N < |Real.log (k * n : ℕ) - Real.log j| := by
        by_contra h
        have hd := upward_product_distance_le_small_width hc hT hj (le_of_not_gt h) hw
        have hlow := (abs_le.mp hd).1
        have hhigh := (abs_le.mp hd).2
        have h1 : j ≤ k * n + B := by
          have : (j : ℝ) ≤ (k * n : ℕ) + B := by linarith only [hlow]
          exact_mod_cast this
        have h2 : k * n ≤ j + B := by
          have : ((k * n : ℕ) : ℝ) ≤ j + B := by linarith only [hhigh]
          exact_mod_cast this
        omega
      dsimp only [F]
      rw [bumpCorr_eq_zero hgsupp hgap, mul_zero]
    calc
      _ = ∑ j ∈ Icc 1 N, if j = k * n then 0 else F j := by
        apply sum_congr rfl
        intro j _
        rw [hlog]
        split_ifs <;> simp only [mul_zero, F]
      _ = _ := by
        rw [sum_offDiagonal_eq_offset_sums F N (k * n) B hT hband, ← sum_add_distrib]
        exact sum_congr rfl fun h _ => rfl
  rw [upwardPrimeRow]
  have hrew : (∑' k : ℕ, _root_.RHTower.vonMangoldtAtom k * ∑ j ∈ Icc 1 N,
      ramanujanLagCoefficient m j / Real.sqrt j *
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) =
      ∑' k : ℕ, _root_.RHTower.vonMangoldtAtom k * ∑ h ∈ Icc 1 B,
        (positiveUpwardOffset g N m n k h + negativeUpwardOffset g N m n k h) := by
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
        (positiveUpwardOffset g N m n k h + negativeUpwardOffset g N m n k h)) = 0 := by
      apply sum_eq_zero
      intro h hh
      have hhB := (mem_Icc.mp hh).2
      have hpos : ¬ k * n + h ≤ N := by omega
      have hneg : ¬ (h < k * n ∧ k * n - h ≤ N) := by omega
      simp only [positiveUpwardOffset, negativeUpwardOffset, if_neg hpos, if_neg hneg, add_zero]
    rw [hzero, mul_zero]

/-- Exact finite-source normalization of the literal upward Ramanujan row. -/
theorem sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width {φ : ℝ → ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N n : ℕ} (hn : n ∈ Icc 1 N) (hw : c / N ≤ 1) (m : ℕ) :
    Real.sqrt n * (upwardPrimeRow (atomDilate φ (c / N)) N
      (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
        (∫ u, atomDilate φ (c / N) u ^ 2)) =
      logarithmicUpwardCoefficient φ c (linearPrimeStrip c) N m n := by
  have hN : 1 ≤ N := (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := by
    intro u hu
    change φ (u / (c / N)) = 0
    apply hsupp
    intro hv
    apply hu
    refine ⟨?_, ?_⟩
    · simpa only [zero_mul] using (le_div_iff₀ (div_pos hc hN0)).mp hv.1
    · simpa only [one_mul] using (div_le_iff₀ (div_pos hc hN0)).mp hv.2
  have hterm (k : ℕ) (hk : k ∈ Icc 1 (N + linearPrimeStrip c)) (h : ℕ)
      (hh : h ∈ Icc 1 (linearPrimeStrip c)) :
      Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
        (positiveUpwardOffset (atomDilate φ (c / N)) N m n k h +
          negativeUpwardOffset (atomDilate φ (c / N)) N m n k h) /
          (∫ u, atomDilate φ (c / N) u ^ 2)) =
      1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
        logarithmicUpwardOffset φ c N m n k h) := by
    have hk1 := (mem_Icc.mp hk).1
    have hn1 := (mem_Icc.mp hn).1
    have hh1 := (mem_Icc.mp hh).1
    have hp : Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
        positiveUpwardOffset (atomDilate φ (c / N)) N m n k h /
          (∫ u, atomDilate φ (c / N) u ^ 2)) =
        1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
          (if k * n + h ≤ N then ramanujanLagCoefficient m (k * n + h) *
            logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0)) := by
      dsimp only [positiveUpwardOffset]
      split_ifs
      · simpa only [mul_assoc] using sqrt_mul_upward_offset_factor hc hN hk1 hn1
          (show 1 ≤ k * n + h by omega) m
      · simp only [mul_zero, zero_div]
    have hm : Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
        negativeUpwardOffset (atomDilate φ (c / N)) N m n k h /
          (∫ u, atomDilate φ (c / N) u ^ 2)) =
        1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
          (if h < k * n ∧ k * n - h ≤ N then ramanujanLagCoefficient m (k * n - h) *
            logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0)) := by
      dsimp only [negativeUpwardOffset]
      split_ifs with hhT
      · simpa only [mul_assoc] using sqrt_mul_upward_offset_factor hc hN hk1 hn1
          (show 1 ≤ k * n - h by omega) m
      · simp only [mul_zero, zero_div]
    dsimp only [logarithmicUpwardOffset]
    linear_combination hp + hm
  rw [upwardRamanujanRow_eq_offsets_small_width hc hn hg hw, logarithmicUpwardCoefficient]
  simp only [sum_div, mul_sum]
  exact sum_congr rfl fun k hk => sum_congr rfl fun h hh => hterm k hk h hh

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.upwardRamanujanRow_eq_offsets_small_width
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.upward_product_distance_le_small_width
