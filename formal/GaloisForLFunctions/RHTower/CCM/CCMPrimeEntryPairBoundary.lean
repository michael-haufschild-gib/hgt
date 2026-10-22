import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitPairEnergy

/-!
# The rank-two boundary correction of the full prime-pair energy

After the final prime entry, a finite sum of tents is affine. Its omitted
infinite tail is therefore exactly a sum of two squares of arithmetic
charges. This is the full correction between the limiting overlap matrix
and its finite-time restriction, including every off-diagonal interaction.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

def ccmPrimeEntryPairLimit (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m *
      ccmPrimeEntryOverlapLimit (Real.log n) (Real.log m)

def ccmPrimeEntryPairBoundary (T : ℝ) : ℝ :=
  Real.exp (-T) *
    ((ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T + Chebyshev.psi (Real.exp T)) ^ 2 +
      Chebyshev.psi (Real.exp T) ^ 2)

theorem ccmPrimeEntryPairBoundary_nonneg (T : ℝ) : 0 ≤ ccmPrimeEntryPairBoundary T := by
  unfold ccmPrimeEntryPairBoundary
  positivity

private theorem terminal_log_bounds {T : ℝ} {n : ℕ}
    (hn : n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) : 0 ≤ Real.log n ∧ Real.log n ≤ T := by
  obtain ⟨hn1, hnT⟩ := Finset.mem_Icc.mp hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  exact ⟨Real.log_nonneg hnR, (Real.log_le_iff_le_exp (zero_lt_one.trans_le hnR)).mpr
    ((Nat.le_floor_iff (Real.exp_pos T).le).mp hnT)⟩

private theorem boundary_sum_eq (T : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, ∑ m ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
      ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m *
        ((T - Real.log n) * (T - Real.log m) + 2 * T - Real.log n - Real.log m + 2)) =
      (ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T + Chebyshev.psi (Real.exp T)) ^ 2 +
        Chebyshev.psi (Real.exp T) ^ 2 := by
  let S := Finset.Icc 1 ⌊Real.exp T⌋₊
  have hpsi : Chebyshev.psi (Real.exp T) = ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := by
    simp only [S, Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  have hsum : ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T + Chebyshev.psi (Real.exp T) =
      ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * (T - Real.log n + 1) := by
    rw [ccmPrimeEntryPrefix, hpsi]
    change (∑ n ∈ S, ArithmeticFunction.vonMangoldt n * ccmPrimeEntryTent (Real.log n) T) +
      (∑ n ∈ S, ArithmeticFunction.vonMangoldt n) = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ccmPrimeEntryTent, max_eq_left (sub_nonneg.mpr (terminal_log_bounds hn).2)]
    ring
  rw [hsum, hpsi]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The complete omitted tail has rank two: its two arithmetic coordinates
are the terminal prefix plus psi, and psi itself. -/
theorem ccmPrimeEntryPairPrefix_eq_limit_sub_boundary (T : ℝ) :
    ccmPrimeEntryPairPrefix T ⌊Real.exp T⌋₊ =
      ccmPrimeEntryPairLimit ⌊Real.exp T⌋₊ - ccmPrimeEntryPairBoundary T := by
  let S := Finset.Icc 1 ⌊Real.exp T⌋₊
  calc
    _ = ∑ n ∈ S, ∑ m ∈ S,
        (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m *
          ccmPrimeEntryOverlapLimit (Real.log n) (Real.log m) -
        Real.exp (-T) * (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m *
          ((T - Real.log n) * (T - Real.log m) + 2 * T - Real.log n - Real.log m + 2))) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      obtain ⟨hn0, hnT⟩ := terminal_log_bounds hn
      obtain ⟨_, hmT⟩ := terminal_log_bounds hm
      rw [ccmPrimeEntryOverlap_eq (hn0.trans (le_max_left _ _)) hnT hmT]
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [show (∑ n ∈ S, ∑ m ∈ S, ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m *
        ((T - Real.log n) * (T - Real.log m) + 2 * T - Real.log n - Real.log m + 2)) =
          (ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T + Chebyshev.psi (Real.exp T)) ^ 2 +
            Chebyshev.psi (Real.exp T) ^ 2 from boundary_sum_eq T]
      rfl

/-- The limiting pair matrix enters the actual centered energy only after
subtracting its complete two-charge boundary term. -/
theorem ccmPrimeDeficitCriticalEnergy_integral_eq_pair_limit {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
      Real.exp T - Real.exp (-T) - 2 * T -
        2 * ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ +
          ccmPrimeEntryPairLimit ⌊Real.exp T⌋₊ - ccmPrimeEntryPairBoundary T := by
  rw [ccmPrimeDeficitCriticalEnergy_integral_eq_pair hT,
    ccmPrimeEntryPairPrefix_eq_limit_sub_boundary]
  ring

end RHTower
