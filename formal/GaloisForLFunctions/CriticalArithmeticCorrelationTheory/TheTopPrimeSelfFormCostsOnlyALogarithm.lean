import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AsymmetricTwoRegionConductorReserve
import Zeta23.FromPNTPlus.Mertens

/-!
# The prime self-form of the overlapping top costs `c (1 + log c)`

Let `M = N / L_c` with `L_c = linearDefectCutoff c`, and let `y` live on the top `(M, N]`. Two top
atoms are paired by the prime lag `log k` only when their ratio is within `e^w` of `k`, so
`k ≤ e L_c`, and the integers `n` with `kn` in a window of radius `R` number at most `2R/k + 1`
(`card_mul_near_le`). A Schur test with the Perron weights `n^{−1/2}`, applied to the full window
(the ratio lag and the non-ratio lags together), bounds the prime form of the top atomic test by
`O(c (1 + log c))` times its mass (`abs_primeSum_top_le`). The non-ratio rows alone were known
with `O(c²)`; the gain is that a prime power `k > 2ec` meets a window of width `2ec` at most once.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset ArithmeticFunction
open scoped BigOperators

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics RHTower

/-! ### Counting multiples in a window -/

/-- At most `B − A + 1` naturals lie in a real interval `[A, B]`. -/
theorem card_filter_mem_Icc_real_le (s : Finset ℕ) {A B : ℝ} (hAB : A ≤ B) :
    ((s.filter fun n => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B).card : ℝ) ≤ B - A + 1 := by
  rcases lt_or_ge B 0 with hB | hB
  · have hempty : (s.filter fun n => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B) = ∅ :=
      filter_eq_empty_iff.mpr fun n _ h => absurd (h.2.trans_lt hB) (not_lt.mpr n.cast_nonneg)
    rw [hempty, card_empty, Nat.cast_zero]; linarith
  have hsub : (s.filter fun n => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B) ⊆ Icc ⌈A⌉₊ ⌊B⌋₊ := fun n hn =>
    mem_Icc.mpr ⟨Nat.ceil_le.mpr (mem_filter.mp hn).2.1, Nat.le_floor (mem_filter.mp hn).2.2⟩
  have hcard : ((s.filter fun n => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B).card : ℝ) ≤ (⌊B⌋₊ + 1 - ⌈A⌉₊ : ℕ) := by
    exact_mod_cast (card_le_card hsub).trans_eq (Nat.card_Icc _ _)
  have hceil : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  have hfloor : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
  refine hcard.trans ?_
  rcases le_or_gt ⌈A⌉₊ (⌊B⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h]; push_cast; linarith
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]; linarith

/-- At most `2R/k + 1` naturals `n` have `kn` within `R` of a point. -/
theorem card_mul_near_le (s : Finset ℕ) {k : ℕ} (hk : 1 ≤ k) (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ((s.filter fun n => |(k : ℝ) * n - a| ≤ R).card : ℝ) ≤ 2 * R / k + 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hAB : (a - R) / k ≤ (a + R) / k := div_le_div_of_nonneg_right (by linarith) hk0.le
  have hsub : (s.filter fun n => |(k : ℝ) * n - a| ≤ R) ⊆
      s.filter fun n => (a - R) / k ≤ (n : ℝ) ∧ (n : ℝ) ≤ (a + R) / k := by
    intro n hn
    obtain ⟨hs, h⟩ := mem_filter.mp hn
    obtain ⟨h1, h2⟩ := abs_le.mp h
    refine mem_filter.mpr ⟨hs, ?_, ?_⟩
    · rw [div_le_iff₀ hk0]; linarith
    · rw [le_div_iff₀ hk0]; linarith
  refine (Nat.cast_le.mpr (card_le_card hsub)).trans
    ((card_filter_mem_Icc_real_le s hAB).trans_eq ?_)
  field_simp
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
