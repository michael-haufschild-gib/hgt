import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormAtEveryOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNonRatioPrimeRowsSplitIntoDownwardAndUpward
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap

/-!
# The shell degree retains its position in the horizon

The weighted non-ratio row is exactly `n` times the shell degree. Upward
prime windows cost `O(c)`; downward divisor windows cost
`O(c (n/N) (1 + log n))`. These bounds keep the terminal loss separate
from the cost on a fixed prefix.
-/

noncomputable section

open MeasureTheory Finset
open scoped Real

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis
  CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  ArithmeticLorentzianGeometry ArithmeticEffectivityTheory

private theorem nonRatio_entry_le_windows {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (n j : PrimeHorizonIndex N) :
    fullWeilNonRatioMatrix φ c N n j ≤
      ∑ k ∈ range (lagRange (Real.log N + c / N + 1)), RHTower.vonMangoldtAtom k *
        (upInd (c / N) k n j + upInd (c / N) k j n) := by
  have hN : 1 ≤ N := (mem_Icc.mp n.property).1.trans (mem_Icc.mp n.property).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ hsupp hw
  let g := atomDilate φ (c / N)
  let G := ∫ u, g u ^ 2
  let K := lagRange (Real.log N + c / N + 1)
  have hG : 0 < G := by
    dsimp only [G, g]
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have heq : fullWeilNonRatioMatrix φ c N n j =
      (primePair (atom g n) (atom g j) - G * weilPrimeKernel n j) / G := by
    rw [fullWeilNonRatioMatrix_apply]
    change primePair (atom g n) (atom g j) / G - weilPrimeKernel n j = _
    field_simp [hG.ne']
  have hsum := primePair_atom_sub_ratio_eq_tsum hgs hw.le n.property j.property
  have hfin : (∑' k : ℕ, RHTower.vonMangoldtAtom k *
      ((if (n : ℕ) = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) +
        (if (j : ℕ) = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))))) =
      ∑ k ∈ range K, RHTower.vonMangoldtAtom k *
      ((if (n : ℕ) = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) +
        (if (j : ℕ) = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) := by
    apply tsum_eq_sum
    intro k hk
    have hk' : K ≤ k := by simpa only [mem_range, not_lt] using hk
    obtain ⟨h1, h2⟩ := bumpCorr_lag_eq_zero hgs hw.le n.property j.property hk'
    rw [h1, h2]
    split_ifs <;> simp only [add_zero, mul_zero]
  rw [heq, hsum, hfin]
  apply (div_le_iff₀ hG).mpr
  rw [sum_mul]
  apply sum_le_sum
  intro k hk
  have hd := (le_abs_self _).trans (abs_nonRatio_term_le hg.continuous hgc hgs k j n)
  have hu := (le_abs_self _).trans (abs_nonRatio_term_le hg.continuous hgc hgs k n j)
  have h := mul_le_mul_of_nonneg_left (add_le_add hd hu) (vonMangoldtAtom_nonneg' k)
  convert h using 1 <;> ring

/-- The shell degree is the Schur row with pole weights, divided by its row index. -/
theorem nat_mul_shellDegree_eq_weighted_row (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (n : PrimeHorizonIndex N) :
    (n : ℕ) * shellDegree φ c N n =
      ∑ j : PrimeHorizonIndex N, Real.sqrt ((n : ℝ) / j) * fullWeilNonRatioMatrix φ c N n j := by
  rw [shellDegree, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp n.property).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp j.property).1
  have hs := Real.mul_self_sqrt hn0.le
  rw [nonRatioWeight, Real.sqrt_div hn0.le]
  field_simp [(Real.sqrt_pos.mpr hn0).ne', (Real.sqrt_pos.mpr hj0).ne']
  nlinarith only [congrArg (fun t : ℝ => t * fullWeilNonRatioMatrix φ c N n j) hs]

/-- Both directed prime rows bound the literal shell degree at every positive overlap. -/
theorem nat_mul_shellDegree_le_nonRatioRow {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (n : PrimeHorizonIndex N) :
    (n : ℕ) * shellDegree φ c N n ≤ nonRatioRow (c / N) N n := by
  let K := lagRange (Real.log N + c / N + 1)
  have hN : 1 ≤ N := (mem_Icc.mp n.property).1.trans (mem_Icc.mp n.property).2
  have hw : 0 ≤ c / N := div_nonneg hc.le (Nat.cast_nonneg N)
  rw [nat_mul_shellDegree_eq_weighted_row]
  calc
    _ ≤ ∑ j : PrimeHorizonIndex N, Real.sqrt ((n : ℝ) / j) *
        (∑ k ∈ range K, RHTower.vonMangoldtAtom k *
          (upInd (c / N) k n j + upInd (c / N) k j n)) :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (nonRatio_entry_le_windows hφ hsupp hM hc n j) (Real.sqrt_nonneg _)
    _ = (∑ k ∈ range K, RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, Real.sqrt ((n : ℝ) / j) * upInd (c / N) k n j) +
        ∑ k ∈ range K, RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, Real.sqrt ((n : ℝ) / j) * upInd (c / N) k j n := by
      rw [sum_coe_sort]
      simp only [mul_sum, ← sum_add_distrib]
      rw [sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun j _ => by ring
    _ ≤ _ := add_le_add (up_row_le hw (mem_Icc.mp n.property).1 K)
      (down_row_le hw (mem_Icc.mp n.property).1 K)

/-- At `c≤N`, the shell cost is constant on the prefix and logarithmic near the terminal horizon. -/
theorem nat_mul_shellDegree_le_explicit {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hcN : c ≤ N) (n : PrimeHorizonIndex N) :
    (n : ℕ) * shellDegree φ c N n ≤
      2 * (Real.log 4 + 4) * Real.exp (5 / 2) * c +
        2 * Real.exp (3 / 2) * c * ((n : ℝ) / N) * (Real.log n + 1) := by
  have hN : 1 ≤ N := (mem_Icc.mp n.property).1.trans (mem_Icc.mp n.property).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact (nat_mul_shellDegree_le_nonRatioRow hφ hsupp hM hc n).trans
    (nonRatioRow_le_of_ratio hN (div_nonneg hc.le hN0.le)
      ((div_le_one hN0).mpr hcN) le_rfl (mem_Icc.mp n.property).1)

/-- Nonnegative profiles have nonnegative shell degree. -/
theorem shellDegree_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (n : PrimeHorizonIndex N) :
    0 ≤ shellDegree φ c N n :=
  sum_nonneg fun j _ => nonRatioWeight_nonneg hφ0 hsupp hM hc n j

/-- The shell payment on any packet is bounded by its harmonic mass and a terminal logarithmic mass. -/
theorem shellDegree_packet_payment_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hcN : c ≤ N) (F : ℕ → ℝ) :
    (∑ n : PrimeHorizonIndex N, shellDegree φ c N n * F n ^ 2) ≤
      2 * (Real.log 4 + 4) * Real.exp (5 / 2) * c *
          (∑ n : PrimeHorizonIndex N, F n ^ 2 / n) +
        (2 * Real.exp (3 / 2) * c / N) *
          ∑ n : PrimeHorizonIndex N, F n ^ 2 * (Real.log n + 1) := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp n.property).1
  have hN0 : (0 : ℝ) < N := hc.trans_le hcN
  have h := nat_mul_shellDegree_le_explicit hφ hsupp hM hc hcN n
  have hd : shellDegree φ c N n ≤
      (2 * (Real.log 4 + 4) * Real.exp (5 / 2) * c +
        2 * Real.exp (3 / 2) * c * ((n : ℝ) / N) * (Real.log n + 1)) / n :=
    (le_div_iff₀ hn0).mpr (by simpa only [mul_comm] using h)
  have hp := mul_le_mul_of_nonneg_right hd (sq_nonneg (F n))
  convert hp using 1 <;> field_simp [hn0.ne', hN0.ne'] <;> ring

end GaloisForLFunctions.ArithmeticCouplingTheory

#print axioms GaloisForLFunctions.ArithmeticCouplingTheory.nat_mul_shellDegree_le_explicit
#print axioms GaloisForLFunctions.ArithmeticCouplingTheory.shellDegree_packet_payment_le
