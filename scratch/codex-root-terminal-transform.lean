import GaloisForLFunctions.RHTower.MobiusDivisorSquareRootTerminalOrder
import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreInterpolation

noncomputable section
open Finset
namespace RHTower

def mobiusDivisorCriticalChildSource (M p : ℕ) : ℝ :=
  (1 - divisorPrimeClipWeight M p) *
      (∑ d ∈ Icc 1 (M / p), mobiusDivisorDilationChannel (M / p) d) +
    divisorPrimeClipWeight M p *
      (∑ d ∈ Icc 1 (M / p + 1), mobiusDivisorDilationChannel (M / p + 1) d)

private theorem selectionPrimes_mono {a b : ℕ} (hab : a ≤ b) :
    mobiusDivisorSelectionPrimes a ⊆ mobiusDivisorSelectionPrimes b := by
  intro q hq
  obtain ⟨hq, hprime⟩ := mem_filter.mp hq
  exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hq).trans_le hab), hprime⟩

private theorem sqrt_core_terminal (M B : ℕ) (hMB : M < B ^ (2 : ℕ)) :
    mobiusDivisorSmallSelectionPrimes M ⊆ mobiusDivisorSelectionPrimes B := by
  intro q hq
  obtain ⟨hq, hsmall⟩ := mem_filter.mp hq
  obtain ⟨hqM, hprime⟩ := mem_filter.mp hq
  have hqB : q < B := by
    by_contra h
    have hBq : B ≤ q := le_of_not_gt h
    nlinarith only [hMB, hsmall, hBq, sq_nonneg (q - B)]
  exact mem_filter.mpr ⟨mem_range.mpr hqB, hprime⟩

private theorem remaining_prime_child_covered
    (M B : ℕ) (hMB : M < B ^ (2 : ℕ))
    {p : ℕ} (hp : p ∈ mobiusDivisorSelectionPrimes M \
      mobiusDivisorSelectionPrimes B) :
    mobiusDivisorSelectionPrimes (M / p + 1) ⊆
      mobiusDivisorSelectionPrimes B := by
  obtain ⟨hpM, hpB⟩ := mem_sdiff.mp hp
  obtain ⟨hpmem, hprime⟩ := mem_filter.mp hpM
  have hpge : B ≤ p := by
    by_contra h
    exact hpB (mem_filter.mpr ⟨mem_range.mpr (by omega), hprime⟩)
  have hquot : M / p + 1 ≤ B := by
    have hmul : M < B * p := by nlinarith only [hMB, hpge, sq_nonneg (p - B)]
    have hh : M / p < B := (Nat.div_lt_iff_lt_mul hprime.pos).mpr
      (by simpa only [Nat.mul_comm] using hmul)
    omega
  exact selectionPrimes_mono hquot

theorem mobiusDivisorSelectionFibre_sqrtCore_eq_criticalChild
    (M B : ℕ) (hMB : M < B ^ (2 : ℕ))
    {p : ℕ} (hp : p ∈ mobiusDivisorSelectionPrimes M \
      mobiusDivisorSelectionPrimes B) :
    mobiusDivisorSelectionFibre M (mobiusDivisorSelectionPrimes B) {p} =
      -Real.sqrt p * mobiusDivisorCriticalChildSource M p := by
  obtain ⟨hpM, hpB⟩ := mem_sdiff.mp hp
  have hprime := (mem_filter.mp hpM).2
  have hcover1 := remaining_prime_child_covered M B hMB hp
  have hcover0 : mobiusDivisorSelectionPrimes (M / p) ⊆
      mobiusDivisorSelectionPrimes B :=
    (selectionPrimes_mono (Nat.le_succ _)).trans hcover1
  have hF0 := mobiusDivisorSelectionFibre_of_all_source_primes_processed
    (M / p) (mobiusDivisorSelectionPrimes B) ∅ hcover0
  have hF1 := mobiusDivisorSelectionFibre_of_all_source_primes_processed
    (M / p + 1) (mobiusDivisorSelectionPrimes B) ∅ hcover1
  simp only [if_true] at hF0 hF1
  rw [show ({p} : Finset ℕ) = insert p ∅ by rfl,
    mobiusDivisorSelectionFibre_prime_interpolation hprime M
      (mobiusDivisorSelectionPrimes B) ∅ hpB (by simp)]
  simp only [mobiusDivisorInterpolatedFibre, mobiusDivisorCriticalChildSource]
  rw [hF0, hF1]

theorem mobiusDivisorSelectionEnergy_sqrtCore_criticalTransform
    (M B : ℕ) (hMB : M < B ^ (2 : ℕ)) :
    let P := mobiusDivisorSelectionPrimes B
    let U := mobiusDivisorSelectionPrimes M \
      P
    let S := ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d
    mobiusDivisorSelectionEnergy M P =
      (S + ∑ p ∈ U, Real.sqrt p * mobiusDivisorCriticalChildSource M p) ^ (2 : ℕ) +
        ∑ p ∈ U, (p : ℝ) * (mobiusDivisorCriticalChildSource M p) ^ (2 : ℕ) := by
  dsimp only
  let P := mobiusDivisorSelectionPrimes B
  let U := mobiusDivisorSelectionPrimes M \
    P
  let S := ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d
  have hterminal := sqrt_core_terminal M B hMB
  have hsum := mobiusDivisorSelectionHead_add_terminal_leaves M P hterminal
  have hleaf (p : ℕ) (hp : p ∈ U) :
      mobiusDivisorSelectionFibre M P {p} =
        -Real.sqrt p * mobiusDivisorCriticalChildSource M p :=
    mobiusDivisorSelectionFibre_sqrtCore_eq_criticalChild M B hMB hp
  have hsum' : mobiusDivisorSelectionFibre M P ∅ =
      S + ∑ p ∈ U, Real.sqrt p * mobiusDivisorCriticalChildSource M p := by
    rw [sum_congr rfl hleaf] at hsum
    have hneg : (∑ p ∈ U, -Real.sqrt p * mobiusDivisorCriticalChildSource M p) =
        -(∑ p ∈ U, Real.sqrt p * mobiusDivisorCriticalChildSource M p) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro p hp
      ring
    rw [hneg] at hsum
    linarith only [hsum]
  rw [mobiusDivisorSelectionEnergy_terminal M P hterminal, hsum']
  congr 1
  apply sum_congr rfl
  intro p hp
  rw [hleaf p hp, neg_mul, even_two.neg_pow, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg p)]

end RHTower
