import GaloisForLFunctions.RHTower.MobiusDivisorCriticalChildAbelMellinWeld
import GaloisForLFunctions.RHTower.MobiusDivisorTerminalCriticalSourceTransform

noncomputable section
open Finset
namespace RHTower

private theorem adaptive_selectionPrimes_mono {a b : ℕ} (hab : a ≤ b) :
    mobiusDivisorSelectionPrimes a ⊆ mobiusDivisorSelectionPrimes b := by
  intro q hq
  obtain ⟨hq, hprime⟩ := mem_filter.mp hq
  exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hq).trans_le hab), hprime⟩

private theorem adaptive_terminal_small_subset (M : ℕ) (P : Finset ℕ)
    (hcover : ∀ p ∈ mobiusDivisorSelectionPrimes M, p * p ≤ M → p ∈ P) :
    mobiusDivisorSmallSelectionPrimes M ⊆ P := by
  intro p hp
  obtain ⟨hpM, hpsq⟩ := mem_filter.mp hp
  exact hcover p hpM hpsq.le

private theorem adaptive_terminal_child_covered (M : ℕ) (P : Finset ℕ)
    (hcover : ∀ p ∈ mobiusDivisorSelectionPrimes M, p * p ≤ M → p ∈ P)
    {p : ℕ} (hp : p ∈ mobiusDivisorSelectionPrimes M \ P) :
    mobiusDivisorSelectionPrimes (M / p + 1) ⊆ P := by
  obtain ⟨hpM, hpP⟩ := mem_sdiff.mp hp
  have hprime : p.Prime := (mem_filter.mp hpM).2
  have hpsq : M < p * p := by
    by_contra hn
    exact hpP (hcover p hpM (Nat.le_of_not_gt hn))
  have hdiv : M / p < p :=
    (Nat.div_lt_iff_lt_mul hprime.pos).mpr (by simpa [mul_comm] using hpsq)
  intro q hq
  have hqprime : q.Prime := (mem_filter.mp hq).2
  have hqdiv : q ≤ M / p := by
    have := mem_range.mp (mem_filter.mp hq).1
    omega
  have hqM : q < M := by
    have hm := Nat.div_mul_le_self M p
    have hpos : 2 ≤ q := hqprime.two_le
    nlinarith
  have hqsq : q * q ≤ M := by
    have hm := Nat.div_mul_le_self M p
    nlinarith
  exact hcover q (mem_filter.mpr ⟨mem_range.mpr hqM, hqprime⟩) hqsq

theorem adaptive_terminal_singleton_source (M : ℕ) (P : Finset ℕ)
    (hcover : ∀ p ∈ mobiusDivisorSelectionPrimes M, p * p ≤ M → p ∈ P)
    {p : ℕ} (hp : p ∈ mobiusDivisorSelectionPrimes M \ P) :
    mobiusDivisorSelectionFibre M P {p} =
      -Real.sqrt p * criticalContinuousAbel ((M : ℝ) / p) := by
  obtain ⟨hpM, hpP⟩ := mem_sdiff.mp hp
  have hprime : p.Prime := (mem_filter.mp hpM).2
  have hq1 : 1 ≤ M / p :=
    (Nat.le_div_iff_mul_le hprime.pos).mpr (by have := mem_range.mp (mem_filter.mp hpM).1; omega)
  have hcover1 := adaptive_terminal_child_covered M P hcover hp
  have hcover0 : mobiusDivisorSelectionPrimes (M / p) ⊆ P :=
    (adaptive_selectionPrimes_mono (Nat.le_succ _)).trans hcover1
  have hF0 := mobiusDivisorSelectionFibre_of_all_source_primes_processed
    (M / p) P ∅ hcover0
  have hF1 := mobiusDivisorSelectionFibre_of_all_source_primes_processed
    (M / p + 1) P ∅ hcover1
  simp only [if_true] at hF0 hF1
  rw [show ({p} : Finset ℕ) = insert p ∅ by rfl,
    mobiusDivisorSelectionFibre_prime_interpolation hprime M P ∅ hpP (by simp)]
  simp only [mobiusDivisorInterpolatedFibre]
  rw [hF0, hF1]
  change -Real.sqrt p * mobiusDivisorCriticalChildSource M p = _
  rw [criticalChild_eq_criticalContinuousAbel M p hprime.pos hq1]

theorem adaptive_terminal_head_source (M : ℕ) (P : Finset ℕ)
    (hcover : ∀ p ∈ mobiusDivisorSelectionPrimes M, p * p ≤ M → p ∈ P) :
    mobiusDivisorSelectionFibre M P ∅ =
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d) +
        ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
          Real.sqrt p * criticalContinuousAbel ((M : ℝ) / p) := by
  have hh := mobiusDivisorSelectionHead_add_terminal_leaves M P
    (adaptive_terminal_small_subset M P hcover)
  have hleaf : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P,
      mobiusDivisorSelectionFibre M P {p} =
        -Real.sqrt p * criticalContinuousAbel ((M : ℝ) / p) :=
    fun p hp => adaptive_terminal_singleton_source M P hcover hp
  rw [sum_congr rfl hleaf] at hh
  have hneg : (∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
      -Real.sqrt p * criticalContinuousAbel ((M : ℝ) / p)) =
      -(∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
        Real.sqrt p * criticalContinuousAbel ((M : ℝ) / p)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    ring
  rw [hneg] at hh
  linarith only [hh]

theorem adaptive_terminal_energy_source (M : ℕ) (P : Finset ℕ)
    (hcover : ∀ p ∈ mobiusDivisorSelectionPrimes M, p * p ≤ M → p ∈ P) :
    mobiusDivisorSelectionEnergy M P =
      ((∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d) +
        ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
          Real.sqrt p * criticalContinuousAbel ((M : ℝ) / p)) ^ (2 : ℕ) +
        ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
          (p : ℝ) * (criticalContinuousAbel ((M : ℝ) / p)) ^ (2 : ℕ) := by
  rw [mobiusDivisorSelectionEnergy_terminal M P
      (adaptive_terminal_small_subset M P hcover),
    adaptive_terminal_head_source M P hcover]
  congr 1
  apply sum_congr rfl
  intro p hp
  rw [adaptive_terminal_singleton_source M P hcover hp]
  rw [mul_pow, neg_sq, Real.sq_sqrt (Nat.cast_nonneg p)]

end RHTower
