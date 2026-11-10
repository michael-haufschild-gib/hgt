import GaloisForLFunctions.HyperbolicArakelovTheory.TheContinuumPrimeGreenChannel
import GaloisForLFunctions.ArithmeticOrientationTheory.PrimePowerSumsRegroupByTowers
import GaloisForLFunctions.RHTower.WeilMarkovPoleCapacity

/-!
# The prime sum from continuum Green channels

Compact support makes the prime-power correlations finite simultaneously in
the prime and its exponent. Regrouping the von Mangoldt sum then identifies
the complete correlation of the translated Green channels with Weil's prime
term, without any separation condition on the packet.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Classical BigOperators ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm

private theorem sum_Icc_one_eq_sum_range (g : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, g k) = ∑ k ∈ Finset.range N, g (k + 1) := by
  induction N with
  | zero => simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
      Finset.range_zero, Finset.sum_empty]
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private theorem atom_eq (n : ℕ) : vonMangoldtAtom n = Λ n / Real.sqrt n := by
  by_cases hn : 2 ≤ n
  · exact if_pos hn
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> simp [vonMangoldtAtom]

private theorem primeSum_eq_tsum (f : ℝ → ℝ) :
    primeSum f = ∑' n : ℕ, Λ n * (2 * autocorr f (Real.log n) / Real.sqrt n) := by
  apply tsum_congr
  intro n
  rw [atom_eq]
  have hn : (∫ t, f t * f (t - Real.log n)) = autocorr f (-Real.log n) := by
    simp only [autocorr, sub_eq_add_neg]
  rw [hn, autocorr_neg]
  change _ * (autocorr f (Real.log n) + autocorr f (Real.log n)) = _
  ring

private theorem tower_entry {p e : ℕ} (hp : p.Prime) (he : 0 < e) (f : ℝ → ℝ) :
    Λ (p ^ e) * (2 * autocorr f (Real.log (p ^ e : ℕ)) / Real.sqrt (p ^ e : ℕ)) =
      2 * Real.log p * ((1 / Real.sqrt p) ^ e * autocorr f ((e : ℝ) * Real.log p)) := by
  have hsq : Real.sqrt ((p : ℝ) ^ e) = Real.sqrt p ^ e := by
    rw [show (p : ℝ) ^ e = (Real.sqrt p ^ e) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg p)]]
    exact Real.sqrt_sq (by positivity)
  rw [ArithmeticFunction.vonMangoldt_apply_pow he.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, hsq, Real.log_pow,
    one_div_pow]
  ring

private theorem primeCorrelation_eq_tower {p N : ℕ} (hp : p.Prime) {f : ℝ → ℝ}
    (hcut : ∀ n : ℕ, N < n → autocorr f (Real.log n) = 0) :
    primeCorrelation p f = ∑ e ∈ Finset.Icc 1 (p.log N),
      Λ (p ^ e) * (2 * autocorr f (Real.log (p ^ e : ℕ)) / Real.sqrt (p ^ e : ℕ)) := by
  have hs : Function.support (correlationCoefficient p f) ⊆
      (Finset.range (p.log N) : Set ℕ) := by
    intro k hk
    by_contra hmem
    have hkN : p.log N ≤ k := by
      simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
    have hpow : N < p ^ (k + 1) := by
      by_contra h
      have := Nat.le_log_of_pow_le hp.one_lt (not_lt.mp h)
      omega
    have hz := hcut (p ^ (k + 1)) hpow
    rw [Nat.cast_pow, Real.log_pow] at hz
    exact hk (by rw [correlationCoefficient, hz, mul_zero])
  rw [primeCorrelation, finsum_eq_sum_of_support_subset _ hs, Finset.mul_sum,
    sum_Icc_one_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  exact (tower_entry hp (Nat.succ_pos k) f).symm

private theorem primeCorrelation_eq_zero_above {p N : ℕ} (hp : p.Prime) (hNp : N < p)
    {f : ℝ → ℝ} (hcut : ∀ n : ℕ, N < n → autocorr f (Real.log n) = 0) :
    primeCorrelation p f = 0 := by
  have hz (k : ℕ) : correlationCoefficient p f k = 0 := by
    have hpk : p ≤ p ^ (k + 1) :=
      Nat.le_of_dvd (pow_pos hp.pos _) (dvd_pow_self p (Nat.succ_ne_zero k))
    have h := hcut (p ^ (k + 1)) (hNp.trans_le hpk)
    rw [Nat.cast_pow, Real.log_pow] at h
    rw [correlationCoefficient, h, mul_zero]
  simp only [primeCorrelation, hz, finsum_zero, mul_zero]

/-- One finite prime horizon captures the complete continuum correlation of a compact packet. -/
theorem primeSum_eq_finite_channels {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ N : ℕ,
      primeSum f = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, primeCorrelation p f ∧
      ∀ p : ℕ, p.Prime → N < p → primeCorrelation p f = 0 := by
  obtain ⟨N, hN⟩ := _root_.RHTower.WeilMarkovPole.exists_level hfc
  have hcut (n : ℕ) (hn : N < n) : autocorr f (Real.log n) = 0 := by
    simp only [autocorr, hN n hn, integral_zero]
  refine ⟨N, ?_, fun p hp hNp => primeCorrelation_eq_zero_above hp hNp hcut⟩
  rw [primeSum_eq_tsum]
  have hs : (∑' n : ℕ, Λ n * (2 * autocorr f (Real.log n) / Real.sqrt n)) =
      ∑ n ∈ Finset.Icc 1 N, Λ n * (2 * autocorr f (Real.log n) / Real.sqrt n) := by
    apply tsum_eq_sum
    intro n hn
    by_cases hn0 : n = 0
    · subst n; simp
    · have hNn : N < n := by
        have := hn
        simp only [Finset.mem_Icc, not_and, not_le] at this
        exact this (by omega)
      rw [hcut n hNn, mul_zero, zero_div, mul_zero]
  rw [hs, ArithmeticOrientationTheory.sum_vonMangoldt_mul_eq_sum_towers]
  apply Finset.sum_congr rfl
  intro p hp
  exact (primeCorrelation_eq_tower (Finset.mem_filter.mp hp).2 hcut).symm

#print axioms primeSum_eq_finite_channels

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
