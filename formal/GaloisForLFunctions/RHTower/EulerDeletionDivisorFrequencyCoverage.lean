import GaloisForLFunctions.RHTower.EulerDeletionDivisorFrequencyBoundary
import Mathlib.NumberTheory.Bertrand

/-!
# Every large EDQ cutoff has a negative divisor-frequency coefficient

For `m <= N < 2*m`, the frequency `4*m` has the exact coefficient
`1 - 2*mu(2*m)`. Squarefree divisor support makes this coefficient constant
throughout the cutoff band. Odd primes give value minus one.

The large-argument form of Bertrand's theorem then places a negative
coefficient in `[2*N+2, 4*N]` at every cutoff `N >= 1024`. Consequently,
selecting a cofinal sequence of cutoffs cannot recover nonnegativity at
all frequencies. The earlier positive band through `2*N+1` is retained.

This is a coefficient classification, not a bound for the complete signed
physical source. It does not prove RH or the analytic Estermann transfer.
-/

open Finset ArithmeticFunction
noncomputable section
namespace RHTower.DeletionDivisorFrequency

/-- Squarefree divisor support makes the coefficient constant on the whole cutoff band. -/
theorem coeff_four_mul_plateau {N m : ℕ} (hm : m ≤ N) (hN : N < 2*m) :
    coeff N (4*m) = coeff (2*m-1) (4*m) := by
  have hm0 : m ≠ 0 := by omega
  simp only [coeff]
  apply sum_congr rfl
  intro d hd
  by_cases hdN : d ≤ N
  · simp [hdN, show d ≤ 2*m-1 by omega]
  · by_cases hdt : d ≤ 2*m-1
    · have hzero : moebius d = 0 := by
        by_contra hnonzero
        have hs : Squarefree d := moebius_ne_zero_iff_squarefree.mp hnonzero
        have hd4 : d ∣ 4*m := (Nat.mem_divisors.mp hd).1
        have hdPow : d ∣ (2*m)^(2 : ℕ) := hd4.trans ⟨m, by ring⟩
        have hd2 : d ∣ 2*m := (hs.dvd_pow_iff_dvd (by omega : 2 ≠ 0)).mp hdPow
        have hproper : d ∈ (2*m).properDivisors :=
          Nat.mem_properDivisors.mpr ⟨hd2, by omega⟩
        obtain ⟨k, hk, he⟩ :=
          (Nat.mem_properDivisors_iff_exists (by omega : 2*m ≠ 0)).mp hproper
        have hdm : d ≤ m := by nlinarith
        exact hdN (hdm.trans hm)
      simp [hdN, hdt, hzero]
    · simp [hdN, hdt]

private theorem moebius_four_mul (m : ℕ) : moebius (4*m) = 0 := by
  apply moebius_eq_zero_of_not_squarefree
  intro hs
  have hs4 : Squarefree (4 : ℕ) := hs.squarefree_of_dvd (dvd_mul_right 4 m)
  have hn : moebius 4 ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hs4
  have hz : moebius 4 = 0 := by
    have he := moebius_apply_prime_pow (k := 2) Nat.prime_two (by omega)
    simpa using he
  exact hn hz

/-- Exact coefficient throughout the cutoff band; all signs are retained. -/
theorem coeff_four_mul_band {N m : ℕ} (hm2 : 2 ≤ m) (hm : m ≤ N)
    (hN : N < 2*m) : coeff N (4*m) = 1 - 2*moebius (2*m) := by
  rw [coeff_four_mul_plateau hm hN]
  have h := coeff_even_second_band (N := 2*m-1) (m := 2*m) (by omega) (by omega)
  rw [show 2*(2*m) = 4*m by omega, moebius_four_mul] at h
  simpa using h

/-- Every odd prime produces a full band of cutoffs with coefficient minus one. -/
theorem coeff_prime_band {N p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpN : p ≤ N) (hNp : N < 2*p) : coeff N (4*p) = -1 := by
  rw [coeff_four_mul_plateau hpN hNp]
  exact coeff_prime_boundary hp hp3

/-- Every sufficiently large cutoff has a negative coefficient within four times its size. -/
theorem negative_frequency_every_large_cutoff (N : ℕ) (hN : 1024 ≤ N) :
    ∃ l : ℕ, 2*N+2 ≤ l ∧ l ≤ 4*N ∧ coeff N l = -1 := by
  obtain ⟨p, hp, hplow, hpup⟩ :=
    Nat.exists_prime_lt_and_le_two_mul_eventually (N/2) (by omega)
  have hp3 : 3 ≤ p := by omega
  have hpN : p ≤ N := by omega
  have hNp : N < 2*p := by omega
  exact ⟨4*p, by omega, by omega, coeff_prime_band hp hp3 hpN hNp⟩

/-- There is no cofinal choice of cutoffs with nonnegative coefficients at every frequency. -/
theorem not_cofinal_all_frequency_nonnegative :
    ¬ (∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧ ∀ l : ℕ, 0 ≤ coeff N l) := by
  intro h
  obtain ⟨N, hN, hpos⟩ := h 1024
  obtain ⟨l, _, _, hl⟩ := negative_frequency_every_large_cutoff N hN
  have hh := hpos l
  rw [hl] at hh
  omega

end RHTower.DeletionDivisorFrequency
