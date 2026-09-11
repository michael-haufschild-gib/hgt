import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Convert

/-!
# Sharp sign boundary of the EDQ divisor-frequency coefficient

The actual finite coefficient exposed by Estermann frequency regrouping is
`coeff N n = sum_{d | n, d <= N} mu(d) * tau(n/d)`.
Complete convolution is one. Up to `2*N+1`, the only omitted divisor can be
`n` itself, giving a nonnegative coefficient. At cofinally many cutoffs the
very next coefficient is negative: `N = 2*p-1`, `n = 4*p` for primes `p >= 3`.

`sharp_cofinal_sign_boundary` closes both the positive interval and its exact
cofinal sharpness. This obstructs an all-frequency positivity argument. It
supplies no bound for the complete signed EDQ energy. The analytic
Estermann-to-physical-Gram representation is not proved in this module.
-/

open Finset ArithmeticFunction
noncomputable section
namespace RHTower.DeletionDivisorFrequency

/-- Divisor count as the convolution of two constant-one arithmetic functions. -/
def divisorCount : ArithmeticFunction ℤ :=
  (zeta : ArithmeticFunction ℤ) * (zeta : ArithmeticFunction ℤ)

/-- Agreement with the literal number of divisors, including the zero convention. -/
theorem divisorCount_eq_card (n : ℕ) : divisorCount n = (n.divisors.card : ℤ) := by
  rw [divisorCount, coe_zeta_mul_apply]
  trans ∑ _d ∈ n.divisors, (1 : ℤ)
  · apply sum_congr rfl
    intro d hd
    simp [natCoe_apply, (Nat.pos_of_mem_divisors hd).ne']
  · simp

/-- Möbius cutoff against the full divisor count of the complementary factor. -/
def coeff (N n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, if d ≤ N then moebius d * divisorCount (n/d) else 0

/-- Completing the Möbius convolution yields the constant-one function. -/
theorem full_convolution (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, moebius d * divisorCount (n/d) = 1 := by
  have h : moebius * divisorCount = (zeta : ArithmeticFunction ℤ) := by
    rw [divisorCount, ← mul_assoc, moebius_mul_coe_zeta, one_mul]
  have he := congrArg (fun f : ArithmeticFunction ℤ => f n) h
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => moebius a * divisorCount b)] at he
  simpa only [natCoe_apply,
    zeta_apply_ne hn, Nat.cast_one] using he

/-- The finite head and its entire omitted-divisor contribution sum to one. -/
theorem coeff_add_omitted (N n : ℕ) (hn : n ≠ 0) :
    coeff N n + (∑ d ∈ n.divisors,
      if N < d then moebius d * divisorCount (n/d) else 0) = 1 := by
  rw [coeff, ← sum_add_distrib]
  convert full_convolution n hn using 1
  apply sum_congr rfl
  intro d hd
  by_cases h : d ≤ N <;> simp [h, Nat.not_lt_of_ge, Nat.lt_of_not_ge]

/-- No divisor is omitted below the cutoff. -/
theorem coeff_eq_one_of_le {N n : ℕ} (hn : n ≠ 0) (h : n ≤ N) :
    coeff N n = 1 := by
  convert full_convolution n hn using 1
  apply sum_congr rfl
  intro d hd
  have hdN : d ≤ N := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
    (Nat.mem_divisors.mp hd).1).trans h
  simp [hdN]

/-- Through twice the cutoff plus one, only the full index can be omitted. -/
theorem coeff_first_band {N n : ℕ} (hN : N < n) (hn : n ≤ 2*N+1) :
    coeff N n = 1 - moebius n := by
  have hn0 : n ≠ 0 := by omega
  have htail : (∑ d ∈ n.divisors,
      if N < d then moebius d * divisorCount (n/d) else 0) = moebius n := by
    rw [sum_eq_single n]
    · rw [if_pos hN, Nat.div_self (Nat.pos_of_ne_zero hn0)]
      simp [divisorCount_eq_card]
    · intro d hd hdn
      have hdvd := (Nat.mem_divisors.mp hd).1
      have hle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
      have hp : d ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨hdvd, by omega⟩
      obtain ⟨k, hk, he⟩ := (Nat.mem_properDivisors_iff_exists hn0).mp hp
      have hd2 : 2*d ≤ n := by nlinarith
      have hdN : d ≤ N := by omega
      simp [show ¬N < d by omega]
    · intro hnot
      exact False.elim (hnot (Nat.mem_divisors.mpr ⟨dvd_refl n, hn0⟩))
  have h := coeff_add_omitted N n hn0
  rw [htail] at h
  omega

/-- The whole first frequency band has nonnegative coefficients. -/
theorem coeff_nonneg_through_twice_add_one {N n : ℕ} (hn : n ≠ 0) (h : n ≤ 2*N+1) :
    0 ≤ coeff N n := by
  by_cases hnN : n ≤ N
  · rw [coeff_eq_one_of_le hn hnN]; positivity
  · rw [coeff_first_band (by omega) h]
    have hm := (le_abs_self (moebius n)).trans (abs_moebius_le_one (n := n))
    omega

/-- Exact next-band law: the omitted divisors are the full index and its half. -/
theorem coeff_even_second_band {N m : ℕ} (hm : N < m) (hband : 2*m ≤ 3*N) :
    coeff N (2*m) = 1 - moebius (2*m) - 2*moebius m := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : 2*m ≠ 0 := by omega
  have hnm : 2*m ≠ m := by omega
  have hmdiv : m ∈ (2*m).divisors := Nat.mem_divisors.mpr ⟨dvd_mul_left m 2, hn0⟩
  have hndiv : 2*m ∈ (2*m).divisors := Nat.mem_divisors.mpr ⟨dvd_refl _, hn0⟩
  let f : ℕ → ℤ := fun d =>
    if N < d then moebius d * divisorCount (2*m/d) else 0
  have hs : (∑ d ∈ (2*m).divisors, f d) = ∑ d ∈ ({2*m,m} : Finset ℕ), f d := by
    symm
    apply Finset.sum_subset
    · intro d hd
      simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl <;> assumption
    · intro d hd hnot
      have hdn : d ≠ 2*m := by intro he; subst d; simp at hnot
      have hdm : d ≠ m := by intro he; subst d; simp at hnot
      have hdvd := (Nat.mem_divisors.mp hd).1
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
      have hp : d ∈ (2*m).properDivisors :=
        Nat.mem_properDivisors.mpr ⟨hdvd, by omega⟩
      obtain ⟨k, hk, he⟩ := (Nat.mem_properDivisors_iff_exists hn0).mp hp
      have hk2 : k ≠ 2 := by intro hk2; rw [hk2] at he; omega
      have hk3 : 3 ≤ k := by omega
      have hd3 : 3*d ≤ 2*m := by nlinarith
      have hdN : d ≤ N := by omega
      simp [f, show ¬N < d by omega]
  have hτ2 : divisorCount 2 = 2 := by
    rw [divisorCount_eq_card, Nat.prime_two.divisors]
    simp
  have htail : (∑ d ∈ (2*m).divisors, f d) = moebius (2*m) + 2*moebius m := by
    rw [hs]
    simp only [sum_pair hnm, f, if_pos hm,
      if_pos (show N < 2*m by omega), Nat.div_self (Nat.pos_of_ne_zero hn0),
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0), hτ2]
    simp [divisorCount_eq_card, mul_comm]
  have h := coeff_add_omitted N (2*m) hn0
  change coeff N (2*m) + (∑ d ∈ (2*m).divisors, f d) = 1 at h
  rw [htail] at h
  omega

/-- A prime family reaches a negative coefficient immediately after the positive band. -/
theorem coeff_prime_boundary {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    coeff (2*p-1) (4*p) = -1 := by
  have hc : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  have hmu : moebius (2*p) = 1 := by
    rw [isMultiplicative_moebius.map_mul_of_coprime hc,
      moebius_apply_prime Nat.prime_two, moebius_apply_prime hp]
    rfl
  have hmu4 : moebius (4*p) = 0 := by
    apply moebius_eq_zero_of_not_squarefree
    intro hs
    have hs4 : Squarefree (4 : ℕ) := hs.squarefree_of_dvd (dvd_mul_right 4 p)
    have hsmu : moebius 4 ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hs4
    have hz : moebius 4 = 0 := by
      have he := moebius_apply_prime_pow (k := 2) Nat.prime_two (by omega)
      simpa using he
    exact hsmu hz
  have h := coeff_even_second_band (N := 2*p-1) (m := 2*p) (by omega) (by omega)
  have he : 2*(2*p) = 4*p := by omega
  rw [he, hmu4, hmu] at h
  exact h

/-- The first excluded integer has a negative coefficient at arbitrarily large cutoffs. -/
theorem cofinal_negative_next_frequency :
    ∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧ coeff N (2*N+2) = -1 := by
  intro B
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (max 3 (B+1))
  have hp3 : 3 ≤ p := (le_max_left _ _).trans hpB
  have hBp : B+1 ≤ p := (le_max_right _ _).trans hpB
  refine ⟨2*p-1, by omega, ?_⟩
  have he : 2*(2*p-1)+2 = 4*p := by omega
  rw [he]
  exact coeff_prime_boundary hp hp3

/-- Closed sharp classification: positivity through `2*N+1`, with cofinal failure at `2*N+2`. -/
theorem sharp_cofinal_sign_boundary :
    (∀ N n : ℕ, n ≤ 2*N+1 → 0 ≤ coeff N n) ∧
    (∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧ coeff N (2*N+2) = -1) := by
  refine ⟨?_, cofinal_negative_next_frequency⟩
  intro N n hn
  by_cases hn0 : n = 0
  · subst n; simp [coeff]
  · exact coeff_nonneg_through_twice_add_one hn0 hn

end RHTower.DeletionDivisorFrequency
