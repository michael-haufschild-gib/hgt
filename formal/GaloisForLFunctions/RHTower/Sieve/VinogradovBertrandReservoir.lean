import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

private theorem exists_vinogradovCeilRootWitness (k N : ℕ) :
    ∃ y : ℕ, k = 0 ∨ N ≤ y ^ k := by
  by_cases hk : k = 0
  · exact ⟨0, Or.inl hk⟩
  · refine ⟨N + 1, Or.inr ?_⟩
    exact (Nat.le_succ N).trans (Nat.le_pow (Nat.pos_of_ne_zero hk))

/-- Least natural `y` whose `k`-th power covers `N` (with a harmless
totalization at `k=0`). -/
def vinogradovCeilRoot (k N : ℕ) : ℕ :=
  Nat.find (exists_vinogradovCeilRootWitness k N)

theorem le_vinogradovCeilRoot_pow {k N : ℕ} (hk : k ≠ 0) :
    N ≤ vinogradovCeilRoot k N ^ k := by
  have h := Nat.find_spec (exists_vinogradovCeilRootWitness k N)
  exact h.resolve_left hk

theorem vinogradovCeilRoot_pos {k N : ℕ} (hk : k ≠ 0) (hN : N ≠ 0) :
    0 < vinogradovCeilRoot k N := by
  by_contra hzero
  have hy : vinogradovCeilRoot k N = 0 := Nat.eq_zero_of_not_pos hzero
  have hcover := le_vinogradovCeilRoot_pow (k := k) (N := N) hk
  rw [hy, zero_pow hk] at hcover
  exact hN (Nat.eq_zero_of_le_zero hcover)

theorem pred_vinogradovCeilRoot_pow_lt
    {k N : ℕ} (hk : k ≠ 0) (hN : N ≠ 0) :
    (vinogradovCeilRoot k N - 1) ^ k < N := by
  let y := vinogradovCeilRoot k N
  have hypos : 0 < y := vinogradovCeilRoot_pos hk hN
  have hmin := Nat.find_min (exists_vinogradovCeilRootWitness k N)
    (Nat.sub_lt hypos zero_lt_one)
  exact Nat.lt_of_not_ge fun hge => hmin (Or.inr hge)

/-- The least covering root loses at most `2^k` after taking the `k`-th
power.  This replaces real-root rounding in the mean-value induction. -/
theorem vinogradovCeilRoot_pow_le
    {k N : ℕ} (hk : k ≠ 0) (hN : N ≠ 0) :
    vinogradovCeilRoot k N ^ k ≤ 2 ^ k * N := by
  let y := vinogradovCeilRoot k N
  have hypos : 0 < y := vinogradovCeilRoot_pos hk hN
  have hpred : (y - 1) ^ k < N := pred_vinogradovCeilRoot_pow_lt hk hN
  change y ^ k ≤ 2 ^ k * N
  by_cases hy1 : y = 1
  · rw [hy1, one_pow]
    calc
      1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
      _ = 1 * N := by simp
      _ ≤ 2 ^ k * N := Nat.mul_le_mul_right N
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by omega)))
  · have hpredpos : 0 < y - 1 := by omega
    have hy_le : y ≤ 2 * (y - 1) := by omega
    calc
      y ^ k ≤ (2 * (y - 1)) ^ k := Nat.pow_le_pow_left hy_le k
      _ = 2 ^ k * (y - 1) ^ k := mul_pow 2 (y - 1) k
      _ ≤ 2 ^ k * N := Nat.mul_le_mul_left _ (Nat.le_of_lt hpred)

/-- A deterministic choice of a Bertrand prime above `n+1`. -/
def vinogradovBertrandNext (n : ℕ) : ℕ :=
  Classical.choose (Nat.exists_prime_lt_and_le_two_mul (n + 1) (Nat.succ_ne_zero n))

theorem vinogradovBertrandNext_prime (n : ℕ) :
    (vinogradovBertrandNext n).Prime :=
  (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul (n + 1) (Nat.succ_ne_zero n))).1

theorem lt_vinogradovBertrandNext (n : ℕ) : n < vinogradovBertrandNext n := by
  unfold vinogradovBertrandNext
  have h := (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul (n + 1) (Nat.succ_ne_zero n))).2.1
  omega

theorem vinogradovBertrandNext_le (n : ℕ) :
    vinogradovBertrandNext n ≤ 2 * (n + 1) :=
  (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul (n + 1) (Nat.succ_ne_zero n))).2.2

/-- Iterated Bertrand chain, beginning at an arbitrary threshold `y`. -/
def vinogradovBertrandChain (y : ℕ) : ℕ → ℕ
  | 0 => y
  | n + 1 => vinogradovBertrandNext (vinogradovBertrandChain y n)

@[simp] theorem vinogradovBertrandChain_zero (y : ℕ) :
    vinogradovBertrandChain y 0 = y := rfl

@[simp] theorem vinogradovBertrandChain_succ (y n : ℕ) :
    vinogradovBertrandChain y (n + 1) =
      vinogradovBertrandNext (vinogradovBertrandChain y n) := rfl

theorem vinogradovBertrandChain_lt_succ (y n : ℕ) :
    vinogradovBertrandChain y n < vinogradovBertrandChain y (n + 1) := by
  rw [vinogradovBertrandChain_succ]
  exact lt_vinogradovBertrandNext _

theorem vinogradovBertrandChain_strictMono (y : ℕ) :
    StrictMono (vinogradovBertrandChain y) :=
  strictMono_nat_of_lt_succ (vinogradovBertrandChain_lt_succ y)

theorem vinogradovBertrandChain_add_two_le (y n : ℕ) :
    vinogradovBertrandChain y n + 2 ≤ 2 ^ n * (y + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [vinogradovBertrandChain_succ]
      calc
        vinogradovBertrandNext (vinogradovBertrandChain y n) + 2 ≤
            2 * (vinogradovBertrandChain y n + 1) + 2 :=
          Nat.add_le_add_right (vinogradovBertrandNext_le _) 2
        _ = 2 * (vinogradovBertrandChain y n + 2) := by omega
        _ ≤ 2 * (2 ^ n * (y + 2)) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) * (y + 2) := by ring

/-- `M` distinct primes above `y`, obtained without a prime number theorem. -/
def vinogradovBertrandPrimeReservoir (y M : ℕ) (i : Fin M) : ℕ :=
  vinogradovBertrandChain y (i.val + 1)

theorem vinogradovBertrandPrimeReservoir_prime
    (y M : ℕ) (i : Fin M) :
    (vinogradovBertrandPrimeReservoir y M i).Prime := by
  rw [vinogradovBertrandPrimeReservoir, vinogradovBertrandChain_succ]
  exact vinogradovBertrandNext_prime _

theorem vinogradovBertrandPrimeReservoir_injective (y M : ℕ) :
    Function.Injective (vinogradovBertrandPrimeReservoir y M) := by
  intro i j hij
  apply Fin.ext
  have := (vinogradovBertrandChain_strictMono y).injective hij
  omega

theorem lt_vinogradovBertrandPrimeReservoir
    (y M : ℕ) (i : Fin M) :
    y < vinogradovBertrandPrimeReservoir y M i := by
  change vinogradovBertrandChain y 0 <
    vinogradovBertrandChain y (i.val + 1)
  exact vinogradovBertrandChain_strictMono y (by omega)

theorem vinogradovBertrandPrimeReservoir_add_two_le
    (y M : ℕ) (i : Fin M) :
    vinogradovBertrandPrimeReservoir y M i + 2 ≤ 2 ^ M * (y + 2) := by
  calc
    vinogradovBertrandPrimeReservoir y M i + 2 ≤
        2 ^ (i.val + 1) * (y + 2) :=
      vinogradovBertrandChain_add_two_le y (i.val + 1)
    _ ≤ 2 ^ M * (y + 2) := by
      exact Nat.mul_le_mul_right (y + 2)
        (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))

/-- If nonzero `A` is at most `y^M`, one of the first `M+1` Bertrand
primes above `y` does not divide `A`. -/
theorem exists_vinogradovBertrandPrimeReservoir_not_dvd
    {y M A : ℕ} (hy : 0 < y) (hA : A ≠ 0) (hbound : A ≤ y ^ M) :
    ∃ i : Fin (M + 1),
      ¬vinogradovBertrandPrimeReservoir y (M + 1) i ∣ A := by
  by_contra hall
  push Not at hall
  let f : Fin (M + 1) → ℕ :=
    vinogradovBertrandPrimeReservoir y (M + 1)
  have hpair : Set.Pairwise Set.univ
      (Function.onFun IsRelPrime f) := by
    intro i _ j _ hij
    change IsRelPrime (f i) (f j)
    rw [← Nat.coprime_iff_isRelPrime]
    apply (Nat.coprime_primes
      (by simpa [f] using vinogradovBertrandPrimeReservoir_prime y (M + 1) i)
      (by simpa [f] using vinogradovBertrandPrimeReservoir_prime y (M + 1) j)).2
    exact fun h => hij (vinogradovBertrandPrimeReservoir_injective y (M + 1)
      (by simpa [f] using h))
  have hprodDvd : (∏ i : Fin (M + 1), f i) ∣ A := by
    apply Finset.prod_dvd_of_isRelPrime
    · simpa using hpair
    · exact fun i _ => hall i
  have hprod_le : (∏ i : Fin (M + 1), f i) ≤ A :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hA) hprodDvd
  by_cases hy1 : y = 1
  · have hbound' : A ≤ 1 := by simpa [hy1] using hbound
    have hA1 : A = 1 := by omega
    subst A
    have hprime := vinogradovBertrandPrimeReservoir_prime y (M + 1)
      (⟨0, by omega⟩ : Fin (M + 1))
    exact hprime.not_dvd_one (hall ⟨0, by omega⟩)
  · have hygt : 1 < y := by omega
    have hlower : y ^ (M + 1) < ∏ i : Fin (M + 1), f i := by
      have hconst : (∏ _i : Fin (M + 1), y) = y ^ (M + 1) := by simp
      rw [← hconst]
      apply Finset.prod_lt_prod
      · intro i _
        exact hy
      · intro i _
        exact (lt_vinogradovBertrandPrimeReservoir y (M + 1) i).le
      · exact ⟨⟨0, by omega⟩, Finset.mem_univ _,
          lt_vinogradovBertrandPrimeReservoir y (M + 1) ⟨0, by omega⟩⟩
    have hpow : y ^ M < y ^ (M + 1) := by
      exact Nat.pow_lt_pow_right hygt (by omega)
    exact (Nat.not_lt_of_ge (hprod_le.trans hbound)) (hpow.trans hlower)

end

end RHTower.Sieve
