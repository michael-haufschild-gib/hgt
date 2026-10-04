import GaloisForLFunctions.RHTower.LiouvilleTwistedDensityPhase

/-!
# Exact multiplicity decomposition of a moving prime-phase band

The common phase parameter enters every arithmetic coefficient as a single monomial.
Its degree counts selected prime factors with multiplicity. Degree one has an exact
sum over selected primes and band-free cofactors; degree at least two forces a product
of two selected primes to divide the index, allowing the two primes to coincide.
Thus no prime square or mixed cofactor is omitted from the nonlinear remainder.

These identities supply the arithmetic decomposition for MC-C12.92. They do not assert
a simple zero, Liouville positivity, critical cancellation, or RH.
-/

open Finset
open scoped BigOperators

namespace RHTower.LiouvillePrimeBand
noncomputable section

/-- Total selected-prime multiplicity, including repeated prime factors. -/
def degree (P : Finset ℕ) (n : ℕ) : ℕ := ∑ p ∈ P, n.factorization p

@[simp] theorem degree_zero (P : Finset ℕ) : degree P 0 = 0 := by simp [degree]
@[simp] theorem degree_one (P : Finset ℕ) : degree P 1 = 0 := by simp [degree]

theorem degree_mul (P : Finset ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    degree P (m * n) = degree P m + degree P n := by
  simp only [degree, Nat.factorization_mul hm hn, Finsupp.add_apply, Finset.sum_add_distrib]

theorem degree_prime (P : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    degree P p = if p ∈ P then 1 else 0 := by
  simp [degree, hp.factorization, Finsupp.single_apply]

theorem factorization_eq_zero_of_degree_zero {P : Finset ℕ} {n p : ℕ}
    (hn : degree P n = 0) (hp : p ∈ P) : n.factorization p = 0 := by
  have h := Finset.single_le_sum (fun q (_ : q ∈ P) => Nat.zero_le (n.factorization q)) hp
  change n.factorization p ≤ degree P n at h
  omega

theorem exists_prime_dvd_of_degree_pos {P : Finset ℕ} {n : ℕ} (hn : 0 < degree P n) :
    ∃ p ∈ P, p.Prime ∧ p ∣ n := by
  obtain ⟨p, hp, hpv⟩ := Finset.sum_pos_iff.mp hn
  have hprime : p.Prime := by
    by_contra h
    exact hpv.ne' ((Nat.factorization_eq_zero_iff n p).mpr (Or.inl h))
  exact ⟨p, hp, hprime, Nat.dvd_of_factorization_pos hpv.ne'⟩

theorem degree_pos_of_prime_dvd {P : Finset ℕ} {n p : ℕ} (hpP : p ∈ P)
    (hp : p.Prime) (hn : n ≠ 0) (hpn : p ∣ n) : 0 < degree P n :=
  (hp.factorization_pos_of_dvd hn hpn).trans_le
    (Finset.single_le_sum (fun q (_ : q ∈ P) => Nat.zero_le (n.factorization q)) hpP)

theorem degree_div_prime {P : Finset ℕ} {n p : ℕ} (hpP : p ∈ P)
    (hp : p.Prime) (hn : n ≠ 0) (hpn : p ∣ n) :
    degree P n = 1 + degree P (n / p) := by
  have hq : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) hp.pos).ne'
  calc
    degree P n = degree P (p * (n / p)) := congrArg (degree P) (Nat.mul_div_cancel' hpn).symm
    _ = _ := by rw [degree_mul P hp.ne_zero hq, degree_prime P hp, if_pos hpP]

theorem degree_le_self (P : Finset ℕ) (n : ℕ) : degree P n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hd : degree P n = 0
    · simp [hd]
    · have hn : n ≠ 0 := by intro h; subst n; simp at hd
      obtain ⟨p, hpP, hp, hpn⟩ := exists_prime_dvd_of_degree_pos (Nat.pos_of_ne_zero hd)
      have hq : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) hp.pos
      have hi := ih (n / p) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt)
      rw [degree_div_prime hpP hp hn hpn]
      have he : p * (n / p) = n := Nat.mul_div_cancel' hpn
      have hp2 := hp.two_le
      nlinarith

theorem exists_two_prime_divisors_of_degree_ge_two {P : Finset ℕ} {n : ℕ}
    (hn : 2 ≤ degree P n) : ∃ p ∈ P, ∃ q ∈ P, p.Prime ∧ q.Prime ∧ p * q ∣ n := by
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
  obtain ⟨p, hpP, hp, hpn⟩ := exists_prime_dvd_of_degree_pos (by omega : 0 < degree P n)
  have hdeg := degree_div_prime hpP hp hn0 hpn
  obtain ⟨q, hqP, hq, hqn⟩ := exists_prime_dvd_of_degree_pos (by omega : 0 < degree P (n / p))
  refine ⟨p, hpP, q, hqP, hp, hq, ?_⟩
  obtain ⟨k, hk⟩ := hqn
  refine ⟨k, ?_⟩
  calc
    n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
    _ = (p * q) * k := by rw [hk]; ring

theorem degree_pos_escape {P : Finset ℕ} {n : ℕ} {T : ℝ}
    (hP : ∀ p ∈ P, T < (p : ℝ)) (hn : 0 < degree P n) : T < (n : ℝ) := by
  have hn0 : 0 < n := by
    by_contra h
    have hnzero : n = 0 := by omega
    subst n
    simp at hn
  obtain ⟨p, hpP, _, hpn⟩ := exists_prime_dvd_of_degree_pos hn
  exact (hP p hpP).trans_le (by exact_mod_cast Nat.le_of_dvd hn0 hpn)

theorem degree_ge_two_escape {P : Finset ℕ} {n : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (hP : ∀ p ∈ P, T < (p : ℝ)) (hn : 2 ≤ degree P n) :
    T ^ 2 < (n : ℝ) := by
  have hn0 : 0 < n := by
    by_contra h
    have hnzero : n = 0 := by omega
    subst n
    simp at hn
  obtain ⟨p, hpP, q, hqP, hp, hq, hpqn⟩ := exists_two_prime_divisors_of_degree_ge_two hn
  have hle : (p : ℝ) * (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_dvd hn0 hpqn
  have hpp := hP p hpP
  have hqq := hP q hqP
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  nlinarith [mul_pos (sub_pos.mpr hpp) (sub_pos.mpr hqq)]

/-- Vary exactly the selected prime phases, leaving the original fixed twist elsewhere. -/
def character (P : Finset ℕ) (β : ℕ → ℂ) (z : ℂ) : ℕ →*₀ ℂ :=
  GaloisForLFunctions.HTGeometry.phaseChar
    (fun p => if p ∈ P then z * β p else RHTower.LiouvilleTwistedDensity.primePhase p)

theorem character_prime {P : Finset ℕ} {p : ℕ} (hp : p.Prime) (hpP : p ∈ P)
    (β : ℕ → ℂ) (z : ℂ) : character P β z p = z * β p := by
  rw [character, GaloisForLFunctions.HTGeometry.phaseChar_prime _ hp, if_pos hpP]

theorem character_eq_twist_of_degree_zero {P : Finset ℕ} {n : ℕ} (hn : degree P n = 0)
    (β : ℕ → ℂ) (z : ℂ) : character P β z n = RHTower.LiouvilleTwistedDensity.twist n := by
  by_cases hn0 : n = 0
  · simp [hn0]
  rw [character, RHTower.LiouvilleTwistedDensity.twist,
    GaloisForLFunctions.HTGeometry.phaseChar_apply_of_ne_zero _ hn0,
    GaloisForLFunctions.HTGeometry.phaseChar_apply_of_ne_zero _ hn0, Finsupp.prod, Finsupp.prod]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : p ∈ P
  · simp [hp, factorization_eq_zero_of_degree_zero hn hp]
  · simp [hp]

private theorem degree_eq_support_sum (P : Finset ℕ) (n : ℕ) :
    degree P n = ∑ p ∈ n.factorization.support, if p ∈ P then n.factorization p else 0 := by
  have hset : P.filter (fun p => p ∈ n.factorization.support) =
      n.factorization.support.filter (fun p => p ∈ P) := by
    ext p
    simp [and_comm]
  rw [← Finset.sum_filter, ← hset]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hs : p ∉ n.factorization.support := by simpa [hp] using hnot
  exact Finsupp.notMem_support_iff.mp hs

/-- Each coefficient is a single monomial in the common prime-phase parameter. -/
theorem character_eq_monomial (P : Finset ℕ) (β : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    character P β z n = character P β 1 n * z ^ degree P n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [character, character,
    GaloisForLFunctions.HTGeometry.phaseChar_apply_of_ne_zero _ hn,
    GaloisForLFunctions.HTGeometry.phaseChar_apply_of_ne_zero _ hn,
    degree_eq_support_sum, ← Finset.prod_pow_eq_pow_sum]
  simp only [Finsupp.prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : p ∈ P
  · simp only [hp, ↓reduceIte, one_mul, mul_pow]
    ring
  · simp [hp]

theorem norm_character_one_le {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) (n : ℕ) : ‖character P β 1 n‖ ≤ 1 := by
  apply GaloisForLFunctions.HTGeometry.norm_phaseChar_le_one
  intro p _
  by_cases hp : p ∈ P
  · simp [hp, hβ p hp]
  · by_cases hp2 : p = 2
    · subst p
      simp [hp, RHTower.LiouvilleTwistedDensity.primePhase]
    · simp [hp, RHTower.LiouvilleTwistedDensity.primePhase, hp2]

theorem norm_character_le_pow {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) (z : ℂ) (n : ℕ) :
    ‖character P β z n‖ ≤ ‖z‖ ^ degree P n := by
  rw [character_eq_monomial, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (norm_character_one_le hβ n)

theorem character_baseline {P : Finset ℕ} (hP : 2 ∉ P) :
    character P (fun _ => -1) 1 = RHTower.LiouvilleTwistedDensity.twist := by
  unfold character RHTower.LiouvilleTwistedDensity.twist
  congr 1
  funext p
  by_cases hp : p ∈ P
  · have hp2 : p ≠ 2 := by intro he; subst p; exact hP hp
    simp [hp, RHTower.LiouvilleTwistedDensity.primePhase, hp2]
  · simp [hp]

private theorem unique_prime_of_degree_one {P : Finset ℕ} {n p q : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hn : degree P n = 1)
    (hpP : p ∈ P) (hpn : p ∣ n) (hqP : q ∈ P) (hqn : q ∣ n) : q = p := by
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
  have hp := hP p hpP
  have hq := hP q hqP
  have hm0 : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn) hp.pos).ne'
  have hfree : degree P (n / p) = 0 := by have := degree_div_prime hpP hp hn0 hpn; omega
  have hdiv : q ∣ p * (n / p) := by rwa [Nat.mul_div_cancel' hpn]
  rcases hq.dvd_mul.mp hdiv with hqp | hqm
  · exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  · have hpos := degree_pos_of_prime_dvd hqP hq hm0 hqm
    omega

/-- The exact coefficient of degree one, with every selected prime included. -/
theorem character_degree_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (β : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    (if degree P n = 1 then character P β z n else 0) =
      ∑ p ∈ P, if p ∣ n ∧ degree P (n / p) = 0 then
        z * β p * RHTower.LiouvilleTwistedDensity.twist (n / p) else 0 := by
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn : degree P n = 1
  · obtain ⟨p, hpP, hp, hpn⟩ := exists_prime_dvd_of_degree_pos (by omega : 0 < degree P n)
    have hfree : degree P (n / p) = 0 := by have := degree_div_prime hpP hp hn0 hpn; omega
    have hchar : character P β z n = z * β p * RHTower.LiouvilleTwistedDensity.twist (n / p) := by
      calc
        _ = character P β z (p * (n / p)) := congrArg (character P β z) (Nat.mul_div_cancel' hpn).symm
        _ = _ := by rw [map_mul, character_prime hp hpP, character_eq_twist_of_degree_zero hfree]
    rw [if_pos hn, Finset.sum_eq_single p]
    · rw [if_pos ⟨hpn, hfree⟩]
      exact hchar
    · intro q hqP hqp
      have hnot : ¬q ∣ n := by intro hqn; exact hqp (unique_prime_of_degree_one hP hn hpP hpn hqP hqn)
      simp [hnot]
    · exact fun h => (h hpP).elim
  · rw [if_neg hn]
    symm
    apply Finset.sum_eq_zero
    intro p hpP
    split_ifs with hcond
    · have hdeg := degree_div_prime hpP (hP p hpP) hn0 hcond.1
      exact (hn (by omega)).elim
    · rfl

/-- Zero, linear, and nonlinear parts of the actual source, without omitting any integer. -/
theorem character_decomposition (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (β : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    character P β z n =
      (if degree P n = 0 then RHTower.LiouvilleTwistedDensity.twist n else 0) +
      (∑ p ∈ P, if p ∣ n ∧ degree P (n / p) = 0 then
        z * β p * RHTower.LiouvilleTwistedDensity.twist (n / p) else 0) +
      (if 2 ≤ degree P n then character P β z n else 0) := by
  rw [← character_degree_one P hP β z n]
  by_cases h0 : degree P n = 0
  · simp [h0, character_eq_twist_of_degree_zero h0]
  · by_cases h1 : degree P n = 1
    · simp [h1]
    · have h2 : 2 ≤ degree P n := by omega
      simp [h0, h1, h2]

end
end RHTower.LiouvillePrimeBand
