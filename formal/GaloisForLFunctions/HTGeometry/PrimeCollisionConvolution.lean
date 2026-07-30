import GaloisForLFunctions.HTGeometry.PrimeConstraintJoining
import GaloisForLFunctions.HTGeometry.PrimeValuationFusion

/-!
# Prime collision strata of native Dirichlet convolution

The same-prime face of the product of two pure prime-power columns is exactly prime-valuation
fusion after projection to the corresponding output layer. At two distinct primes, unequal
valuation degrees retain the ordered tensor coefficient, while equal degrees retain precisely the
two-term symmetrization. These are exact coefficient identities inside the native arithmetic
function ring.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

/-- Projection of an arithmetic function onto one positive prime-power layer. -/
def primePowerLayerProjection (e : ℕ) (A : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ :=
  arithmeticOfPrimePowerColumn e fun p => A ((p : ℕ) ^ (e + 1))

/-- The same-prime coefficient of native Dirichlet convolution is exactly the product of the two
input column coefficients. -/
theorem arithmeticOfPrimePowerColumn_mul_apply_samePrime
    (e f : ℕ) (c d : Nat.Primes → ℂ) (p : Nat.Primes) :
    (arithmeticOfPrimePowerColumn e c * arithmeticOfPrimePowerColumn f d)
        ((p : ℕ) ^ (e + f + 2)) = c p * d p := by
  rw [ArithmeticFunction.mul_apply]
  rw [Finset.sum_eq_single
    ((p : ℕ) ^ (e + 1), (p : ℕ) ^ (f + 1))]
  · simp
  · rintro ⟨a, b⟩ hab hne
    by_cases ha : arithmeticOfPrimePowerColumn e c a = 0
    · simp [ha]
    by_cases hb : arithmeticOfPrimePowerColumn f d b = 0
    · simp [hb]
    exfalso
    obtain ⟨q, hq⟩ := arithmeticOfPrimePowerColumn_support e c ha
    obtain ⟨r, hr⟩ := arithmeticOfPrimePowerColumn_support f d hb
    have habprod : a * b = (p : ℕ) ^ (e + f + 2) :=
      (Nat.mem_divisorsAntidiagonal.mp hab).1
    have hqdiva : (q : ℕ) ∣ a := by
      rw [hq]
      exact dvd_pow_self _ (Nat.succ_ne_zero e)
    have hardiv : a ∣ (p : ℕ) ^ (e + f + 2) := ⟨b, habprod.symm⟩
    have hqdivp : (q : ℕ) ∣ (p : ℕ) ^ (e + f + 2) := hqdiva.trans hardiv
    have hqp : q = p := by
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hqdivp
    have hrdivb : (r : ℕ) ∣ b := by
      rw [hr]
      exact dvd_pow_self _ (Nat.succ_ne_zero f)
    have hbrdiv : b ∣ (p : ℕ) ^ (e + f + 2) := by
      refine ⟨a, ?_⟩
      rw [Nat.mul_comm]
      exact habprod.symm
    have hrdivp : (r : ℕ) ∣ (p : ℕ) ^ (e + f + 2) := hrdivb.trans hbrdiv
    have hrp : r = p := by
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow r.2 p.2 hrdivp
    apply hne
    apply Prod.ext
    · simpa [hqp] using hq
    · simpa [hrp] using hr
  · intro hnot
    exfalso
    apply hnot
    apply Nat.mem_divisorsAntidiagonal.mpr
    constructor
    · rw [← pow_add]
      congr 1
      omega
    · exact pow_ne_zero _ p.2.ne_zero

/-- Prime-valuation fusion is not an added multiplication: it is precisely the same-prime
collision projection of native Dirichlet convolution. -/
theorem primePowerLayerProjection_mul_columns
    (e f : ℕ) (c d : Nat.Primes → ℂ) :
    primePowerLayerProjection (e + f + 1)
        (arithmeticOfPrimePowerColumn e c * arithmeticOfPrimePowerColumn f d) =
      primeValuationFusion e f
        (arithmeticOfPrimePowerColumn e c) (arithmeticOfPrimePowerColumn f d) := by
  rw [primeValuationFusion_columns]
  unfold primePowerLayerProjection
  congr 1
  funext p
  simpa [Nat.add_assoc] using
    arithmeticOfPrimePowerColumn_mul_apply_samePrime e f c d p

theorem swapped_distinct_prime_powers_force_equal_exponents
    (e f : ℕ) (p q : Nat.Primes) (hpq : p ≠ q)
    (h : (q : ℕ) ^ (e + 1) * (p : ℕ) ^ (f + 1) =
      (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (f + 1)) : e = f := by
  have hfac := congrArg (fun n : ℕ => n.factorization (p : ℕ)) h
  have hpqNat : (p : ℕ) ≠ (q : ℕ) := fun hpq' => hpq (Subtype.ext hpq')
  rw [Nat.factorization_mul
      (pow_ne_zero _ q.2.ne_zero) (pow_ne_zero _ p.2.ne_zero),
    Nat.factorization_mul
      (pow_ne_zero _ p.2.ne_zero) (pow_ne_zero _ q.2.ne_zero)] at hfac
  rw [q.2.factorization_pow, p.2.factorization_pow,
    p.2.factorization_pow, q.2.factorization_pow] at hfac
  simp [hpqNat] at hfac
  omega

/-- With unequal positive valuation degrees, unique factorization orients a two-prime collision. -/
theorem primePower_pair_orientation
    (e f : ℕ) (hef : e ≠ f)
    (p q r s : Nat.Primes) (hpq : p ≠ q)
    (h : (r : ℕ) ^ (e + 1) * (s : ℕ) ^ (f + 1) =
      (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (f + 1)) :
    r = p ∧ s = q := by
  have hrdivTarget : (r : ℕ) ∣
      (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (f + 1) := by
    rw [← h]
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero e)) _
  have hsdivTarget : (s : ℕ) ∣
      (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (f + 1) := by
    rw [← h]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ (Nat.succ_ne_zero f)) _
  have hrCases : r = p ∨ r = q := by
    rcases (r.2.dvd_mul.mp hrdivTarget) with hrp | hrq
    · left
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow r.2 p.2 hrp
    · right
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow r.2 q.2 hrq
  have hsCases : s = p ∨ s = q := by
    rcases (s.2.dvd_mul.mp hsdivTarget) with hsp | hsq
    · left
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow s.2 p.2 hsp
    · right
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow s.2 q.2 hsq
  rcases hrCases with hrp | hrq
  · subst r
    rcases hsCases with hsp | hsq
    · subst s
      exfalso
      have hqdiv : (q : ℕ) ∣ (p : ℕ) ^ (e + 1) * (p : ℕ) ^ (f + 1) := by
        rw [h]
        exact dvd_mul_of_dvd_right (dvd_pow_self _ (Nat.succ_ne_zero f)) _
      rcases q.2.dvd_mul.mp hqdiv with hqp | hqp
      · exact hpq (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hqp).symm)
      · exact hpq (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hqp).symm)
    · subst s
      exact ⟨rfl, rfl⟩
  · subst r
    rcases hsCases with hsp | hsq
    · subst s
      exfalso
      exact hef (swapped_distinct_prime_powers_force_equal_exponents e f p q hpq h)
    · subst s
      exfalso
      have hpdiv : (p : ℕ) ∣ (q : ℕ) ^ (e + 1) * (q : ℕ) ^ (f + 1) := by
        rw [h]
        exact dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero e)) _
      rcases p.2.dvd_mul.mp hpdiv with hpq' | hpq'
      · exact hpq (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow p.2 q.2 hpq'))
      · exact hpq (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow p.2 q.2 hpq'))

/-- Unequal valuation degrees label the two distinct-prime factors, so the native convolution
coefficient is the ordered tensor coefficient with no symmetrization. -/
theorem arithmeticOfPrimePowerColumn_mul_apply_distinct_unequal
    (e f : ℕ) (hef : e ≠ f) (c d : Nat.Primes → ℂ)
    (p q : Nat.Primes) (hpq : p ≠ q) :
    (arithmeticOfPrimePowerColumn e c * arithmeticOfPrimePowerColumn f d)
        ((p : ℕ) ^ (e + 1) * (q : ℕ) ^ (f + 1)) = c p * d q := by
  rw [ArithmeticFunction.mul_apply]
  rw [Finset.sum_eq_single
    ((p : ℕ) ^ (e + 1), (q : ℕ) ^ (f + 1))]
  · simp
  · rintro ⟨a, b⟩ hab hne
    by_cases ha : arithmeticOfPrimePowerColumn e c a = 0
    · simp [ha]
    by_cases hb : arithmeticOfPrimePowerColumn f d b = 0
    · simp [hb]
    exfalso
    obtain ⟨r, hr⟩ := arithmeticOfPrimePowerColumn_support e c ha
    obtain ⟨s, hs⟩ := arithmeticOfPrimePowerColumn_support f d hb
    have habprod : a * b =
        (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (f + 1) :=
      (Nat.mem_divisorsAntidiagonal.mp hab).1
    have hrs : (r : ℕ) ^ (e + 1) * (s : ℕ) ^ (f + 1) =
        (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (f + 1) := by
      rw [← hr, ← hs]
      exact habprod
    obtain ⟨hrp, hsq⟩ := primePower_pair_orientation e f hef p q r s hpq hrs
    apply hne
    apply Prod.ext
    · simpa [hrp] using hr
    · simpa [hsq] using hs
  · intro hnot
    exfalso
    apply hnot
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨rfl, mul_ne_zero (pow_ne_zero _ p.2.ne_zero) (pow_ne_zero _ q.2.ne_zero)⟩

/-- Equal valuation degrees forget the ordering of the two distinct prime factors, but retain the
unordered pair exactly. -/
theorem equalPrimePower_pair_unordered
    (e : ℕ) (p q r s : Nat.Primes) (hpq : p ≠ q)
    (h : (r : ℕ) ^ (e + 1) * (s : ℕ) ^ (e + 1) =
      (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (e + 1)) :
    (r = p ∧ s = q) ∨ (r = q ∧ s = p) := by
  have hrdivTarget : (r : ℕ) ∣
      (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (e + 1) := by
    rw [← h]
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero e)) _
  have hsdivTarget : (s : ℕ) ∣
      (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (e + 1) := by
    rw [← h]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ (Nat.succ_ne_zero e)) _
  have hrCases : r = p ∨ r = q := by
    rcases (r.2.dvd_mul.mp hrdivTarget) with hrp | hrq
    · exact Or.inl (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow r.2 p.2 hrp))
    · exact Or.inr (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow r.2 q.2 hrq))
  have hsCases : s = p ∨ s = q := by
    rcases (s.2.dvd_mul.mp hsdivTarget) with hsp | hsq
    · exact Or.inl (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow s.2 p.2 hsp))
    · exact Or.inr (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow s.2 q.2 hsq))
  rcases hrCases with hrp | hrq
  · subst r
    rcases hsCases with hsp | hsq
    · subst s
      exfalso
      have hqdiv : (q : ℕ) ∣ (p : ℕ) ^ (e + 1) * (p : ℕ) ^ (e + 1) := by
        rw [h]
        exact dvd_mul_of_dvd_right (dvd_pow_self _ (Nat.succ_ne_zero e)) _
      rcases q.2.dvd_mul.mp hqdiv with hqp | hqp
      · exact hpq (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hqp).symm)
      · exact hpq (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hqp).symm)
    · exact Or.inl ⟨rfl, hsq⟩
  · subst r
    rcases hsCases with hsp | hsq
    · exact Or.inr ⟨rfl, hsp⟩
    · subst s
      exfalso
      have hpdiv : (p : ℕ) ∣ (q : ℕ) ^ (e + 1) * (q : ℕ) ^ (e + 1) := by
        rw [h]
        exact dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero e)) _
      rcases p.2.dvd_mul.mp hpdiv with hpq' | hpq'
      · exact hpq (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow p.2 q.2 hpq'))
      · exact hpq (Subtype.ext (Nat.prime_eq_prime_of_dvd_pow p.2 q.2 hpq'))

/-- Equal valuation degrees produce precisely the two ordered lifts of an unordered distinct-prime
collision. Thus native convolution gives the exact symmetrized tensor coefficient. -/
theorem arithmeticOfPrimePowerColumn_mul_apply_distinct_equal
    (e : ℕ) (c d : Nat.Primes → ℂ)
    (p q : Nat.Primes) (hpq : p ≠ q) :
    (arithmeticOfPrimePowerColumn e c * arithmeticOfPrimePowerColumn e d)
        ((p : ℕ) ^ (e + 1) * (q : ℕ) ^ (e + 1)) =
      c p * d q + c q * d p := by
  rw [ArithmeticFunction.mul_apply]
  let n : ℕ := (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (e + 1)
  let P : ℕ × ℕ := ((p : ℕ) ^ (e + 1), (q : ℕ) ^ (e + 1))
  let Q : ℕ × ℕ := ((q : ℕ) ^ (e + 1), (p : ℕ) ^ (e + 1))
  have hn : n ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ p.2.ne_zero) (pow_ne_zero _ q.2.ne_zero)
  have hP : P ∈ Nat.divisorsAntidiagonal n :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hn⟩
  have hQ : Q ∈ Nat.divisorsAntidiagonal n := by
    apply Nat.mem_divisorsAntidiagonal.mpr
    constructor
    · dsimp only [Q, n]
      rw [Nat.mul_comm]
    · exact hn
  have hQP : Q ≠ P := by
    intro hQP
    have hpqpow : (q : ℕ) ^ (e + 1) = (p : ℕ) ^ (e + 1) :=
      congrArg Prod.fst hQP
    have hpqNat : (q : ℕ) = (p : ℕ) :=
      Nat.pow_left_injective (Nat.succ_ne_zero e) hpqpow
    exact hpq (Subtype.ext hpqNat.symm)
  change (∑ de ∈ Nat.divisorsAntidiagonal n,
    arithmeticOfPrimePowerColumn e c de.1 *
      arithmeticOfPrimePowerColumn e d de.2) = _
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hP]
  have hQerase : Q ∈ Nat.divisorsAntidiagonal n \ {P} := by
    exact Finset.mem_sdiff.mpr ⟨hQ, by simpa using hQP⟩
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hQerase]
  have hrest :
      ∑ de ∈ (Nat.divisorsAntidiagonal n \ {P}) \ {Q},
        arithmeticOfPrimePowerColumn e c de.1 *
          arithmeticOfPrimePowerColumn e d de.2 = 0 := by
    apply Finset.sum_eq_zero
    intro de hde
    have hdeQ := (Finset.mem_sdiff.mp hde).2
    have hdeP := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hde).1).2
    have hdeMem := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hde).1).1
    by_cases ha : arithmeticOfPrimePowerColumn e c de.1 = 0
    · simp [ha]
    by_cases hb : arithmeticOfPrimePowerColumn e d de.2 = 0
    · simp [hb]
    exfalso
    obtain ⟨r, hr⟩ := arithmeticOfPrimePowerColumn_support e c ha
    obtain ⟨s, hs⟩ := arithmeticOfPrimePowerColumn_support e d hb
    have hprod : de.1 * de.2 = n :=
      (Nat.mem_divisorsAntidiagonal.mp hdeMem).1
    have hrs : (r : ℕ) ^ (e + 1) * (s : ℕ) ^ (e + 1) =
        (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (e + 1) := by
      simpa [n, hr, hs] using hprod
    rcases equalPrimePower_pair_unordered e p q r s hpq hrs with hrs | hrs
    · apply hdeP
      simp only [Finset.mem_singleton]
      apply Prod.ext
      · simpa [P, hrs.1] using hr
      · simpa [P, hrs.2] using hs
    · apply hdeQ
      simp only [Finset.mem_singleton]
      apply Prod.ext
      · simpa [Q, hrs.1] using hr
      · simpa [Q, hrs.2] using hs
  rw [hrest]
  simp [P, Q]



end

end GaloisForLFunctions.HTGeometry
