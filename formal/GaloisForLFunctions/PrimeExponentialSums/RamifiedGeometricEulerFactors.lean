import GaloisForLFunctions.RHTower.Sieve.LocalEulerConstruction

/-!
# Removing nonlinear prime-power coefficients away from the phase denominator

Gou's Lemma 3.1 (arXiv:2610.22345) keeps every Euler coefficient at primes
dividing the phase denominator. At other primes its correction is the
first-order defect of a geometric progression. The factorization below
starts with arbitrary prime-power tables over a commutative ring.
-/

noncomputable section
open Finset RHTower.Sieve
namespace GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler
variable {R : Type*} [CommRing R]

/-- Keep the local table at protected primes and continue the other rows geometrically. -/
def geometric (q : ℕ) (A : ℕ → ℕ → R) := localEuler (fun p k =>
  if p ∣ q then A p k else (A p 1)^k)

private def delta (u : ℕ → R) (z : R) : ℕ → R
  | 0 => u 0
  | k+1 => u (k+1) - z*u k

/-- The first-order difference is an exact convolution inverse to geometric continuation. -/
private theorem telescope (u : ℕ → R) (z : R) (k : ℕ) :
    (∑ j ∈ range (k+1), delta u z j*z^(k-j)) = u k := by
  induction k with
  | zero => simp [delta]
  | succ k ih =>
    rw [sum_range_succ,Nat.sub_self,pow_zero,mul_one]
    have he : (∑ j ∈ range (k+1), delta u z j*z^(k+1-j)) =
        (∑ j ∈ range (k+1), delta u z j*z^(k-j))*z := by
      rw [sum_mul]
      apply sum_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      rw [show k+1-j=k-j+1 by omega,pow_succ,mul_assoc]
    rw [he,ih,delta]
    ring

/-- Multiplicative correction supported on powerful integers coprime to q. -/
def correction (q : ℕ) (A : ℕ → ℕ → R) := localEuler (fun p k =>
  if p ∣ q then 0 else delta (normalizedPrimePowerValue A p) (A p 1) k)

theorem geometric_local (q : ℕ) (A : ℕ → ℕ → R) (p : Nat.Primes) (k : ℕ) :
    geometric q A ((p : ℕ)^k) = if (p : ℕ) ∣ q then normalizedPrimePowerValue A p k
      else (A p 1)^k := by
  rw [geometric,localEuler_prime_pow]
  by_cases hk : k=0 <;> by_cases hp : (p : ℕ) ∣ q <;> simp [hk,hp,normalizedPrimePowerValue]

theorem correction_local (q : ℕ) (A : ℕ → ℕ → R) (p : Nat.Primes) (k : ℕ) :
    correction q A ((p : ℕ)^(k+1)) = if (p : ℕ) ∣ q then 0 else
      A p (k+1) - A p 1 * normalizedPrimePowerValue A p k := by
  simp [correction,localEuler_prime_pow,delta,normalizedPrimePowerValue]

theorem correction_prime (q : ℕ) (A : ℕ → ℕ → R) (p : Nat.Primes) :
    correction q A (p : ℕ) = 0 := by
  simpa [normalizedPrimePowerValue] using correction_local q A p 0

private theorem convolution_local (f g : ArithmeticFunction R) (p : Nat.Primes) (k : ℕ) :
    (f*g) ((p : ℕ)^k) = ∑ j ∈ range (k+1), f ((p : ℕ)^j)*g ((p : ℕ)^(k-j)) := by
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun x y => f x*g y),
    Nat.sum_divisors_prime_pow p.property]
  exact sum_congr rfl fun j hj => by rw [Nat.pow_div (Nat.lt_succ_iff.mp (mem_range.mp hj)) p.property.pos]

/-- Exact Dirichlet factorization with all ramified local data preserved. -/
theorem factorization (q : ℕ) (A : ℕ → ℕ → R) :
    correction q A * geometric q A = localEuler A := by
  apply (((localEuler_isMultiplicative _).mul (localEuler_isMultiplicative _)).eq_iff_eq_on_prime_powers
    _ _ (localEuler_isMultiplicative A)).2
  intro p k hp
  let P : Nat.Primes := ⟨p,hp⟩
  rw [convolution_local _ _ P,localEuler_prime_pow A P]
  by_cases hr : p ∣ q
  · rw [sum_eq_single 0]
    · simp [correction,geometric_local,hr,P,normalizedPrimePowerValue]
    · intro j _ hj
      obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      rw [correction_local,if_pos hr,zero_mul]
    · simp
  · have hc (j : ℕ) : correction q A ((P : ℕ)^j) =
        delta (normalizedPrimePowerValue A p) (A p 1) j := by
      cases j with
      | zero => simp [correction,delta,normalizedPrimePowerValue]
      | succ j => simp [correction_local,hr,P,delta,normalizedPrimePowerValue]
    simp only [hc,geometric_local,if_neg (show ¬ (P : ℕ) ∣ q from hr)]
    exact telescope _ _ k

/-- A surviving integer cannot contain a ramified prime or a prime to the first power. -/
theorem support (q : ℕ) (A : ℕ → ℕ → R) (n : ℕ) (hn : correction q A n ≠ 0) :
    n.Coprime q ∧ ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p := by
  have hn0 : n ≠ 0 := fun h => hn (h ▸ rfl)
  have nonzero (p : ℕ) (hp : p ∈ n.primeFactors) :
      ¬ p ∣ q ∧ 2 ≤ n.factorization p := by
    change (if n=0 then 0 else _) ≠ 0 at hn
    rw [if_neg hn0] at hn
    have hterm := fun hz => hn (prod_eq_zero hp hz)
    have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp (by simpa using hp)
    by_cases hr : p ∣ q
    · exact False.elim (hterm (if_pos hr))
    · refine ⟨hr,?_⟩
      by_contra! h
      have he : n.factorization p = 1 := by omega
      exact hterm (by simp [hr,he,delta,normalizedPrimePowerValue])
  constructor
  · by_contra h
    obtain ⟨p,hp,hnp,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    exact (nonzero p (Nat.mem_primeFactors.mpr ⟨hp,hnp,hn0⟩)).1 hpq
  · exact fun p hp => (nonzero p hp).2

/-- The rational phase denominator is unchanged in every nonzero correction term. -/
theorem denominator_preserved (q a : ℕ) (A : ℕ → ℕ → R) (d : ℕ) :
    correction q A d ≠ 0 → (a*d).gcd q = a.gcd q := by
  intro hd
  exact (support q A d hd).1.gcd_mul_right_cancel a

end GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler

#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.geometric_local
#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.correction_local
#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.correction_prime
#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.factorization
#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.support
#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.denominator_preserved
