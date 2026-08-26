import GaloisForLFunctions.RHTower.Sieve.LocalizedReciprocalMoebiusAmplitude
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion
import GaloisForLFunctions.HTGeometry.PrimeRadialFusionNaturality

/-!
# Smooth-prime convolution for coprime Möbius weights

The reciprocal weight supported on integers whose prime factors divide `r` is multiplicative.
Its Dirichlet convolution with `μ(n) / n` removes exactly the coefficients not coprime to `r`.
This is the coefficient identity behind the smooth-semigroup expansion in the uniform coprime
logarithmic Möbius estimate.
-/

namespace RHTower.Sieve

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reciprocal weight restricted to integers supported on primes dividing `r`. -/
def primeSupportedReciprocal (r : ℕ) : ArithmeticFunction ℝ :=
  by
    classical
    exact ⟨fun n => if primeSupportedOn r n then reciprocalNatArithmetic n else 0, by simp⟩

@[simp] theorem primeSupportedReciprocal_one (r : ℕ) :
    primeSupportedReciprocal r 1 = 1 := by
  classical
  simp [primeSupportedReciprocal]

theorem primeSupportedReciprocal_apply_of_supported {r n : ℕ}
    (h : primeSupportedOn r n) :
    primeSupportedReciprocal r n = reciprocalNatArithmetic n := by
  classical
  simp [primeSupportedReciprocal, h]

theorem primeSupportedReciprocal_apply_of_not_supported {r n : ℕ}
    (h : ¬ primeSupportedOn r n) : primeSupportedReciprocal r n = 0 := by
  classical
  simp [primeSupportedReciprocal, h]

theorem isMultiplicative_primeSupportedReciprocal (r : ℕ) :
    (primeSupportedReciprocal r).IsMultiplicative := by
  classical
  constructor
  · exact primeSupportedReciprocal_one r
  · intro m n hmn
    have hrecip := isMultiplicative_reciprocalNatArithmetic.map_mul_of_coprime hmn
    by_cases hm : primeSupportedOn r m <;>
      by_cases hn : primeSupportedOn r n <;>
      simp [primeSupportedReciprocal, primeSupportedOn_mul_iff, hm, hn, hrecip]

/-- Möbius reciprocal weight restricted to integers coprime to `r`. -/
def coprimeMoebiusDiv (r : ℕ) : ArithmeticFunction ℝ :=
  by
    classical
    exact ⟨fun n => if Nat.Coprime r n then moebiusDiv n else 0, by simp⟩

theorem coprimeMoebiusDiv_apply (r n : ℕ) :
    coprimeMoebiusDiv r n =
      if Nat.Coprime r n then ((μ n : ℤ) : ℝ) / (n : ℝ) else 0 := by
  classical
  simp [coprimeMoebiusDiv, moebiusDiv_apply]

@[simp] theorem coprimeMoebiusDiv_one (r : ℕ) : coprimeMoebiusDiv r 1 = 1 := by
  classical
  simp [coprimeMoebiusDiv, moebiusDiv_apply]

theorem isMultiplicative_coprimeMoebiusDiv (r : ℕ) :
    (coprimeMoebiusDiv r).IsMultiplicative := by
  classical
  constructor
  · exact coprimeMoebiusDiv_one r
  · intro m n hmn
    have hmob := isMultiplicative_moebiusDiv.map_mul_of_coprime hmn
    change (if Nat.Coprime r (m * n) then moebiusDiv (m * n) else 0) =
      (if Nat.Coprime r m then moebiusDiv m else 0) *
        (if Nat.Coprime r n then moebiusDiv n else 0)
    simp only [Nat.coprime_mul_iff_right]
    by_cases hm : Nat.Coprime r m
    · by_cases hn : Nat.Coprime r n
      · rw [if_pos ⟨hm, hn⟩, if_pos hm, if_pos hn, hmob]
      · rw [if_neg (fun h => hn h.2), if_pos hm, if_neg hn, mul_zero]
    · rw [if_neg (fun h => hm h.1), if_neg hm, zero_mul]

private theorem sum_nat_antidiagonal_eq_sum_range
    (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n, f x.1 x.2) =
      ∑ i ∈ Finset.range (n + 1), f i (n - i) := by
  apply Finset.sum_nbij'
    (i := fun x => x.1)
    (j := fun i => (i, n - i))
  · intro x hx
    rw [Finset.mem_range]
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega
  · intro i hi
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    rw [Finset.mem_range] at hi
    omega
  · intro x hx
    apply Prod.ext
    · rfl
    · have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      omega
  · intro i _
    rfl
  · intro x hx
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [show x.2 = n - x.1 by omega]

theorem primeSupportedReciprocal_prime_pow {r p i : ℕ} (hp : p.Prime) :
    primeSupportedReciprocal r (p ^ i) =
      if i = 0 ∨ p ∣ r then 1 / ((p ^ i : ℕ) : ℝ) else 0 := by
  classical
  rcases i with _ | i
  · simp
  · have hpow : primeSupportedOn r (p ^ (i + 1)) ↔ p ∣ r :=
      primeSupportedOn_prime_pow_iff hp (by omega)
    by_cases hpr : p ∣ r
    · rw [if_pos (Or.inr hpr), primeSupportedReciprocal_apply_of_supported (hpow.mpr hpr),
        reciprocalNatArithmetic_apply (pow_ne_zero _ hp.ne_zero)]
    · rw [if_neg (not_or_intro (by omega) hpr),
        primeSupportedReciprocal_apply_of_not_supported (fun h => hpr (hpow.mp h))]

private theorem coprimeMoebiusDiv_prime_pow {r p i : ℕ} (hp : p.Prime) :
    coprimeMoebiusDiv r (p ^ i) =
      if p ∣ r ∧ i ≠ 0 then 0 else moebiusDiv (p ^ i) := by
  classical
  rcases i with _ | i
  · simp
  · change (if Nat.Coprime r (p ^ (i + 1)) then moebiusDiv (p ^ (i + 1)) else 0) =
      if p ∣ r ∧ i + 1 ≠ 0 then 0 else moebiusDiv (p ^ (i + 1))
    have hcop : Nat.Coprime r (p ^ (i + 1)) ↔ ¬ p ∣ r := by
      rw [Nat.coprime_pow_right_iff (by omega) r p, Nat.coprime_comm,
        hp.coprime_iff_not_dvd]
    by_cases hpr : p ∣ r <;> simp [hpr, hcop]

private theorem convolution_primeSupportedReciprocal_moebiusDiv_prime_pow
    {r p i : ℕ} (hp : p.Prime) :
    (primeSupportedReciprocal r * moebiusDiv) (p ^ i) =
      coprimeMoebiusDiv r (p ^ i) := by
  classical
  rcases i with _ | i
  · simp
  · rw [ArithmeticFunction.mul_apply,
      GaloisForLFunctions.HTGeometry.divisorsAntidiagonal_prime_pow
        (⟨p, hp⟩ : Nat.Primes) (i + 1),
      Finset.sum_map]
    change (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) (i + 1),
      primeSupportedReciprocal r (p ^ x.1) * moebiusDiv (p ^ x.2)) = _
    rw [show
      (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) (i + 1),
        primeSupportedReciprocal r (p ^ x.1) * moebiusDiv (p ^ x.2)) =
        ∑ j ∈ Finset.range (i + 2),
          primeSupportedReciprocal r (p ^ j) * moebiusDiv (p ^ (i + 1 - j))
      from sum_nat_antidiagonal_eq_sum_range
        (fun a b => primeSupportedReciprocal r (p ^ a) * moebiusDiv (p ^ b)) (i + 1)]
    rw [coprimeMoebiusDiv_prime_pow hp]
    by_cases hpr : p ∣ r
    · rw [if_pos ⟨hpr, by omega⟩]
      have hterms : ∀ j ∈ Finset.range (i + 2),
          primeSupportedReciprocal r (p ^ j) * moebiusDiv (p ^ (i + 1 - j)) =
            if j = i then -(1 / ((p ^ (i + 1) : ℕ) : ℝ))
            else if j = i + 1 then 1 / ((p ^ (i + 1) : ℕ) : ℝ) else 0 := by
        intro j hj
        have hjlt : j < i + 2 := Finset.mem_range.mp hj
        rw [primeSupportedReciprocal_prime_pow hp, if_pos (Or.inr hpr), moebiusDiv_apply]
        by_cases hj1 : j = i + 1
        · subst j
          simp
        · by_cases hj0 : j = i
          · subst j
            simp [ArithmeticFunction.moebius_apply_prime hp]
            rw [pow_succ]
            field_simp
          · have hexp : 2 ≤ i + 1 - j := by omega
            rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
            simp [hj0, hj1]
      rw [Finset.sum_congr rfl hterms]
      have hi : i < i + 2 := by omega
      have hi1 : i + 1 < i + 2 := by omega
      calc
        (∑ j ∈ Finset.range (i + 2),
            if j = i then -(1 / ((p ^ (i + 1) : ℕ) : ℝ))
            else if j = i + 1 then 1 / ((p ^ (i + 1) : ℕ) : ℝ) else 0) =
            (∑ j ∈ Finset.range (i + 2),
              if j = i then -(1 / ((p ^ (i + 1) : ℕ) : ℝ)) else 0) +
            ∑ j ∈ Finset.range (i + 2),
              if j = i + 1 then 1 / ((p ^ (i + 1) : ℕ) : ℝ) else 0 := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro j _
                by_cases hj0 : j = i <;> by_cases hj1 : j = i + 1 <;>
                  simp [hj0, hj1]
        _ = 0 := by
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [hi, hi1]
    · rw [if_neg (fun h => hpr h.1)]
      have hterms : ∀ j ∈ Finset.range (i + 2),
          primeSupportedReciprocal r (p ^ j) * moebiusDiv (p ^ (i + 1 - j)) =
            if j = 0 then moebiusDiv (p ^ (i + 1)) else 0 := by
        intro j hj
        rw [primeSupportedReciprocal_prime_pow hp]
        by_cases hj0 : j = 0
        · subst j
          simp
        · rw [if_neg (not_or_intro hj0 hpr)]
          simp [hj0]
      rw [Finset.sum_congr rfl hterms, Finset.sum_ite_eq']
      simp

/-- Smooth-prime reciprocal convolution removes exactly the primes dividing the modulus. -/
theorem primeSupportedReciprocal_mul_moebiusDiv (r : ℕ) :
    primeSupportedReciprocal r * moebiusDiv = coprimeMoebiusDiv r := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    (primeSupportedReciprocal r * moebiusDiv)
    ((isMultiplicative_primeSupportedReciprocal r).mul isMultiplicative_moebiusDiv)
    (coprimeMoebiusDiv r) (isMultiplicative_coprimeMoebiusDiv r)).2
  intro p i hp
  exact convolution_primeSupportedReciprocal_moebiusDiv_prime_pow hp

end

end RHTower.Sieve
