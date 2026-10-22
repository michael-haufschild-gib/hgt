import GaloisForLFunctions.RHTower.Sieve.SelbergPrincipalOriginalCoefficients

/-!
# Selberg Euler correction coefficients at prime powers

The bivariate Euler correction coefficient is
`selbergEulerCorrectionCoeff m n = ∑_{r | gcd(m, n)} μ(r)/r^2 · A_r(m/r) · A_r(n/r)`, where `A_r` is
the reciprocal Möbius amplitude `μ * (1/n)` restricted to integers whose prime factors divide `r`.
This module evaluates it on pairs of powers of one prime `p`: it vanishes when exactly one argument
is a nontrivial power of `p` and the other is `1`, and on two nontrivial powers only the divisor
`r = p` contributes.

## Main results

- `selbergEulerCorrectionCoeff_prime_pow_succ_one`: `coeff(p^(i+1), 1) = 0`.
- `selbergEulerCorrectionCoeff_one_prime_pow_succ`: `coeff(1, p^(j+1)) = 0`.
- `selbergEulerCorrectionCoeff_prime_pow_succ`:
  `coeff(p^(i+1), p^(j+1)) = -(1/p^2) · A(p^i) · A(p^j)` with `A = reciprocalMoebiusAmplitude`.

## Hypotheses

Unconditional; `p` is assumed prime.
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- For a prime `p`, the Euler correction coefficient vanishes at `(p^(i+1), 1)`. -/
theorem selbergEulerCorrectionCoeff_prime_pow_succ_one
    {p i : ℕ} (hp : p.Prime) :
    selbergEulerCorrectionCoeff (p ^ (i + 1)) 1 = 0 := by
  rw [selbergEulerCorrectionCoeff, if_neg (by simp [hp.ne_zero])]
  have hgcd : Nat.gcd (p ^ (i + 1)) 1 = 1 := Nat.gcd_one_right _
  rw [hgcd]
  let z₀ : {r // r ∈ (1 : ℕ).divisors} := ⟨1, by simp⟩
  rw [Fintype.sum_eq_single z₀]
  · simp [z₀, selbergCorrectionWeight,
      localizedReciprocalMoebiusAmplitude_prime_pow_succ_of_not_dvd hp hp.not_dvd_one]
  · intro z hz
    exfalso
    apply hz
    apply Subtype.ext
    exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors z.2)

/-- For a prime `p`, the Euler correction coefficient vanishes at `(1, p^(j+1))`. -/
theorem selbergEulerCorrectionCoeff_one_prime_pow_succ
    {p j : ℕ} (hp : p.Prime) :
    selbergEulerCorrectionCoeff 1 (p ^ (j + 1)) = 0 := by
  rw [selbergEulerCorrectionCoeff, if_neg (by simp [hp.ne_zero])]
  have hgcd : Nat.gcd 1 (p ^ (j + 1)) = 1 := Nat.gcd_one_left _
  rw [hgcd]
  let z₀ : {r // r ∈ (1 : ℕ).divisors} := ⟨1, by simp⟩
  rw [Fintype.sum_eq_single z₀]
  · simp [z₀, selbergCorrectionWeight,
      localizedReciprocalMoebiusAmplitude_prime_pow_succ_of_not_dvd hp hp.not_dvd_one]
  · intro z hz
    exfalso
    apply hz
    apply Subtype.ext
    exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors z.2)

private theorem gcd_prime_pow_eq_pow_min {p i j : ℕ} :
    Nat.gcd (p ^ i) (p ^ j) = p ^ min i j := by
  rcases le_total i j with hij | hji
  · rw [min_eq_left hij, Nat.gcd_eq_left_iff_dvd.mpr (pow_dvd_pow p hij)]
  · rw [min_eq_right hji, Nat.gcd_eq_right_iff_dvd.mpr (pow_dvd_pow p hji)]

/-- For a prime `p`, `selbergEulerCorrectionCoeff (p^(i+1)) (p^(j+1)) = -(1/p^2) · A(p^i) · A(p^j)`,
where `A = reciprocalMoebiusAmplitude`; only the divisor `r = p` of the gcd contributes. -/
theorem selbergEulerCorrectionCoeff_prime_pow_succ
    {p i j : ℕ} (hp : p.Prime) :
    selbergEulerCorrectionCoeff (p ^ (i + 1)) (p ^ (j + 1)) =
      (-(1 : ℝ) / ((p : ℝ) ^ (2 : ℕ))) *
        reciprocalMoebiusAmplitude (p ^ i) * reciprocalMoebiusAmplitude (p ^ j) := by
  rw [selbergEulerCorrectionCoeff, if_neg (by simp [hp.ne_zero])]
  change (∑ r ∈ (Nat.gcd (p ^ (i + 1)) (p ^ (j + 1))).divisors.attach,
      selbergCorrectionWeight r.1 ((p ^ (i + 1)) / r.1)
        ((p ^ (j + 1)) / r.1)) = _
  rw [show (∑ r ∈ (Nat.gcd (p ^ (i + 1)) (p ^ (j + 1))).divisors.attach,
        selbergCorrectionWeight r.1 ((p ^ (i + 1)) / r.1)
          ((p ^ (j + 1)) / r.1)) =
      ∑ r ∈ (Nat.gcd (p ^ (i + 1)) (p ^ (j + 1))).divisors,
        selbergCorrectionWeight r ((p ^ (i + 1)) / r)
          ((p ^ (j + 1)) / r) by
      simpa only using (Finset.sum_attach
        (Nat.gcd (p ^ (i + 1)) (p ^ (j + 1))).divisors
        (fun r : ℕ => selbergCorrectionWeight r ((p ^ (i + 1)) / r)
          ((p ^ (j + 1)) / r)))]
  rw [gcd_prime_pow_eq_pow_min, Nat.sum_divisors_prime_pow hp]
  rw [Finset.sum_eq_single 1]
  · have hpi : p ^ (i + 1) / p ^ (1 : ℕ) = p ^ i := by
      simpa using Nat.pow_div (x := p) (m := i + 1) (n := 1) (by omega) hp.pos
    have hpj : p ^ (j + 1) / p ^ (1 : ℕ) = p ^ j := by
      simpa using Nat.pow_div (x := p) (m := j + 1) (n := 1) (by omega) hp.pos
    rw [hpi, hpj, pow_one, selbergCorrectionWeight,
      ArithmeticFunction.moebius_apply_prime hp,
      localizedReciprocalMoebiusAmplitude_prime_pow_of_dvd hp (dvd_refl p),
      localizedReciprocalMoebiusAmplitude_prime_pow_of_dvd hp (dvd_refl p)]
    push_cast
    ring
  · intro k hk hk1
    have hklt : k < min (i + 1) (j + 1) + 1 := Finset.mem_range.mp hk
    rcases eq_or_ne k 0 with rfl | hk0
    · simp [selbergCorrectionWeight,
        localizedReciprocalMoebiusAmplitude_prime_pow_succ_of_not_dvd hp hp.not_dvd_one]
    · have hk2 : k ≠ 1 := by exact fun h1 => hk1 h1
      rw [selbergCorrectionWeight,
        ArithmeticFunction.moebius_apply_prime_pow hp hk0, if_neg hk2]
      norm_num
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

end

end RHTower.Sieve
