import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedFactorisation
import GaloisForLFunctions.RHTower.Sieve.MenonFinalRangeRamareReduction

/-!
# Exact harmonic Ramaré factorization on Menon's final range

Menon's final-frequency Dirichlet polynomial is harmonic: its coefficient is `μ(n) / n`, not the
unweighted Möbius coefficient.  This module carries Ramaré's exact reciprocal multiplicity through
that harmonic normalization.  The result is the precise pointwise decomposition on the dyadic
source interval `[ceil X, floor(3X)]`: a prime-supported harmonic factor times its damped harmonic
cofactor polynomial, plus the integers with no prime factor in Menon's literal final range.
-/

namespace RHTower.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The harmonic Möbius coefficient `μ(n)/n`. -/
def harmonicMoebiusC (n : ℕ) : ℂ := ((μ n : ℤ) : ℂ) / (n : ℂ)

/-- The harmonic Möbius phase `μ(n)n⁻¹ n^{2πiw}`. -/
def harmonicMoebiusPhase (w : ℝ) (n : ℕ) : ℂ := moebiusPhase w n / (n : ℂ)

/-- The harmonic Möbius phase remains multiplicative on coprime factors, including the zero
boundary cases forced by `Nat.Coprime`. -/
theorem harmonicMoebiusPhase_mul_of_coprime (w : ℝ) (a b : ℕ)
    (h : Nat.Coprime a b) :
    harmonicMoebiusPhase w (a * b) =
      harmonicMoebiusPhase w a * harmonicMoebiusPhase w b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hb : b = 1 := by simpa [Nat.Coprime] using h
    subst hb
    simp [harmonicMoebiusPhase, moebiusPhase]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have ha1 : a = 1 := by simpa [Nat.Coprime] using h
    subst ha1
    simp [harmonicMoebiusPhase, moebiusPhase]
  rw [harmonicMoebiusPhase, harmonicMoebiusPhase, harmonicMoebiusPhase,
    moebiusPhase_mul_of_coprime w a b h]
  push_cast
  field_simp [Nat.cast_ne_zero.2 (by omega : a ≠ 0),
    Nat.cast_ne_zero.2 (by omega : b ≠ 0)]

/-- The harmonic Möbius Dirichlet polynomial is the phase-carrying harmonic sum. -/
theorem logPoly_harmonicMoebius_eq_sum_phase (s : Finset ℕ) (w : ℝ) :
    logPoly harmonicMoebiusC s w = ∑ n ∈ s, harmonicMoebiusPhase w n := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [harmonicMoebiusC, harmonicMoebiusPhase, moebiusPhase, unitLogPhase]
  ring

/-- Harmonic Ramaré cofactor coefficient `μ(m)/(m(ω_P(m)+1))`. -/
def harmonicRamareCofactorCoeff (P : Finset ℕ) (m : ℕ) : ℂ :=
  harmonicMoebiusC m / (((primeFactorsIn P m).card : ℂ) + 1)

/-- The damped harmonic cofactor sum is itself a Dirichlet polynomial. -/
theorem sum_harmonicMoebiusPhase_div_eq_logPoly (P U : Finset ℕ) (w : ℝ) :
    ∑ m ∈ U, harmonicMoebiusPhase w m /
        (((primeFactorsIn P m).card : ℂ) + 1) =
      logPoly (harmonicRamareCofactorCoeff P) U w := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [harmonicMoebiusPhase, moebiusPhase, harmonicRamareCofactorCoeff,
    harmonicMoebiusC, unitLogPhase]
  ring

/-- Exact harmonic Ramaré bilinear form. -/
def harmonicRamareBilinear (P s : Finset ℕ) (w : ℝ) : ℂ :=
  ∑ p ∈ P, harmonicMoebiusPhase w p *
    logPoly (harmonicRamareCofactorCoeff P)
      {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w

/-- Exact harmonic Ramaré factorization, including the rough remainder.  The only structural input
is that the designated finite set consists of primes. -/
theorem logPoly_harmonicMoebius_eq_ramare_add_rough {P : Finset ℕ}
    (hPprime : ∀ p ∈ P, p.Prime) (s : Finset ℕ) (w : ℝ) :
    logPoly harmonicMoebiusC s w =
      harmonicRamareBilinear P s w +
        logPoly harmonicMoebiusC {n ∈ s | primeFactorsIn P n = ∅} w := by
  classical
  have hinner : ∀ p ∈ P,
      ∑ n ∈ {n ∈ s | p ∣ n},
          harmonicMoebiusPhase w n / ((primeFactorsIn P n).card : ℂ) =
        harmonicMoebiusPhase w p *
          ∑ m ∈ {m ∈ ramareCofactorSet s p | ¬ p ∣ m},
            harmonicMoebiusPhase w m /
              (((primeFactorsIn P m).card : ℂ) + 1) := by
    intro p hp
    have hprime := hPprime p hp
    have hreindex :
        ∑ n ∈ {n ∈ s | p ∣ n},
            harmonicMoebiusPhase w n / ((primeFactorsIn P n).card : ℂ) =
          ∑ m ∈ ramareCofactorSet s p,
            harmonicMoebiusPhase w (p * m) /
              ((primeFactorsIn P (p * m)).card : ℂ) :=
      (sum_div_image_complex p {n ∈ s | p ∣ n}
        (fun n hn => (Finset.mem_filter.1 hn).2)
        (fun n => harmonicMoebiusPhase w n /
          ((primeFactorsIn P n).card : ℂ))).symm
    rw [hreindex,
      sum_ramare_bilinear_split_complex hPprime
        (harmonicMoebiusPhase_mul_of_coprime w) hprime hp]
    have hzero :
        ∑ m ∈ {m ∈ ramareCofactorSet s p | p ∣ m},
            harmonicMoebiusPhase w (p * m) /
              ((primeFactorsIn P (p * m)).card : ℂ) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [harmonicMoebiusPhase, moebiusPhase_eq_zero_of_dvd hprime
        (Finset.mem_filter.1 hm).2 w, zero_div, zero_div]
    rw [hzero, add_zero]
  rw [logPoly_harmonicMoebius_eq_sum_phase,
    sum_eq_ramare_add_rough_complex P s (harmonicMoebiusPhase w),
    harmonicRamareBilinear]
  have hb :
      (∑ p ∈ P, ∑ n ∈ {n ∈ s | p ∣ n},
          harmonicMoebiusPhase w n / ((primeFactorsIn P n).card : ℂ)) =
        ∑ p ∈ P, harmonicMoebiusPhase w p *
          logPoly (harmonicRamareCofactorCoeff P)
            {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hinner p hp, sum_harmonicMoebiusPhase_div_eq_logPoly]
  rw [hb, logPoly_harmonicMoebius_eq_sum_phase]

/-- Menon's dyadic source interval `[ceil X, floor(3X)]`. -/
def menonFinalRangeShell (x : ℝ) : Finset ℕ :=
  Finset.Icc ⌈x⌉₊ (menonFinalRangeTopNat x)

/-- Unconditional exact harmonic Ramaré factorization on Menon's literal final prime range and
dyadic source interval. -/
theorem logPoly_harmonicMoebius_eq_menonFinalRange_ramare_add_rough (x w : ℝ) :
    logPoly harmonicMoebiusC (menonFinalRangeShell x) w =
      harmonicRamareBilinear (menonFinalRangePrimes x) (menonFinalRangeShell x) w +
        logPoly harmonicMoebiusC
          {n ∈ menonFinalRangeShell x |
            primeFactorsIn (menonFinalRangePrimes x) n = ∅} w := by
  exact logPoly_harmonicMoebius_eq_ramare_add_rough
    (fun p hp => menonFinalRangePrimes_prime x hp) (menonFinalRangeShell x) w

end

end RHTower.Sieve
