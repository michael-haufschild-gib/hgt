import GaloisForLFunctions.RHTower.Sieve.RamareDecomposition
import GaloisForLFunctions.RHTower.Sieve.LowHeightMoebius
import GaloisForLFunctions.RHTower.Sieve.MRFibreReduction

/-!
# The Möbius Dirichlet polynomial as a bilinear form in a designated prime

Ramaré's weighted factorisation is bilinear up to a remainder counted by multiples.  The Gallagher
phase is completely multiplicative on positive integers,

```text
(p·m)^{2πiw} = p^{2πiw}·m^{2πiw} ,
```

so the whole decomposition carries the phase, and the Möbius Dirichlet polynomial becomes

```text
∑_{n ∈ s} μ(n)·n^{2πiw}
  = ∑_{p ∈ P} ( μ(p)·p^{2πiw} ) · ( ∑_{p ∤ m} (μ(m)/(ω_P(m)+1))·m^{2πiw} )  +  E ,
```

with `E` bounded by the number of cofactors divisible by the designated prime plus the number of
integers with no designated prime factor.  The first factor is a **prime-supported** polynomial and
the second a cofactor polynomial: exactly the shape the factorised mean-square split consumes, where
the prime support supplies the near-diagonal weight `q/log q` in place of `q`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-- **The Gallagher phase is multiplicative on positive integers.** -/
theorem unitLogPhase_mul (w : ℝ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    unitLogPhase w (a * b) = unitLogPhase w a * unitLogPhase w b := by
  have hlog : Real.log ((a * b : ℕ) : ℝ) = Real.log (a : ℝ) + Real.log (b : ℝ) := by
    push_cast
    exact Real.log_mul (Nat.cast_ne_zero.2 ha) (Nat.cast_ne_zero.2 hb)
  rw [unitLogPhase, unitLogPhase, unitLogPhase, hlog, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Möbius coefficient carrying the Gallagher phase. -/
def moebiusPhase (w : ℝ) (n : ℕ) : ℂ := ((μ n : ℤ) : ℂ) * unitLogPhase w n

theorem norm_moebiusPhase_le_one (w : ℝ) (n : ℕ) : ‖moebiusPhase w n‖ ≤ 1 := by
  rw [moebiusPhase, norm_mul, norm_unitLogPhase, mul_one]
  have hnorm : ‖((μ n : ℤ) : ℂ)‖ = |((μ n : ℤ) : ℝ)| := by
    rw [show (((μ n : ℤ)) : ℂ) = ((((μ n : ℤ) : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  exact abs_moebius_real_le_one n

theorem moebiusPhase_mul_of_coprime (w : ℝ) (a b : ℕ) (h : Nat.Coprime a b) :
    moebiusPhase w (a * b) = moebiusPhase w a * moebiusPhase w b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hb : b = 1 := by simpa [Nat.Coprime] using h
    subst hb
    simp [moebiusPhase]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have ha1 : a = 1 := by simpa [Nat.Coprime] using h
    subst ha1
    simp [moebiusPhase]
  have hmu : μ (a * b) = μ a * μ b :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
  rw [moebiusPhase, moebiusPhase, moebiusPhase, hmu,
    unitLogPhase_mul w (by omega : a ≠ 0) (by omega : b ≠ 0)]
  push_cast
  ring

/-- **A multiplicative complex weight factors on a coprime factorisation.** -/
theorem map_mul_prime_of_not_dvd_complex {g : ℕ → ℂ}
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b) {p m : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ m) :
    g (p * m) = g p * g m :=
  hmul p m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)

/-- **The bilinear split of a Ramaré inner sum, complex weight.** -/
theorem sum_ramare_bilinear_split_complex {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {g : ℕ → ℂ} (hmul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b)
    {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) (T : Finset ℕ) :
    ∑ m ∈ T, g (p * m) / ((primeFactorsIn P (p * m)).card : ℂ)
      = g p * (∑ m ∈ {m ∈ T | ¬ p ∣ m}, g m / (((primeFactorsIn P m).card : ℂ) + 1))
        + ∑ m ∈ {m ∈ T | p ∣ m}, g (p * m) / ((primeFactorsIn P (p * m)).card : ℂ) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun m => p ∣ m)
    (fun m => g (p * m) / ((primeFactorsIn P (p * m)).card : ℂ))
  have hcop : ∀ m ∈ {m ∈ T | ¬ p ∣ m},
      g (p * m) / ((primeFactorsIn P (p * m)).card : ℂ)
        = g p * (g m / (((primeFactorsIn P m).card : ℂ) + 1)) := by
    intro m hm
    have hpm : ¬ p ∣ m := (Finset.mem_filter.mp hm).2
    rw [map_mul_prime_of_not_dvd_complex hmul hp hpm,
      card_primeFactorsIn_mul_prime hPprime hp hpP hpm]
    push_cast
    ring
  have hcopsum : ∑ m ∈ {m ∈ T | ¬ p ∣ m},
      g (p * m) / ((primeFactorsIn P (p * m)).card : ℂ)
      = g p * ∑ m ∈ {m ∈ T | ¬ p ∣ m}, g m / (((primeFactorsIn P m).card : ℂ) + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hcop
  rw [← hsplit, hcopsum]
  ring

/-- **The Ramaré remainder is at most the number of terms, complex weight.** -/
theorem norm_ramare_remainder_le_complex {P : Finset ℕ} {g : ℕ → ℂ} (hg : ∀ n, ‖g n‖ ≤ 1)
    {p : ℕ} (hpP : p ∈ P) (T : Finset ℕ) :
    ‖∑ m ∈ {m ∈ T | p ∣ m}, g (p * m) / ((primeFactorsIn P (p * m)).card : ℂ)‖
      ≤ (({m ∈ T | p ∣ m}).card : ℝ) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ m ∈ {m ∈ T | p ∣ m},
      ‖g (p * m) / ((primeFactorsIn P (p * m)).card : ℂ)‖ ≤ 1 := by
    intro m _
    have hω : (1 : ℝ) ≤ ((primeFactorsIn P (p * m)).card : ℝ) := by
      exact_mod_cast one_le_card_primeFactorsIn_mul hpP m
    rw [norm_div]
    have hcast : ‖(((primeFactorsIn P (p * m)).card : ℕ) : ℂ)‖
        = ((primeFactorsIn P (p * m)).card : ℝ) := by
      rw [Complex.norm_natCast]
    rw [hcast, div_le_one (by linarith)]
    have := hg (p * m)
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The cofactor set of a designated prime. -/
def ramareCofactorSet (s : Finset ℕ) (p : ℕ) : Finset ℕ :=
  ({n ∈ s | p ∣ n}).image (fun n => n / p)

/-- **The Ramaré inner sum is bilinear up to a counted remainder, complex weight.** -/
theorem norm_ramare_inner_sub_bilinear_le_complex {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {g : ℕ → ℂ} (hmul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b)
    (hg : ∀ n, ‖g n‖ ≤ 1) {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) (T : Finset ℕ) :
    ‖(∑ m ∈ T, g (p * m) / ((primeFactorsIn P (p * m)).card : ℂ))
        - g p * (∑ m ∈ {m ∈ T | ¬ p ∣ m}, g m / (((primeFactorsIn P m).card : ℂ) + 1))‖
      ≤ (({m ∈ T | p ∣ m}).card : ℝ) := by
  classical
  rw [sum_ramare_bilinear_split_complex hPprime hmul hp hpP T, add_sub_cancel_left]
  exact norm_ramare_remainder_le_complex hg hpP T

/-- The Möbius Dirichlet polynomial is the phase-carrying Möbius sum. -/
theorem logPoly_moebius_eq_sum_moebiusPhase (s : Finset ℕ) (w : ℝ) :
    logPoly (fun n => ((μ n : ℤ) : ℂ)) s w = ∑ n ∈ s, moebiusPhase w n := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [moebiusPhase, unitLogPhase]

/-- The cofactor coefficients of the Ramaré factorisation: the Möbius function damped by the
number of designated prime factors of the cofactor. -/
def ramareCofactorCoeff (P : Finset ℕ) (m : ℕ) : ℂ :=
  ((μ m : ℤ) : ℂ) / (((primeFactorsIn P m).card : ℂ) + 1)

theorem sum_moebiusPhase_div_eq_logPoly (P U : Finset ℕ) (w : ℝ) :
    ∑ m ∈ U, moebiusPhase w m / (((primeFactorsIn P m).card : ℂ) + 1)
      = logPoly (ramareCofactorCoeff P) U w := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [moebiusPhase, ramareCofactorCoeff, unitLogPhase]
  ring

/-- **The Möbius Dirichlet polynomial is a bilinear form in a designated prime, up to a counted
error.**  The prime factor `μ(p)·p^{2πiw}` is a prime-supported Dirichlet polynomial and the
cofactor factor is a Dirichlet polynomial of length `|s|/p`; the error counts the cofactors still
divisible by the designated prime together with the integers carrying no designated prime factor. -/
theorem norm_logPoly_moebius_sub_ramare_bilinear_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    (s : Finset ℕ) (w : ℝ) :
    ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) s w
        - ∑ p ∈ P, moebiusPhase w p
            * logPoly (ramareCofactorCoeff P) {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w‖
      ≤ (∑ p ∈ P, (({m ∈ ramareCofactorSet s p | p ∣ m}).card : ℝ))
        + (({n ∈ s | primeFactorsIn P n = ∅}).card : ℝ) := by
  classical
  have hmul := moebiusPhase_mul_of_coprime w
  have hg := norm_moebiusPhase_le_one w
  have hgoal : ∑ p ∈ P, moebiusPhase w p
        * logPoly (ramareCofactorCoeff P) {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w
      = ∑ p ∈ P, moebiusPhase w p
        * ∑ m ∈ {m ∈ ramareCofactorSet s p | ¬ p ∣ m},
            moebiusPhase w m / (((primeFactorsIn P m).card : ℂ) + 1) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [sum_moebiusPhase_div_eq_logPoly]
  have hinner : ∀ p ∈ P,
      ∑ n ∈ {n ∈ s | p ∣ n}, moebiusPhase w n / ((primeFactorsIn P n).card : ℂ)
        = ∑ m ∈ ramareCofactorSet s p,
            moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ) :=
    fun p _ => (sum_div_image_complex p {n ∈ s | p ∣ n}
      (fun n hn => (Finset.mem_filter.1 hn).2)
      (fun n => moebiusPhase w n / ((primeFactorsIn P n).card : ℂ))).symm
  rw [logPoly_moebius_eq_sum_moebiusPhase, hgoal,
    sum_eq_ramare_add_rough_complex P s (moebiusPhase w), Finset.sum_congr rfl hinner]
  have hrearr :
      ((∑ p ∈ P, ∑ m ∈ ramareCofactorSet s p,
            moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ))
          + ∑ n ∈ {n ∈ s | primeFactorsIn P n = ∅}, moebiusPhase w n)
        - ∑ p ∈ P, moebiusPhase w p
            * ∑ m ∈ {m ∈ ramareCofactorSet s p | ¬ p ∣ m},
                moebiusPhase w m / (((primeFactorsIn P m).card : ℂ) + 1)
      = (∑ p ∈ P, ((∑ m ∈ ramareCofactorSet s p,
              moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ))
            - moebiusPhase w p
              * ∑ m ∈ {m ∈ ramareCofactorSet s p | ¬ p ∣ m},
                  moebiusPhase w m / (((primeFactorsIn P m).card : ℂ) + 1)))
        + ∑ n ∈ {n ∈ s | primeFactorsIn P n = ∅}, moebiusPhase w n := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hrearr]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
    exact norm_ramare_inner_sub_bilinear_le_complex hPprime hmul hg (hPprime p hp) hp _
  · refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun n _ => hg n) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end RHTower.Sieve

end
