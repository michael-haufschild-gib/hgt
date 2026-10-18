import GaloisForLFunctions.BezoutValuationIncidence.SelbergHilbertCoordinateEquivalence
import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticLagSchedulesAndSharpRecoveryHorizon

/-!
# Non-Markovian Compressed Translation Operator Algebra and Prime-Power Revival

On the periodic divisor-sieve Hilbert space `SieveCoefficientSpace N`, true integer translation
by lag `h` compresses to the self-adjoint operator `nativeSieveTranslationPredictor N h`, which is
diagonalized by the Selberg–Ramanujan isometry `weightedSelbergIsometry N` with eigenvalue
`sieveLagMultiplier q h = μ(q / gcd(q, h)) / φ(q / gcd(q, h))`.

Unlike true translation on the ambient period, compressed translation does **not** form a Markov
semigroup: `nativeSieveTranslationPredictor N (h₁ + h₂)` differs from the composition
`nativeSieveTranslationPredictor N h₁ ∘ nativeSieveTranslationPredictor N h₂` by the exact
spectral defect
`nonMarkovianLagDefect q h₁ h₂ = sieveLagMultiplier q (h₁ + h₂) - sieveLagMultiplier q h₁ * sieveLagMultiplier q h₂`.

This module establishes:
1. **The Exact Three-Regime Prime-Power Formula (`sieveLagMultiplier_prime_pow_trichotomy`):**
   For every prime `p`, exponent `a : ℕ`, and lag `h : ℕ`:
   - Full-period alignment (`p ^ (a + 1) ∣ h`): `sieveLagMultiplier (p ^ (a + 1)) h = 1`,
   - Critical visibility/revival (`p ^ a ∣ h` and `¬ p ^ (a + 1) ∣ h`):
     `sieveLagMultiplier (p ^ (a + 1)) h = -1 / (p - 1)`,
   - Sub-clock erasure (`¬ p ^ a ∣ h`): `sieveLagMultiplier (p ^ (a + 1)) h = 0`.
2. **Coprime Multiplicativity Across Arithmetic Modes (`sieveLagMultiplier_mul_of_coprime`):**
   For coprime modes `q₁, q₂` and every lag `h`,
   `sieveLagMultiplier (q₁ * q₂) h = sieveLagMultiplier q₁ h * sieveLagMultiplier q₂ h` and
   `ramanujanLagCoefficient (q₁ * q₂) h = ramanujanLagCoefficient q₁ h * ramanujanLagCoefficient q₂ h`.
3. **The Non-Markovian Prime-Power Revival Theorem (`nonMarkovianLagDefect_prime_pow_revival`):**
   For every prime `p` and `a ≥ 1`, every positive lag `1 ≤ h < p ^ a` is completely erased
   (`sieveLagMultiplier (p ^ (a + 1)) h = 0`), yet any two positive sub-clock lags `h₁, h₂ ≥ 1`
   with `h₁ + h₂ = p ^ a` combine to revive the mode at the visibility clock `p ^ a` with
   non-Markovian semigroup defect `-1 / (p - 1) ≠ 0`.
4. **Commutative Self-Adjoint Operator Algebra & Hilbert-Space Defect Identity
   (`nativeSieveTranslationPredictor_comm`, `inner_nativeSieveTranslationPredictor_left`,
   `norm_nativeNonMarkovianDefect_sq`):**
   Every `nativeSieveTranslationPredictor N h` is self-adjoint on `SieveCoefficientSpace N`, all
   lag predictors commute with one another, and the Hilbert-space norm of the non-Markovian defect
   operator is given by the totient-weighted sum of `(nonMarkovianLagDefect q h₁ h₂) ^ 2`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius InnerProductSpace

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Three-Regime Prime-Power Formula for `sieveLagMultiplier` -/

/-- When a positive mode `q` divides the lag `h`, its compressed translation multiplier is `1`. -/
theorem sieveLagMultiplier_of_dvd {q h : ℕ} (hq : q ≠ 0) (hdvd : q ∣ h) :
    sieveLagMultiplier q h = 1 := by
  rw [sieveLagMultiplier_eq_moebius_totient_quotient, Nat.gcd_eq_left hdvd,
    Nat.div_self (Nat.pos_of_ne_zero hq)]
  simp [moebiusReal]

/-- When a mode `q` divides the lag `h`, its Ramanujan lag coefficient is `φ(q)`. -/
theorem ramanujanLagCoefficient_of_dvd {q h : ℕ} (hdvd : q ∣ h) :
    ramanujanLagCoefficient q h = (q.totient : ℝ) := by
  by_cases hq : q = 0
  · subst hq; simp [ramanujanLagCoefficient]
  · rw [ramanujanLagCoefficient_eq_totient_mul, sieveLagMultiplier_of_dvd hq hdvd, mul_one]

/-- When the visibility clock `lagVisibilityClock q` does not divide `h`, `sieveLagMultiplier q h = 0`. -/
theorem sieveLagMultiplier_eq_zero_of_not_dvd_clock {q h : ℕ}
    (hndvd : ¬ lagVisibilityClock q ∣ h) :
    sieveLagMultiplier q h = 0 := by
  by_contra hne
  exact hndvd ((sieveLagMultiplier_ne_zero_iff q h).mp hne).2

/-- When `lagVisibilityClock q` does not divide `h`, `ramanujanLagCoefficient q h = 0`. -/
theorem ramanujanLagCoefficient_eq_zero_of_not_dvd_clock {q h : ℕ}
    (hndvd : ¬ lagVisibilityClock q ∣ h) :
    ramanujanLagCoefficient q h = 0 := by
  rw [ramanujanLagCoefficient_eq_totient_mul,
    sieveLagMultiplier_eq_zero_of_not_dvd_clock hndvd, mul_zero]

/-- For a prime `p`, if `p ^ a ∣ h` and `¬ p ^ (a + 1) ∣ h`, then `gcd(p ^ (a + 1), h) = p ^ a`. -/
theorem gcd_prime_pow_eq_of_dvd_of_not_dvd {p a h : ℕ}
    (hp : p.Prime) (hdvd : p ^ a ∣ h) (hndvd : ¬ p ^ (a + 1) ∣ h) :
    Nat.gcd (p ^ (a + 1)) h = p ^ a := by
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ (a + 1)) h)
  have hpa_dvd : p ^ a ∣ p ^ k := by
    rw [← hk_eq]
    exact Nat.dvd_gcd (pow_dvd_pow p (Nat.le_succ a)) hdvd
  have ha_le_k : a ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpa_dvd
  have hk_ne : k ≠ a + 1 := by
    intro hkeq
    apply hndvd
    rw [← hkeq, ← hk_eq]
    exact Nat.gcd_dvd_right (p ^ (a + 1)) h
  have hk_eq_a : k = a := by omega
  rw [hk_eq, hk_eq_a]

/-- At any critical lag `h` (`p ^ a ∣ h` and `¬ p ^ (a + 1) ∣ h`), the prime-power mode `p ^ (a + 1)`
has multiplier `-1 / (p - 1)`. -/
theorem sieveLagMultiplier_prime_pow_critical {p a h : ℕ}
    (hp : p.Prime) (hdvd : p ^ a ∣ h) (hndvd : ¬ p ^ (a + 1) ∣ h) :
    sieveLagMultiplier (p ^ (a + 1)) h = -1 / ((p : ℝ) - 1) := by
  rw [sieveLagMultiplier_eq_moebius_totient_quotient,
    gcd_prime_pow_eq_of_dvd_of_not_dvd hp hdvd hndvd]
  have hquot : p ^ (a + 1) / p ^ a = p := by
    rw [pow_succ', Nat.mul_div_cancel _ (pow_pos hp.pos a)]
  rw [hquot, moebiusReal, ArithmeticFunction.moebius_apply_prime hp,
    Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]
  simp

/-- At any critical lag `h` (`p ^ a ∣ h` and `¬ p ^ (a + 1) ∣ h`), the unnormalized Ramanujan
coefficient of `p ^ (a + 1)` is `-p ^ a`. -/
theorem ramanujanLagCoefficient_prime_pow_critical {p a h : ℕ}
    (hp : p.Prime) (hdvd : p ^ a ∣ h) (hndvd : ¬ p ^ (a + 1) ∣ h) :
    ramanujanLagCoefficient (p ^ (a + 1)) h = -((p : ℝ) ^ a) := by
  have hp1 : ((p : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  rw [ramanujanLagCoefficient_eq_totient_mul,
    sieveLagMultiplier_prime_pow_critical hp hdvd hndvd,
    Nat.totient_prime_pow hp (Nat.succ_pos a), Nat.succ_sub_one,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  field_simp [hp1]

/-- **Exact Three-Regime Prime-Power Formula (`sieveLagMultiplier_prime_pow_trichotomy`):**
For every prime `p`, exponent `a : ℕ`, and lag `h : ℕ`:
- if `p ^ (a + 1) ∣ h`, then `sieveLagMultiplier (p ^ (a + 1)) h = 1`,
- else if `p ^ a ∣ h`, then `sieveLagMultiplier (p ^ (a + 1)) h = -1 / (p - 1)`,
- else `sieveLagMultiplier (p ^ (a + 1)) h = 0`. -/
theorem sieveLagMultiplier_prime_pow_trichotomy (p a h : ℕ) (hp : p.Prime) :
    sieveLagMultiplier (p ^ (a + 1)) h =
      if p ^ (a + 1) ∣ h then 1
      else if p ^ a ∣ h then -1 / ((p : ℝ) - 1)
      else 0 := by
  split_ifs with hdvd1 hdvd0
  · exact sieveLagMultiplier_of_dvd (pow_ne_zero (a + 1) hp.ne_zero) hdvd1
  · exact sieveLagMultiplier_prime_pow_critical hp hdvd0 hdvd1
  · apply sieveLagMultiplier_eq_zero_of_not_dvd_clock
    rwa [lagVisibilityClock_prime_power p a hp]

/-! ## §2. Coprime Multiplicativity Across Arithmetic Modes -/

/-- For coprime `q₁, q₂` and any `h : ℕ`, `gcd(q₁ * q₂, h) = gcd(q₁, h) * gcd(q₂, h)`. -/
theorem gcd_mul_left_of_coprime {q₁ q₂ h : ℕ} (hcop : Nat.Coprime q₁ q₂) :
    Nat.gcd (q₁ * q₂) h = Nat.gcd q₁ h * Nat.gcd q₂ h := by
  apply Nat.dvd_antisymm
  · rw [← Nat.gcd_mul_right q₁ (Nat.gcd q₂ h) h]
    refine Nat.dvd_gcd ?_ (dvd_mul_of_dvd_left (Nat.gcd_dvd_right (q₁ * q₂) h) _)
    rw [← Nat.gcd_mul_left q₁ q₂ h]
    exact Nat.dvd_gcd (Nat.gcd_dvd_left (q₁ * q₂) h)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right (q₁ * q₂) h) q₁)
  · have hcop_gcd : Nat.Coprime (Nat.gcd q₁ h) (Nat.gcd q₂ h) :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_left q₁ h)).coprime_dvd_right (Nat.gcd_dvd_left q₂ h)
    exact Nat.dvd_gcd (mul_dvd_mul (Nat.gcd_dvd_left q₁ h) (Nat.gcd_dvd_left q₂ h))
      (hcop_gcd.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right q₁ h) (Nat.gcd_dvd_right q₂ h))

/-- **Coprime Multiplicativity of `sieveLagMultiplier` (`sieveLagMultiplier_mul_of_coprime`):**
For coprime modes `q₁, q₂ : ℕ` and every lag `h : ℕ`,
`sieveLagMultiplier (q₁ * q₂) h = sieveLagMultiplier q₁ h * sieveLagMultiplier q₂ h`. -/
theorem sieveLagMultiplier_mul_of_coprime {q₁ q₂ : ℕ} (hcop : Nat.Coprime q₁ q₂) (h : ℕ) :
    sieveLagMultiplier (q₁ * q₂) h = sieveLagMultiplier q₁ h * sieveLagMultiplier q₂ h := by
  by_cases hq₁ : q₁ = 0
  · subst hq₁
    simp only [Nat.coprime_zero_left] at hcop
    subst hcop
    simp [sieveLagMultiplier, ramanujanLagCoefficient]
  by_cases hq₂ : q₂ = 0
  · subst hq₂
    simp only [Nat.coprime_zero_right] at hcop
    subst hcop
    simp [sieveLagMultiplier, ramanujanLagCoefficient]
  rw [sieveLagMultiplier_eq_moebius_totient_quotient,
    sieveLagMultiplier_eq_moebius_totient_quotient,
    sieveLagMultiplier_eq_moebius_totient_quotient,
    gcd_mul_left_of_coprime hcop,
    Nat.mul_div_mul_comm (Nat.gcd_dvd_left q₁ h) (Nat.gcd_dvd_left q₂ h)]
  have hq₁_div_dvd : q₁ / Nat.gcd q₁ h ∣ q₁ := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q₁ h)
  have hq₂_div_dvd : q₂ / Nat.gcd q₂ h ∣ q₂ := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q₂ h)
  have hcop_quot : Nat.Coprime (q₁ / Nat.gcd q₁ h) (q₂ / Nat.gcd q₂ h) :=
    (hcop.coprime_dvd_left hq₁_div_dvd).coprime_dvd_right hq₂_div_dvd
  have hmu : moebiusReal ((q₁ / Nat.gcd q₁ h) * (q₂ / Nat.gcd q₂ h)) =
      moebiusReal (q₁ / Nat.gcd q₁ h) * moebiusReal (q₂ / Nat.gcd q₂ h) := by
    simp only [moebiusReal, isMultiplicative_moebius.map_mul_of_coprime hcop_quot, Int.cast_mul]
  have htot : (((q₁ / Nat.gcd q₁ h) * (q₂ / Nat.gcd q₂ h)).totient : ℝ) =
      ((q₁ / Nat.gcd q₁ h).totient : ℝ) * ((q₂ / Nat.gcd q₂ h).totient : ℝ) := by
    exact_mod_cast Nat.totient_mul hcop_quot
  rw [hmu, htot, div_mul_div_comm]

/-- **Coprime Multiplicativity of `ramanujanLagCoefficient` (`ramanujanLagCoefficient_mul_of_coprime`):**
For coprime modes `q₁, q₂ : ℕ` and every lag `h : ℕ`,
`ramanujanLagCoefficient (q₁ * q₂) h = ramanujanLagCoefficient q₁ h * ramanujanLagCoefficient q₂ h`. -/
theorem ramanujanLagCoefficient_mul_of_coprime {q₁ q₂ : ℕ} (hcop : Nat.Coprime q₁ q₂) (h : ℕ) :
    ramanujanLagCoefficient (q₁ * q₂) h =
      ramanujanLagCoefficient q₁ h * ramanujanLagCoefficient q₂ h := by
  rw [ramanujanLagCoefficient_eq_totient_mul, ramanujanLagCoefficient_eq_totient_mul,
    ramanujanLagCoefficient_eq_totient_mul, sieveLagMultiplier_mul_of_coprime hcop h,
    Nat.totient_mul hcop, Nat.cast_mul]
  ring

/-! ## §3. The Non-Markovian Semigroup Defect & Prime-Power Revival Theorem -/

/-- **The Non-Markovian Semigroup Defect (`nonMarkovianLagDefect`):**
Measures the failure of the compressed lag multipliers at mode `q` to satisfy the Markov semigroup
law `λ_q(h₁ + h₂) = λ_q(h₁) * λ_q(h₂)`. -/
def nonMarkovianLagDefect (q h₁ h₂ : ℕ) : ℝ :=
  sieveLagMultiplier q (h₁ + h₂) - sieveLagMultiplier q h₁ * sieveLagMultiplier q h₂

/-- Every positive sub-clock lag `1 ≤ h < p ^ a` is completely erased at mode `p ^ (a + 1)`. -/
theorem sieveLagMultiplier_prime_pow_subclock_zero {p a h : ℕ}
    (hp : p.Prime) (hhpos : 1 ≤ h) (hhlt : h < p ^ a) :
    sieveLagMultiplier (p ^ (a + 1)) h = 0 := by
  apply sieveLagMultiplier_eq_zero_of_not_dvd_clock
  rw [lagVisibilityClock_prime_power p a hp]
  intro hdvd
  have hle : p ^ a ≤ h := Nat.le_of_dvd hhpos hdvd
  omega

/-- At the visibility clock `h = p ^ a`, the prime-power mode `p ^ (a + 1)` revives with
multiplier `-1 / (p - 1)`. -/
theorem sieveLagMultiplier_prime_pow_revival_at_clock (p a : ℕ) (hp : p.Prime) :
    sieveLagMultiplier (p ^ (a + 1)) (p ^ a) = -1 / ((p : ℝ) - 1) := by
  apply sieveLagMultiplier_prime_pow_critical hp dvd_rfl
  intro hdvd
  have hle : p ^ (a + 1) ≤ p ^ a := Nat.le_of_dvd (pow_pos hp.pos a) hdvd
  have hlt : p ^ a < p ^ (a + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self a)
  omega

/-- **The Non-Markovian Prime-Power Revival Theorem (`nonMarkovianLagDefect_prime_pow_revival`):**
For every prime `p`, exponent `a : ℕ`, and positive lags `h₁, h₂ ≥ 1` whose sum equals the
visibility clock `h₁ + h₂ = p ^ a`, both individual lags are completely invisible
(`sieveLagMultiplier (p ^ (a + 1)) h₁ = 0` and `sieveLagMultiplier (p ^ (a + 1)) h₂ = 0`), while
their sum `h₁ + h₂` revives mode `p ^ (a + 1)` with non-Markovian defect `-1 / (p - 1) ≠ 0`. -/
theorem nonMarkovianLagDefect_prime_pow_revival {p a h₁ h₂ : ℕ}
    (hp : p.Prime) (h₁pos : 1 ≤ h₁) (h₂pos : 1 ≤ h₂) (hsum : h₁ + h₂ = p ^ a) :
    sieveLagMultiplier (p ^ (a + 1)) h₁ = 0 ∧
      sieveLagMultiplier (p ^ (a + 1)) h₂ = 0 ∧
      nonMarkovianLagDefect (p ^ (a + 1)) h₁ h₂ = -1 / ((p : ℝ) - 1) := by
  have hh₁ : sieveLagMultiplier (p ^ (a + 1)) h₁ = 0 :=
    sieveLagMultiplier_prime_pow_subclock_zero hp h₁pos (by omega)
  have hh₂ : sieveLagMultiplier (p ^ (a + 1)) h₂ = 0 :=
    sieveLagMultiplier_prime_pow_subclock_zero hp h₂pos (by omega)
  refine ⟨hh₁, hh₂, ?_⟩
  unfold nonMarkovianLagDefect
  rw [hsum, hh₁, hh₂, sieveLagMultiplier_prime_pow_revival_at_clock p a hp]
  ring

/-- **One-Step vs. Clock-Complement Revival (`nonMarkovianLagDefect_prime_pow_one_pred`):**
For every prime `p` and `a ≥ 1`, pairing lag `1` with lag `p ^ a - 1` produces the exact
non-Markovian revival defect `-1 / (p - 1)` at mode `p ^ (a + 1)`. -/
theorem nonMarkovianLagDefect_prime_pow_one_pred (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    nonMarkovianLagDefect (p ^ (a + 1)) 1 (p ^ a - 1) = -1 / ((p : ℝ) - 1) := by
  have hpa : 2 ≤ p ^ a := by
    calc
      2 ≤ p ^ 1 := by simpa using hp.two_le
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
  exact (nonMarkovianLagDefect_prime_pow_revival hp (le_refl 1) (by omega) (by omega)).2.2

/-- **Exact First-Octave Two-Step Non-Markovian Semigroup Defect Table
(`nonMarkovianLagDefect_first_octave_table`):**
At `h₁ = h₂ = 1` (comparing two-step compression `C₂` against iterated one-step compression `C₁²`):
- modes `q = 1` and `q = 2` are Markovian (`nonMarkovianLagDefect 1 1 1 = 0`,
  `nonMarkovianLagDefect 2 1 1 = 0`),
- the odd prime mode `q = 3` and primorial mode `q = 6` have defect `-3 / 4`,
- the prime-square Wall 11 mode `q = 4 = 2²` has pure revival defect `-1`. -/
theorem nonMarkovianLagDefect_first_octave_table :
    nonMarkovianLagDefect 1 1 1 = 0 ∧
      nonMarkovianLagDefect 2 1 1 = 0 ∧
      nonMarkovianLagDefect 3 1 1 = -3 / 4 ∧
      nonMarkovianLagDefect 4 1 1 = -1 ∧
      nonMarkovianLagDefect 6 1 1 = -3 / 4 := by
  have h1 : ∀ h : ℕ, sieveLagMultiplier 1 h = 1 :=
    fun h => sieveLagMultiplier_of_dvd (by decide) (one_dvd h)
  have h2_1 : sieveLagMultiplier 2 1 = -1 := by
    have := sieveLagMultiplier_prime_pow_critical (p := 2) (a := 0) (h := 1)
      Nat.prime_two (one_dvd 1) (by decide)
    norm_num at this ⊢
    exact this
  have h2_2 : sieveLagMultiplier 2 2 = 1 :=
    sieveLagMultiplier_of_dvd (by decide) dvd_rfl
  have h3_1 : sieveLagMultiplier 3 1 = -1 / 2 := by
    have := sieveLagMultiplier_prime_pow_critical (p := 3) (a := 0) (h := 1)
      Nat.prime_three (one_dvd 1) (by decide)
    norm_num at this ⊢
    exact this
  have h3_2 : sieveLagMultiplier 3 2 = -1 / 2 := by
    have := sieveLagMultiplier_prime_pow_critical (p := 3) (a := 0) (h := 2)
      Nat.prime_three (one_dvd 2) (by decide)
    norm_num at this ⊢
    exact this
  have h4 : nonMarkovianLagDefect 4 1 1 = -1 := by
    have := nonMarkovianLagDefect_prime_pow_one_pred 2 1 Nat.prime_two (le_refl 1)
    norm_num at this ⊢
    exact this
  have h6_1 : sieveLagMultiplier 6 1 = 1 / 2 := by
    have := sieveLagMultiplier_mul_of_coprime (q₁ := 2) (q₂ := 3) (by decide) 1
    norm_num [h2_1, h3_1] at this ⊢
    exact this
  have h6_2 : sieveLagMultiplier 6 2 = -1 / 2 := by
    have := sieveLagMultiplier_mul_of_coprime (q₁ := 2) (q₂ := 3) (by decide) 2
    norm_num [h2_2, h3_2] at this ⊢
    exact this
  refine ⟨?_, ?_, ?_, h4, ?_⟩ <;>
    unfold nonMarkovianLagDefect <;>
    norm_num [h1, h2_1, h2_2, h3_1, h3_2, h6_1, h6_2]

/-! ## §4. Commutative Self-Adjoint Operator Algebra & Hilbert-Space Defect on `SieveCoefficientSpace N` -/

/-- **Commutativity of Compressed Translation Operators (`nativeSieveTranslationPredictor_comm`):**
For every cutoff `N`, lags `h₁, h₂ : ℕ`, and signal `c : SieveCoefficientSpace N`, the compressed
translation operators at lags `h₁` and `h₂` commute. -/
theorem nativeSieveTranslationPredictor_comm (N h₁ h₂ : ℕ) (c : SieveCoefficientSpace N) :
    nativeSieveTranslationPredictor N h₁ (nativeSieveTranslationPredictor N h₂ c) =
      nativeSieveTranslationPredictor N h₂ (nativeSieveTranslationPredictor N h₁ c) := by
  apply (weightedSelbergIsometry N).injective
  ext q
  rw [weightedSelbergIsometry_translation, weightedSelbergIsometry_translation,
    weightedSelbergIsometry_translation, weightedSelbergIsometry_translation]
  ring

/-- **Self-Adjointness of Compressed Translation Operators
(`inner_nativeSieveTranslationPredictor_left`):**
Every compressed translation operator `nativeSieveTranslationPredictor N h` is self-adjoint with
respect to the native full-period inner product on `SieveCoefficientSpace N`. -/
theorem inner_nativeSieveTranslationPredictor_left (N h : ℕ)
    (b c : SieveCoefficientSpace N) :
    inner (𝕜 := ℝ) (nativeSieveTranslationPredictor N h b) c =
      inner (𝕜 := ℝ) b (nativeSieveTranslationPredictor N h c) := by
  change inner (𝕜 := ℝ) (weightedSelbergIsometry N (nativeSieveTranslationPredictor N h b))
      (weightedSelbergIsometry N c) =
    inner (𝕜 := ℝ) (weightedSelbergIsometry N b)
      (weightedSelbergIsometry N (nativeSieveTranslationPredictor N h c))
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply sum_congr rfl
  intro q _
  simp only [RCLike.inner_apply, conj_trivial, weightedSelbergIsometry_translation]
  ring

/-- **The Native Non-Markovian Semigroup Defect Operator (`nativeNonMarkovianDefect`):**
Measures the operator-level difference between compressed translation at lag `h₁ + h₂` and the
composition of compressed translations at lags `h₁` and `h₂` on `SieveCoefficientSpace N`. -/
def nativeNonMarkovianDefect (N h₁ h₂ : ℕ) (c : SieveCoefficientSpace N) :
    SieveCoefficientSpace N :=
  nativeSieveTranslationPredictor N (h₁ + h₂) c -
    nativeSieveTranslationPredictor N h₁ (nativeSieveTranslationPredictor N h₂ c)

/-- **Spectral Diagonalization of the Non-Markovian Defect Operator
(`weightedSelbergIsometry_nonMarkovianDefect`):**
Under `weightedSelbergIsometry N`, `nativeNonMarkovianDefect N h₁ h₂` acts diagonally by
multiplication with `nonMarkovianLagDefect q.val h₁ h₂`. -/
theorem weightedSelbergIsometry_nonMarkovianDefect (N h₁ h₂ : ℕ)
    (c : SieveCoefficientSpace N) (q : SieveActiveIndex N) :
    weightedSelbergIsometry N (nativeNonMarkovianDefect N h₁ h₂ c) q =
      nonMarkovianLagDefect q.val h₁ h₂ * weightedSelbergIsometry N c q := by
  unfold nativeNonMarkovianDefect nonMarkovianLagDefect
  rw [map_sub, PiLp.sub_apply, weightedSelbergIsometry_translation,
    weightedSelbergIsometry_translation, weightedSelbergIsometry_translation]
  ring

/-- **Exact Hilbert-Space Norm of the Non-Markovian Semigroup Defect
(`norm_nativeNonMarkovianDefect_sq`):**
The squared full-period norm of `nativeNonMarkovianDefect N h₁ h₂ c` equals the totient-weighted
sum of `(nonMarkovianLagDefect q h₁ h₂)²` across all active Selberg modes `q ∈ [1, N]`. -/
theorem norm_nativeNonMarkovianDefect_sq (N h₁ h₂ : ℕ) (c : SieveCoefficientSpace N) :
    ‖nativeNonMarkovianDefect N h₁ h₂ c‖ ^ 2 =
      ∑ q ∈ Icc 1 N, (q.totient : ℝ) * (nonMarkovianLagDefect q h₁ h₂) ^ 2 *
        selbergMultiplesCoord N (sieveCoefficientExtension N c) q ^ 2 := by
  change ‖weightedSelbergIsometry N (nativeNonMarkovianDefect N h₁ h₂ c)‖ ^ 2 = _
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [weightedSelbergIsometry_nonMarkovianDefect]
  change (∑ q : SieveActiveIndex N,
      (nonMarkovianLagDefect q.val h₁ h₂ * weightedSelbergLinear N c q) ^ 2) = _
  simp only [weightedSelbergLinear_apply, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← Finset.sum_coe_sort (Icc 1 N)]
  apply sum_congr rfl
  intro q _
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence
