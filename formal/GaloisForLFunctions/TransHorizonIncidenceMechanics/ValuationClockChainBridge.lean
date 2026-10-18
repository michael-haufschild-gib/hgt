import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticLagSchedulesAndSharpRecoveryHorizon
import GaloisForLFunctions.RHTower.CHMDPrimeChainVariance

/-!
# Pillar I: Valuation-Clock & Prime-Chain Bridge (`ValuationClockChainBridge`)

This first foundational pillar of **Trans-Horizon Arithmetic–Archimedean Incidence Mechanics**
unifies the two previously disconnected multiplicative engines of the repository:
1. The **additive translation visibility clock**
   `lagVisibilityClock q = q / ∏ p ∈ q.primeFactors, p` from `BezoutValuationIncidence`
   (`ValuationVisibilityClockAndRamanujanSupport`), which governs the exact integer translation lag
   `h` at which Selberg mode `q` becomes visible (`sieveLagMultiplier q h ≠ 0 ↔ q ≠ 0 ∧ lagVisibilityClock q ∣ h`).
2. The **multiplicative prime-power chain variance decomposition**
   (`ordCompl[p] m = ordCompl[p] k`, `mangoldt_edge_eq_chain_sum`, `divisor_cut_eq_chainVariance`)
   from `RHTower.CHMDPrimeChain` (`CHMDPrimeChainVariance`), which factors the prime-crossing Doob
   energy along complete bipartite prime-power chains with constant edge weight `Λ(p^r) = log p`.

## Core Main Theorems (100% Unconditional)

1. **Radical Quotient Identity & Exact Valuation-Clock Reconstruction of `vonMangoldt`
   (`lagVisibilityClock_mul_rad`, `div_lagVisibilityClock_eq_rad`,
   `prime_div_lagVisibilityClock_iff_isPrimePow`,
   `vonMangoldt_eq_log_div_lagVisibilityClock`)**:
   For every `d : ℕ`:
   - If `d ≠ 0`, `d / lagVisibilityClock d = ∏ p ∈ d.primeFactors, p` is the squarefree radical of `d`.
   - `Nat.Prime (d / lagVisibilityClock d) ↔ IsPrimePow d`.
   - Consequently, the von Mangoldt weight `Λ(d)` is reconstructed **for all `d : ℕ`** from the
     quotient of `d` by its additive translation visibility clock:
     $$\Lambda(d) = \begin{cases}
       \log\bigl(d / \operatorname{lagVisibilityClock}(d)\bigr) &
         \text{if } \operatorname{Nat.Prime}\bigl(d / \operatorname{lagVisibilityClock}(d)\bigr), \\
       0 & \text{otherwise.}
     \end{cases}$$

2. **Exact Ramanujan Lag Multiplier & Coefficient at the Prime-Power Visibility Clock
   (`sieveLagMultiplier_prime_power_at_clock`, `ramanujanLagCoefficient_prime_power_at_clock`,
   `sieveLagMultiplier_prime_power_eq_zero_of_lt_clock`)**:
   For every prime `p` and exponent `a : ℕ`, the prime-power mode `q = p ^ (a + 1)` has visibility
   clock `lagVisibilityClock (p ^ (a + 1)) = p ^ a`, is completely invisible at every positive lag
   `1 ≤ h < p ^ a`, and at its visibility clock `h = p ^ a` has exact Ramanujan lag multiplier and
   coefficient:
   $$\operatorname{sieveLagMultiplier}(p^{a+1}, p^a) = -\frac{1}{(p : \mathbb{R}) - 1}, \qquad
     \operatorname{ramanujanLagCoefficient}(p^{a+1}, p^a) = -(p : \mathbb{R})^a =
       -\bigl(\operatorname{lagVisibilityClock}(p^{a+1}) : \mathbb{R}\bigr).$$

3. **Prime-Chain Step Clock Scaling & Valuation-Clock Bridge to `CHMDPrimeChain.chainVariance`
   (`div_lagVisibilityClock_of_same_chain`, `mangoldt_edge_eq_clock_quotient`,
   `divisor_cut_eq_clock_chainVariance`)**:
   Along any active prime-power chain edge `m < k` (`m ∣ k` and `ordCompl[p] m = ordCompl[p] k` for
   `p ∈ N.primeFactors`), the edge quotient `d = k / m` satisfies
   `d / lagVisibilityClock d = p`, so its von Mangoldt weight is `log (d / lagVisibilityClock d)`
   and its first visible translation lag is `lagVisibilityClock (k / m) = (k / m) / p`.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve RHTower.CHMDPrimeChain
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Radical Quotient Identity & Exact Valuation-Clock Reconstruction of `vonMangoldt` -/

/-- The squarefree radical `∏ p ∈ d.primeFactors, p` of a natural number `d`. -/
def primeRadical (d : ℕ) : ℕ := ∏ p ∈ d.primeFactors, p

theorem primeRadical_pos (d : ℕ) : 0 < primeRadical d :=
  Finset.prod_pos fun _ hp => (Nat.mem_primeFactors.mp hp).1.pos

theorem primeRadical_dvd (d : ℕ) : primeRadical d ∣ d :=
  Nat.prod_primeFactors_dvd d

/-- **Product Identity of `lagVisibilityClock` and `primeRadical` (`lagVisibilityClock_mul_rad`):**
For every `d : ℕ`, `lagVisibilityClock d * primeRadical d = d`. -/
theorem lagVisibilityClock_mul_rad (d : ℕ) :
    lagVisibilityClock d * primeRadical d = d :=
  Nat.div_mul_cancel (primeRadical_dvd d)

/-- `lagVisibilityClock d` divides `d` for every `d : ℕ`. -/
theorem lagVisibilityClock_dvd_self (d : ℕ) : lagVisibilityClock d ∣ d :=
  ⟨primeRadical d, (lagVisibilityClock_mul_rad d).symm⟩

/-- **Exact Quotient by `lagVisibilityClock` (`div_lagVisibilityClock_eq_rad`):**
For every `d ≠ 0`, dividing `d` by its additive translation visibility clock `lagVisibilityClock d`
recovers the squarefree radical `primeRadical d = ∏ p ∈ d.primeFactors, p`. -/
theorem div_lagVisibilityClock_eq_rad {d : ℕ} (hd : d ≠ 0) :
    d / lagVisibilityClock d = primeRadical d := by
  have hclock_pos : 0 < lagVisibilityClock d :=
    Nat.pos_of_ne_zero (fun hz => hd ((lagVisibilityClock_eq_zero_iff d).mp hz))
  calc
    d / lagVisibilityClock d = (primeRadical d * lagVisibilityClock d) / lagVisibilityClock d := by
      rw [mul_comm, lagVisibilityClock_mul_rad]
    _ = primeRadical d := Nat.mul_div_cancel _ hclock_pos

/-- For every prime `p` and `a : ℕ`, `(p ^ (a + 1)) / lagVisibilityClock (p ^ (a + 1)) = p`. -/
theorem div_lagVisibilityClock_prime_power (p a : ℕ) (hp : p.Prime) :
    p ^ (a + 1) / lagVisibilityClock (p ^ (a + 1)) = p := by
  have hne : p ^ (a + 1) ≠ 0 := pow_ne_zero (a + 1) hp.ne_zero
  rw [div_lagVisibilityClock_eq_rad hne, primeRadical,
    Nat.primeFactors_pow p (by omega : a + 1 ≠ 0), hp.primeFactors, Finset.prod_singleton]

/-- **Prime-Power Characterization via the Valuation-Clock Quotient
(`prime_div_lagVisibilityClock_iff_isPrimePow`):**
For every `d : ℕ`, the quotient `d / lagVisibilityClock d` is prime if and only if `IsPrimePow d`. -/
theorem prime_div_lagVisibilityClock_iff_isPrimePow (d : ℕ) :
    Nat.Prime (d / lagVisibilityClock d) ↔ IsPrimePow d := by
  constructor
  · intro hprime
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp [lagVisibilityClock] at hprime
      exact Nat.not_prime_zero hprime
    rw [div_lagVisibilityClock_eq_rad hd0] at hprime
    have hcard : d.primeFactors.card = 1 := by
      by_contra hne1
      rcases Nat.lt_or_gt_of_ne hne1 with hlt | hgt
      · have hempty : d.primeFactors = ∅ := Finset.card_eq_zero.mp (by omega)
        rw [primeRadical, hempty, Finset.prod_empty] at hprime
        exact Nat.not_prime_one hprime
      · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hgt
        have hp_prime := (Nat.mem_primeFactors.mp hp).1
        have hq_prime := (Nat.mem_primeFactors.mp hq).1
        have hdvd_p : p ∣ primeRadical d := Finset.dvd_prod_of_mem _ hp
        have hdvd_q : q ∣ primeRadical d := Finset.dvd_prod_of_mem _ hq
        have hp_eq := ((Nat.dvd_prime hprime).mp hdvd_p).resolve_left hp_prime.ne_one
        have hq_eq := ((Nat.dvd_prime hprime).mp hdvd_q).resolve_left hq_prime.ne_one
        exact hpq (hp_eq.trans hq_eq.symm)
    exact isPrimePow_iff_card_primeFactors_eq_one.mpr hcard
  · intro hpp
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [div_lagVisibilityClock_prime_power p a hp']
    exact hp'

/-- **Exact Valuation-Clock Reconstruction of `vonMangoldt`
(`vonMangoldt_eq_log_div_lagVisibilityClock`):**
For every `d : ℕ`, the von Mangoldt function `Λ(d)` is given unconditionally by testing primality of
the valuation-clock quotient `d / lagVisibilityClock d`:
`Λ(d) = if Nat.Prime (d / lagVisibilityClock d) then Real.log (d / lagVisibilityClock d) else 0`. -/
theorem vonMangoldt_eq_log_div_lagVisibilityClock (d : ℕ) :
    ArithmeticFunction.vonMangoldt d =
      if Nat.Prime (d / lagVisibilityClock d) then
        Real.log ((d / lagVisibilityClock d : ℕ) : ℝ)
      else 0 := by
  by_cases hpp : IsPrimePow d
  · have hprime : Nat.Prime (d / lagVisibilityClock d) :=
      (prime_div_lagVisibilityClock_iff_isPrimePow d).mpr hpp
    rw [if_pos hprime]
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [div_lagVisibilityClock_prime_power p a hp',
      ArithmeticFunction.vonMangoldt_apply_pow (by omega : a + 1 ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime hp']
  · have hnot : ¬Nat.Prime (d / lagVisibilityClock d) :=
      fun hp => hpp ((prime_div_lagVisibilityClock_iff_isPrimePow d).mp hp)
    rw [if_neg hnot, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]

/-- **Structural Dichotomy Between Pronic Successor Nodes and Valuation-Clock Prime Powers
(`not_prime_div_lagVisibilityClock_pronicSeq`):**
For every `k ≥ 2`, the pronic successor product `pronicSeq k = k * (k + 1)` has composite
valuation-clock quotient `pronicSeq k / lagVisibilityClock (pronicSeq k)` and vanishing
von Mangoldt weight. -/
theorem not_prime_div_lagVisibilityClock_pronicSeq {k : ℕ} (hk : 2 ≤ k) :
    ¬Nat.Prime (pronicSeq k / lagVisibilityClock (pronicSeq k)) ∧
      ArithmeticFunction.vonMangoldt (pronicSeq k) = 0 := by
  have hvm := vonMangoldt_pronicSeq_eq_zero hk
  have hnpp : ¬IsPrimePow (pronicSeq k) :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mp hvm
  exact ⟨fun hp => hnpp ((prime_div_lagVisibilityClock_iff_isPrimePow _).mp hp), hvm⟩

/-! ## §2. Exact Ramanujan Lag Multiplier & Coefficient at the Prime-Power Visibility Clock -/

/-- **Sub-Clock Invisibility of Prime Powers (`sieveLagMultiplier_prime_power_eq_zero_of_lt_clock`):**
For every prime `p`, exponent `a : ℕ`, and positive lag `1 ≤ h < p ^ a`, the prime-power mode
`p ^ (a + 1)` is completely invisible in the compressed translation spectrum:
`sieveLagMultiplier (p ^ (a + 1)) h = 0` and `ramanujanLagCoefficient (p ^ (a + 1)) h = 0`. -/
theorem sieveLagMultiplier_prime_power_eq_zero_of_lt_clock {p a h : ℕ} (hp : p.Prime)
    (hh1 : 1 ≤ h) (hhlt : h < p ^ a) :
    sieveLagMultiplier (p ^ (a + 1)) h = 0 ∧
      ramanujanLagCoefficient (p ^ (a + 1)) h = 0 := by
  have hnot_dvd : ¬(lagVisibilityClock (p ^ (a + 1)) ∣ h) := by
    rw [lagVisibilityClock_prime_power p a hp]
    intro hdvd
    have hle := Nat.le_of_dvd hh1 hdvd
    omega
  have hm0 : sieveLagMultiplier (p ^ (a + 1)) h = 0 := by
    by_contra hne
    exact hnot_dvd ((sieveLagMultiplier_ne_zero_iff (p ^ (a + 1)) h).mp hne).2
  have hr0 : ramanujanLagCoefficient (p ^ (a + 1)) h = 0 := by
    by_contra hne
    exact hnot_dvd ((ramanujanLagCoefficient_ne_zero_iff (p ^ (a + 1)) h).mp hne).2
  exact ⟨hm0, hr0⟩

/-- **Exact Ramanujan Lag Multiplier of a Prime Power at Its Visibility Clock
(`sieveLagMultiplier_prime_power_at_clock`):**
For every prime `p` and `a : ℕ`:
`sieveLagMultiplier (p ^ (a + 1)) (lagVisibilityClock (p ^ (a + 1))) = -1 / ((p : ℝ) - 1)`. -/
theorem sieveLagMultiplier_prime_power_at_clock (p a : ℕ) (hp : p.Prime) :
    sieveLagMultiplier (p ^ (a + 1)) (lagVisibilityClock (p ^ (a + 1))) =
      -1 / ((p : ℝ) - 1) := by
  rw [lagVisibilityClock_prime_power p a hp, sieveLagMultiplier_eq_moebius_totient_quotient]
  have hdvd : p ^ a ∣ p ^ (a + 1) := ⟨p, pow_succ p a⟩
  have hgcd : Nat.gcd (p ^ (a + 1)) (p ^ a) = p ^ a := Nat.gcd_eq_right hdvd
  have hquot : p ^ (a + 1) / (p ^ a) = p := by
    rw [pow_succ']
    exact Nat.mul_div_cancel _ (pow_pos hp.pos a)
  rw [hgcd, hquot, moebiusReal, ArithmeticFunction.moebius_apply_prime hp,
    Nat.totient_prime hp]
  have hp1 : 1 ≤ p := hp.one_le
  simp [Nat.cast_sub hp1]

/-- **Exact Ramanujan Lag Coefficient of a Prime Power at Its Visibility Clock
(`ramanujanLagCoefficient_prime_power_at_clock`):**
For every prime `p` and `a : ℕ`, at its visibility clock `h = lagVisibilityClock (p ^ (a + 1)) = p ^ a`,
the unnormalized Ramanujan lag coefficient equals `-p ^ a = -(lagVisibilityClock (p ^ (a + 1)) : ℝ)`. -/
theorem ramanujanLagCoefficient_prime_power_at_clock (p a : ℕ) (hp : p.Prime) :
    ramanujanLagCoefficient (p ^ (a + 1)) (lagVisibilityClock (p ^ (a + 1))) =
      -((lagVisibilityClock (p ^ (a + 1)) : ℕ) : ℝ) := by
  rw [ramanujanLagCoefficient_eq_totient_mul, sieveLagMultiplier_prime_power_at_clock p a hp,
    lagVisibilityClock_prime_power p a hp, Nat.totient_prime_pow hp (by omega : 0 < a + 1)]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp1 : 1 ≤ p := hp.one_le
  simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp1, Nat.cast_one]
  field_simp [hp1_ne]

/-! ## §3. Prime-Chain Step Clock Scaling & Bridge to `CHMDPrimeChain.chainVariance` -/

/-- Along any active prime-power chain edge `m < k` (`ordCompl[p] m = ordCompl[p] k`), the quotient
`k / m` is a positive power of `p` and therefore satisfies
`(k / m) / lagVisibilityClock (k / m) = p`. -/
theorem div_lagVisibilityClock_of_same_chain {p m k : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hmk : m < k) (hchain : ordCompl[p] m = ordCompl[p] k) :
    (k / m) / lagVisibilityClock (k / m) = p ∧
      ArithmeticFunction.vonMangoldt (k / m) =
        Real.log (((k / m) / lagVisibilityClock (k / m) : ℕ) : ℝ) := by
  obtain ⟨r, hr, hkr⟩ := exists_pow_mul_of_same_chain hp hm hmk hchain
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hquot : k / m = p ^ (a + 1) := by
    rw [hkr, Nat.mul_div_cancel_left _ hm]
  rw [hquot, div_lagVisibilityClock_prime_power p a hp,
    ArithmeticFunction.vonMangoldt_apply_pow (by omega : a + 1 ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  exact ⟨rfl, rfl⟩

/-- **Valuation-Clock Edge Representation of `CHMDPrimeChain.chainVariance`
(`divisor_cut_eq_clock_chainVariance`):**
For every product index `N : ℕ`, logarithmic cut `u : ℝ`, and profile `a : ℕ → ℝ`, the complete
bipartite prime-chain variance `chainVariance N u a` equals the divisor-cut sum weighted by the
valuation-clock radical test `Nat.Prime ((k / m) / lagVisibilityClock (k / m))`. -/
theorem divisor_cut_eq_clock_chainVariance (N : ℕ) (u : ℝ) (a : ℕ → ℝ) :
    (∑ k ∈ N.divisors, ∑ m ∈ k.divisors,
      if u ∈ Set.Ioo (Real.log m) (Real.log k) then
        (if Nat.Prime ((k / m) / lagVisibilityClock (k / m)) then
          Real.log (((k / m) / lagVisibilityClock (k / m) : ℕ) : ℝ) else 0) *
          (a m - a k) ^ 2
      else 0) =
      chainVariance N u a := by
  simp_rw [← vonMangoldt_eq_log_div_lagVisibilityClock]
  exact divisor_cut_eq_chainVariance N u a

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
