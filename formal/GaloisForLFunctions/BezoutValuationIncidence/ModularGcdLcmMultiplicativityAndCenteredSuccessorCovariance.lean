import GaloisForLFunctions.BezoutValuationIncidence.RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation

/-!
# Pillar XVI: Modular GCD–LCM Multiplicativity, Scaled Bézout Shifts, & Centered Successor Covariance

In this sixteenth pillar of **Bézout–Valuation Incidence Mechanics**, we unify the coprime
multiplicativity of Pillar X (`pmPowerDampedDivisorCoeff_mul_of_coprime`) and the radical
divisor-absorption law of Pillar XV (`pmPowerDampedDivisorCoeff_mul_of_dvd_right`) into a single
**Universal Modular GCD–LCM Multiplicativity Law** on the divisibility lattice $(\mathbb{N}, \gcd, \operatorname{lcm})$,
and apply it to decompose the centered covariance matrix and predictable martingale increments of
Route PM.

## Core Main Theorems (100% Unconditional)

1. **Universal Modular GCD–LCM Multiplicativity Law
   (`primeFactors_inter_eq_gcd`,
   `pmPowerDampedDivisorCoeff_mul_eq_mul_gcd`,
   `pmPowerDampedDivisorCoeff_lcm_eq_mul`,
   `pmPowerDampedDivisorCoeff_mul_eq_lcm_mul_gcd`)**:
   For **every** `ε : ℝ` and **every** pair of natural numbers `j, k : ℕ` (without any coprimality
   hypothesis):
   $$\tau_\varepsilon(j)\,\tau_\varepsilon(k) =
     \tau_\varepsilon(j \cdot k)\,\tau_\varepsilon(\gcd(j, k)) =
     \tau_\varepsilon(\operatorname{lcm}(j, k))\,\tau_\varepsilon(\gcd(j, k)),$$
   where $\tau_\varepsilon = \operatorname{pmPowerDampedDivisorCoeff}\,\varepsilon$.

2. **Scaled Bézout Successor Multiplicativity & Two-Step Parity Autocorrelation
   (`pmPowerDampedDivisorCoeff_scaled_bezout_succ`,
   `pmPowerDampedDivisorCoeff_odd_mul_add_two`,
   `pmPowerDampedDivisorCoeff_even_mul_add_two`)**:
   - For every scale `d : ℕ` and index `k : ℕ`, since $\gcd(d k, d(k + 1)) = d$:
     $$\tau_\varepsilon(d k)\,\tau_\varepsilon(d(k + 1)) =
       \tau_\varepsilon(d \cdot \operatorname{pronicSeq}\,k)\,\tau_\varepsilon(d).$$
   - For two-step shifts $n \mapsto n + 2$:
     - On odd indices $2m + 1$, $\gcd(2m + 1, 2m + 3) = 1$, so
       $\tau_\varepsilon(2m + 1)\,\tau_\varepsilon(2m + 3) = \tau_\varepsilon((2m + 1)(2m + 3))$.
     - On even indices $2m$, $\gcd(2m, 2m + 2) = 2$, so
       $\tau_\varepsilon(2m)\,\tau_\varepsilon(2m + 2) = (1 - 2^{-\varepsilon})\,\tau_\varepsilon(2 \cdot \operatorname{pronicSeq}\,m)$.

3. **Centered Covariance Linearization & Predictable Martingale Predecessor Split
   (`pmPowerDampedCenteredDivisorCoeff_mul_eq_lcm_gcd`,
   `pmPowerDampedCenteredDivisorCoeff_mul_of_coprime`,
   `pmPowerDampedCenteredDivisorCoeff_mul_succ_eq_pronicSeq`,
   `pmPredictableMartingaleIncrement_split_predecessor`)**:
   For $\widetilde{\tau}_\varepsilon(k) = \operatorname{pmPowerDampedCenteredDivisorCoeff}\,\varepsilon\,k$
   and $\alpha_\varepsilon = (\operatorname{pmPowerDampedDivisorDensity}\,\varepsilon).\text{re}$:
   - Every coprime pair $\gcd(j, k) = 1$ linearizes the centered quadratic product:
     $$\widetilde{\tau}_\varepsilon(j)\,\widetilde{\tau}_\varepsilon(k) =
       \widetilde{\tau}_\varepsilon(j \cdot k) -
       \alpha_\varepsilon\bigl(\widetilde{\tau}_\varepsilon(j) + \widetilde{\tau}_\varepsilon(k)\bigr) +
       \alpha_\varepsilon(1 - \alpha_\varepsilon).$$
   - In particular, at consecutive Bézout pairs $(n, n + 1)$, isolating the nearest-neighbor
     predecessor term $j = n$ in the predictable martingale increment
     $\widetilde{\tau}_\varepsilon(n + 1)\,A_\varepsilon(n)$ converts $\widetilde{\tau}_\varepsilon(n)\,\widetilde{\tau}_\varepsilon(n + 1)$
     into the single centered pronic coefficient $\widetilde{\tau}_\varepsilon(\operatorname{pronicSeq}\,n)$
     plus linear drift corrections.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Universal Modular GCD–LCM Multiplicativity Law for `pmPowerDampedDivisorCoeff` -/

/-- For every pair of nonzero natural numbers `j, k ≠ 0`, the intersection of their prime factor
sets is the prime factor set of `Nat.gcd j k`. -/
theorem primeFactors_inter_eq_gcd {j k : ℕ} (hj : j ≠ 0) (hk : k ≠ 0) :
    j.primeFactors ∩ k.primeFactors = (Nat.gcd j k).primeFactors := by
  have hgcd : Nat.gcd j k ≠ 0 := Nat.gcd_ne_zero_left hj
  ext p
  simp only [Finset.mem_inter, Nat.mem_primeFactors, hj, hk, hgcd, ne_eq, not_false_eq_true,
    and_true]
  exact ⟨fun ⟨⟨hp, hdj⟩, _, hdk⟩ => ⟨hp, Nat.dvd_gcd hdj hdk⟩,
    fun ⟨hp, hdg⟩ => ⟨⟨hp, hdg.trans (Nat.gcd_dvd_left j k)⟩,
      hp, hdg.trans (Nat.gcd_dvd_right j k)⟩⟩

/-- **Universal Product–GCD Multiplicativity Law (`pmPowerDampedDivisorCoeff_mul_eq_mul_gcd`):**
For every `ε : ℝ` and **all** `j, k : ℕ` (with no coprimality restriction):
`pmPowerDampedDivisorCoeff ε j * pmPowerDampedDivisorCoeff ε k = pmPowerDampedDivisorCoeff ε (j * k) * pmPowerDampedDivisorCoeff ε (Nat.gcd j k)`. -/
theorem pmPowerDampedDivisorCoeff_mul_eq_mul_gcd (ε : ℝ) (j k : ℕ) :
    pmPowerDampedDivisorCoeff ε j * pmPowerDampedDivisorCoeff ε k =
      pmPowerDampedDivisorCoeff ε (j * k) * pmPowerDampedDivisorCoeff ε (Nat.gcd j k) := by
  by_cases hj : j = 0
  · subst hj; simp [pmPowerDampedDivisorCoeff_zero]
  by_cases hk : k = 0
  · subst hk; simp [pmPowerDampedDivisorCoeff_zero]
  have hjk : j * k ≠ 0 := mul_ne_zero hj hk
  have hgcd : Nat.gcd j k ≠ 0 := Nat.gcd_ne_zero_left hj
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hj,
    pmPowerDampedDivisorCoeff_eq_prod ε hk,
    pmPowerDampedDivisorCoeff_eq_prod ε hjk,
    pmPowerDampedDivisorCoeff_eq_prod ε hgcd,
    ← Finset.prod_union_inter,
    Nat.primeFactors_mul hj hk,
    primeFactors_inter_eq_gcd hj hk]

/-- **LCM–Product Radical Equivalence (`pmPowerDampedDivisorCoeff_lcm_eq_mul`):**
For every `ε : ℝ` and **all** `j, k : ℕ`, `Nat.lcm j k` and `j * k` have the same prime factors,
so `pmPowerDampedDivisorCoeff ε (Nat.lcm j k) = pmPowerDampedDivisorCoeff ε (j * k)`. -/
theorem pmPowerDampedDivisorCoeff_lcm_eq_mul (ε : ℝ) (j k : ℕ) :
    pmPowerDampedDivisorCoeff ε (Nat.lcm j k) = pmPowerDampedDivisorCoeff ε (j * k) := by
  by_cases hj : j = 0
  · subst hj; simp
  by_cases hk : k = 0
  · subst hk; simp
  have hgcd : Nat.gcd j k ≠ 0 := Nat.gcd_ne_zero_left hj
  have hdvd : Nat.gcd j k ∣ Nat.lcm j k :=
    (Nat.gcd_dvd_left j k).trans (Nat.dvd_lcm_left j k)
  rw [← Nat.gcd_mul_lcm j k,
    pmPowerDampedDivisorCoeff_mul_of_dvd_right ε hgcd hdvd]

/-- **Universal Modular GCD–LCM Multiplicativity Law
(`pmPowerDampedDivisorCoeff_mul_eq_lcm_mul_gcd`):**
For every `ε : ℝ` and **all** `j, k : ℕ`:
`pmPowerDampedDivisorCoeff ε j * pmPowerDampedDivisorCoeff ε k = pmPowerDampedDivisorCoeff ε (Nat.lcm j k) * pmPowerDampedDivisorCoeff ε (Nat.gcd j k)`. -/
theorem pmPowerDampedDivisorCoeff_mul_eq_lcm_mul_gcd (ε : ℝ) (j k : ℕ) :
    pmPowerDampedDivisorCoeff ε j * pmPowerDampedDivisorCoeff ε k =
      pmPowerDampedDivisorCoeff ε (Nat.lcm j k) * pmPowerDampedDivisorCoeff ε (Nat.gcd j k) := by
  rw [pmPowerDampedDivisorCoeff_lcm_eq_mul, pmPowerDampedDivisorCoeff_mul_eq_mul_gcd]

/-! ## §2. Scaled Bézout Successor Multiplicativity & Two-Step Shift Autocorrelation -/

/-- **Scaled Bézout Successor Multiplicativity Law
(`pmPowerDampedDivisorCoeff_scaled_bezout_succ`):**
For every `ε : ℝ`, scale `d : ℕ`, and index `k : ℕ`:
`pmPowerDampedDivisorCoeff ε (d * k) * pmPowerDampedDivisorCoeff ε (d * (k + 1)) = pmPowerDampedDivisorCoeff ε (d * pronicSeq k) * pmPowerDampedDivisorCoeff ε d`. -/
theorem pmPowerDampedDivisorCoeff_scaled_bezout_succ (ε : ℝ) (d k : ℕ) :
    pmPowerDampedDivisorCoeff ε (d * k) * pmPowerDampedDivisorCoeff ε (d * (k + 1)) =
      pmPowerDampedDivisorCoeff ε (d * pronicSeq k) * pmPowerDampedDivisorCoeff ε d := by
  by_cases hd : d = 0
  · subst hd; simp [pmPowerDampedDivisorCoeff_zero]
  have hcop : Nat.Coprime k (k + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k)
  have hgcd : Nat.gcd (d * k) (d * (k + 1)) = d := by
    rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  rw [pmPowerDampedDivisorCoeff_mul_eq_mul_gcd, hgcd]
  congr 1
  have hmul : (d * k) * (d * (k + 1)) = d * (d * pronicSeq k) := by
    unfold pronicSeq; ring
  rw [hmul, pmPowerDampedDivisorCoeff_mul_of_dvd_right ε hd (dvd_mul_right d (pronicSeq k))]

/-- **Odd Two-Step Shift Multiplicativity (`pmPowerDampedDivisorCoeff_odd_mul_add_two`):**
For every `ε : ℝ` and `m : ℕ`, since `2m + 1` and `2m + 3` are coprime,
`pmPowerDampedDivisorCoeff ε (2 * m + 1) * pmPowerDampedDivisorCoeff ε (2 * m + 3) = pmPowerDampedDivisorCoeff ε ((2 * m + 1) * (2 * m + 3))`. -/
theorem pmPowerDampedDivisorCoeff_odd_mul_add_two (ε : ℝ) (m : ℕ) :
    pmPowerDampedDivisorCoeff ε (2 * m + 1) * pmPowerDampedDivisorCoeff ε (2 * m + 3) =
      pmPowerDampedDivisorCoeff ε ((2 * m + 1) * (2 * m + 3)) := by
  have hndvd : ¬ (2 ∣ (2 * m + 1)) := by omega
  have hcop : Nat.Coprime (2 * m + 1) (2 * m + 3) := by
    rw [show 2 * m + 3 = (2 * m + 1) + 2 by omega, Nat.coprime_self_add_right]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hndvd).symm
  exact (pmPowerDampedDivisorCoeff_mul_of_coprime ε hcop).symm

/-- **Even Two-Step Shift Multiplicativity (`pmPowerDampedDivisorCoeff_even_mul_add_two`):**
For every `ε : ℝ` and `m : ℕ`:
`pmPowerDampedDivisorCoeff ε (2 * m) * pmPowerDampedDivisorCoeff ε (2 * m + 2) = (1 - (2 : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε (2 * pronicSeq m)`. -/
theorem pmPowerDampedDivisorCoeff_even_mul_add_two (ε : ℝ) (m : ℕ) :
    pmPowerDampedDivisorCoeff ε (2 * m) * pmPowerDampedDivisorCoeff ε (2 * m + 2) =
      (1 - (2 : ℝ) ^ (-ε)) * pmPowerDampedDivisorCoeff ε (2 * pronicSeq m) := by
  rw [show 2 * m + 2 = 2 * (m + 1) by omega,
    pmPowerDampedDivisorCoeff_scaled_bezout_succ,
    pmPowerDampedDivisorCoeff_prime ε Nat.prime_two]
  norm_num
  ring

/-! ## §3. Centered Covariance Linearization & Predictable Martingale Predecessor Split -/

/-- **Universal Centered Covariance Entry Identity
(`pmPowerDampedCenteredDivisorCoeff_mul_eq_lcm_gcd`):**
For every `ε : ℝ` and **all** `j, k : ℕ`:
`pmPowerDampedCenteredDivisorCoeff ε j * pmPowerDampedCenteredDivisorCoeff ε k = pmPowerDampedDivisorCoeff ε (Nat.lcm j k) * pmPowerDampedDivisorCoeff ε (Nat.gcd j k) - (pmPowerDampedDivisorDensity ε).re * (pmPowerDampedCenteredDivisorCoeff ε j + pmPowerDampedCenteredDivisorCoeff ε k) - (pmPowerDampedDivisorDensity ε).re ^ 2`. -/
theorem pmPowerDampedCenteredDivisorCoeff_mul_eq_lcm_gcd (ε : ℝ) (j k : ℕ) :
    pmPowerDampedCenteredDivisorCoeff ε j * pmPowerDampedCenteredDivisorCoeff ε k =
      pmPowerDampedDivisorCoeff ε (Nat.lcm j k) * pmPowerDampedDivisorCoeff ε (Nat.gcd j k) -
        (pmPowerDampedDivisorDensity ε).re *
          (pmPowerDampedCenteredDivisorCoeff ε j + pmPowerDampedCenteredDivisorCoeff ε k) -
        (pmPowerDampedDivisorDensity ε).re ^ (2 : ℕ) := by
  have hmul := pmPowerDampedDivisorCoeff_mul_eq_lcm_mul_gcd ε j k
  unfold pmPowerDampedCenteredDivisorCoeff
  linarith

/-- **Coprime Centered Covariance Linearization
(`pmPowerDampedCenteredDivisorCoeff_mul_of_coprime`):**
For every `ε : ℝ` and coprime `j, k : ℕ`, the quadratic product of centered divisor coefficients
linearizes into a single centered evaluation at `j * k` minus linear centered terms:
`pmPowerDampedCenteredDivisorCoeff ε j * pmPowerDampedCenteredDivisorCoeff ε k = pmPowerDampedCenteredDivisorCoeff ε (j * k) - (pmPowerDampedDivisorDensity ε).re * (pmPowerDampedCenteredDivisorCoeff ε j + pmPowerDampedCenteredDivisorCoeff ε k) + (pmPowerDampedDivisorDensity ε).re * (1 - (pmPowerDampedDivisorDensity ε).re)`. -/
theorem pmPowerDampedCenteredDivisorCoeff_mul_of_coprime (ε : ℝ) {j k : ℕ}
    (hcop : Nat.Coprime j k) :
    pmPowerDampedCenteredDivisorCoeff ε j * pmPowerDampedCenteredDivisorCoeff ε k =
      pmPowerDampedCenteredDivisorCoeff ε (j * k) -
        (pmPowerDampedDivisorDensity ε).re *
          (pmPowerDampedCenteredDivisorCoeff ε j + pmPowerDampedCenteredDivisorCoeff ε k) +
        (pmPowerDampedDivisorDensity ε).re * (1 - (pmPowerDampedDivisorDensity ε).re) := by
  have hmul := pmPowerDampedDivisorCoeff_mul_of_coprime ε hcop
  unfold pmPowerDampedCenteredDivisorCoeff
  linarith

/-- **Centered Bézout Successor Covariance Law
(`pmPowerDampedCenteredDivisorCoeff_mul_succ_eq_pronicSeq`):**
For every `ε : ℝ` and `n : ℕ`:
`pmPowerDampedCenteredDivisorCoeff ε n * pmPowerDampedCenteredDivisorCoeff ε (n + 1) = pmPowerDampedCenteredDivisorCoeff ε (pronicSeq n) - (pmPowerDampedDivisorDensity ε).re * (pmPowerDampedCenteredDivisorCoeff ε n + pmPowerDampedCenteredDivisorCoeff ε (n + 1)) + (pmPowerDampedDivisorDensity ε).re * (1 - (pmPowerDampedDivisorDensity ε).re)`. -/
theorem pmPowerDampedCenteredDivisorCoeff_mul_succ_eq_pronicSeq (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorCoeff ε n * pmPowerDampedCenteredDivisorCoeff ε (n + 1) =
      pmPowerDampedCenteredDivisorCoeff ε (pronicSeq n) -
        (pmPowerDampedDivisorDensity ε).re *
          (pmPowerDampedCenteredDivisorCoeff ε n + pmPowerDampedCenteredDivisorCoeff ε (n + 1)) +
        (pmPowerDampedDivisorDensity ε).re * (1 - (pmPowerDampedDivisorDensity ε).re) := by
  unfold pronicSeq
  exact pmPowerDampedCenteredDivisorCoeff_mul_of_coprime ε
    (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n))

/-- **Predecessor-Isolated Split of the Route PM Predictable Martingale Increment
(`pmPredictableMartingaleIncrement_split_predecessor`):**
For every `ε : ℝ` and `n ≥ 1`, isolating the nearest-neighbor predecessor `j = n` in
`pmPowerDampedCenteredDivisorPrefix ε n = pmPowerDampedCenteredDivisorPrefix ε (n - 1) + pmPowerDampedCenteredDivisorCoeff ε n`
rewrites the predictable martingale increment `widetilde{τ}_ε(n + 1) * A_ε(n)` into the lag-2
predictable product `widetilde{τ}_ε(n + 1) * A_ε(n - 1)` plus the single centered pronic evaluation
`widetilde{τ}_ε(pronicSeq n)` and linear drift terms. -/
theorem pmPredictableMartingaleIncrement_split_predecessor (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) * pmPowerDampedCenteredDivisorPrefix ε n =
      pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
        pmPowerDampedCenteredDivisorPrefix ε (n - 1) +
      pmPowerDampedCenteredDivisorCoeff ε (pronicSeq n) -
      (pmPowerDampedDivisorDensity ε).re *
        (pmPowerDampedCenteredDivisorCoeff ε n + pmPowerDampedCenteredDivisorCoeff ε (n + 1)) +
      (pmPowerDampedDivisorDensity ε).re * (1 - (pmPowerDampedDivisorDensity ε).re) := by
  have hstep : pmPowerDampedCenteredDivisorPrefix ε n =
      pmPowerDampedCenteredDivisorPrefix ε (n - 1) + pmPowerDampedCenteredDivisorCoeff ε n := by
    have heq : n - 1 + 1 = n := by omega
    simpa only [heq] using pmPowerDampedCenteredDivisorPrefix_succ ε (n - 1)
  have hsucc := pmPowerDampedCenteredDivisorCoeff_mul_succ_eq_pronicSeq ε n
  rw [hstep, mul_add]
  linarith

end
end GaloisForLFunctions.BezoutValuationIncidence
