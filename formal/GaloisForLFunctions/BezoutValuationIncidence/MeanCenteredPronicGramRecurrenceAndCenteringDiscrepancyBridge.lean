import GaloisForLFunctions.BezoutValuationIncidence.EnergyCenteredPronicGramPositivityAndVonMangoldtLowerBound

/-!
# Mean-Centered Pronic Gram Recurrence, Centering Discrepancy Rank-One Bridge, and Large-Prime Limits

This module advances **Step 2 & Step 5 (Mean-Centered vs. Energy-Centered Pronic Gram Calculus)**
of the Wall 1 programme (`docs/reports/walls/bezout-wall1-programme.md`):

1. **The Sieve Centering Discrepancy & Exact Rank-One Bridge (`sieveCenteringDiscrepancy`,
   `pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne`,
   `sieveMeanCenteredPronicGramForm_eq_energyCentered_add_sq`,
   `sieveEnergyCenteredPronicGramForm_le_meanCentered`):**
   - For every modulus `q : ℕ`, define the centering discrepancy between the periodic Cesàro mean
     `-φ(q)/2` and the pronic reciprocal mean `-Λ(q)`:
     $$\operatorname{sieveCenteringDiscrepancy}(q) = \frac{\varphi(q)}{2} - \Lambda(q).$$
   - For all `p, q > 1`, the mean-centered pronic Gram entry `pmRamanujanMeanCenteredGram p q` and
     the energy-centered pronic Gram entry `pmRamanujanEnergyCenteredGram p q` differ by the exact
     rank-1 product of `sieveCenteringDiscrepancy`:
     $$\mathcal{G}^{\text{mc}}(p, q) = \mathcal{G}^{\text{ec}}(p, q)
       + \left(\frac{\varphi(p)}{2} - \Lambda(p)\right)\left(\frac{\varphi(q)}{2} - \Lambda(q)\right).$$
   - Consequently, for every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`:
     $$\operatorname{sieveMeanCenteredPronicGramForm}(N, c)
       = \operatorname{sieveEnergyCenteredPronicGramForm}(N, c)
         + \left(\sum_{e=2}^N \operatorname{sieveCenteringDiscrepancy}(e)\,Y_{N,c}(e)\right)^2,$$
     which implies the unconditional dominance inequality
     $$\operatorname{sieveEnergyCenteredPronicGramForm}(N, c)
       \le \operatorname{sieveMeanCenteredPronicGramForm}(N, c).$$

2. **Exact Pure-Totient 3-Term Prime-Dilation Recurrence for `pmRamanujanMeanCenteredGram`
   (`sieveCenteringDiscrepancy_prime_mul`, `pmRamanujanMeanCenteredGram_prime_pair`,
   `pmRamanujanMeanCenteredGram_prime_mul_diag`):**
   - Whereas the prime-dilation recurrence for `pmRamanujanEnergyCenteredGram` acquires the
     von Mangoldt rank-1 term `(p - 1) * Λ(q) * Λ(r)`, in `pmRamanujanMeanCenteredGram` all
     von Mangoldt terms cancel identically, leaving the **pure-totient** 3-term recurrence:
     $$\mathcal{G}^{\text{mc}}(pq, pr) + \mathcal{G}^{\text{mc}}(pq, r) + \mathcal{G}^{\text{mc}}(q, pr)
       = (p - 1)\,\mathcal{G}^{\text{mc}}(q, r) + \frac{p(p - 1)}{4}\,\varphi(q)\,\varphi(r).$$

3. **Large-Prime Asymptotic Limits of `pmRamanujanEnergyCenteredGram`
   (`tendsto_pmRamanujanEnergyCenteredGram_prime_mul`,
   `tendsto_pmRamanujanEnergyCenteredGram_prime_mul_add_of_not_isPrimePow`):**
   - For all `q, r > 1`, as `p → ∞` through primes:
     $$\lim_{p \to \infty} \mathcal{G}^{\text{ec}}(p q, r)
       = \frac{\varphi(r)\Lambda(q)}{2} - \mathcal{G}(q, r).$$
   - In particular, whenever `¬ IsPrimePow q`, `Λ(q) = 0` and `G(q, r) = G^ec(q, r)`, so the
     shifted dilated covariance `G^ec(p * q, r) + G^ec(q, r)` converges to `0` as `p → ∞`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Sieve Centering Discrepancy & Exact Rank-One Bridge Between `G^mc` and `G^ec` -/

/-- **Sieve Centering Discrepancy (`sieveCenteringDiscrepancy`):**
For every modulus `q : ℕ`, the difference `φ(q) / 2 - Λ(q)` between the negative periodic mean and
the negative pronic mean of `pmRamanujanPrimitive q`. -/
def sieveCenteringDiscrepancy (q : ℕ) : ℝ :=
  (q.totient : ℝ) / 2 - vonMangoldt q

/-- Pointwise relation between `pmRamanujanMeanCenteredPrimitive` and
`pmRamanujanEnergyCenteredPrimitive`. -/
theorem pmRamanujanMeanCenteredPrimitive_sub_energyCentered (q N : ℕ) :
    pmRamanujanMeanCenteredPrimitive q N - pmRamanujanEnergyCenteredPrimitive q N =
      sieveCenteringDiscrepancy q := by
  unfold pmRamanujanMeanCenteredPrimitive pmRamanujanEnergyCenteredPrimitive
    sieveCenteringDiscrepancy
  ring

/-- **Exact Entrywise Rank-One Bridge (`pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne`):**
For all `p > 1` and `q > 1`:
`pmRamanujanMeanCenteredGram p q = pmRamanujanEnergyCenteredGram p q + sieveCenteringDiscrepancy p * sieveCenteringDiscrepancy q`. -/
theorem pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    pmRamanujanMeanCenteredGram p q =
      pmRamanujanEnergyCenteredGram p q +
        sieveCenteringDiscrepancy p * sieveCenteringDiscrepancy q := by
  have h1 := pmRamanujanPrimitiveGram_eq_meanCentered hp hq
  have h2 := pmRamanujanPrimitiveGram_eq_energyCentered hp hq
  unfold sieveCenteringDiscrepancy
  linarith

/-- Pointwise relation between `sieveMeanCenteredPrefixDiscrepancy` and
`sieveEnergyCenteredPrefixDiscrepancy`. -/
theorem sieveMeanCenteredPrefixDiscrepancy_eq_energyCentered_add
    (N M : ℕ) (c : ℕ → ℝ) :
    sieveMeanCenteredPrefixDiscrepancy N M c =
      sieveEnergyCenteredPrefixDiscrepancy N M c +
        ∑ e ∈ Finset.Icc 2 N, sieveCenteringDiscrepancy e * selbergMultiplesCoord N c e := by
  unfold sieveMeanCenteredPrefixDiscrepancy sieveEnergyCenteredPrefixDiscrepancy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h := pmRamanujanMeanCenteredPrimitive_sub_energyCentered e M
  linear_combination selbergMultiplesCoord N c e * h

/-- **Rank-One Quadratic Form Decomposition (`sieveMeanCenteredPronicGramForm_eq_energyCentered_add_sq`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`:
`sieveMeanCenteredPronicGramForm N c = sieveEnergyCenteredPronicGramForm N c + (∑ e ∈ Icc 2 N, sieveCenteringDiscrepancy e * selbergMultiplesCoord N c e)²`. -/
theorem sieveMeanCenteredPronicGramForm_eq_energyCentered_add_sq
    (N : ℕ) (c : ℕ → ℝ) :
    sieveMeanCenteredPronicGramForm N c =
      sieveEnergyCenteredPronicGramForm N c +
        (∑ e ∈ Finset.Icc 2 N, sieveCenteringDiscrepancy e * selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
  unfold sieveMeanCenteredPronicGramForm sieveEnergyCenteredPronicGramForm
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hp1 : 1 < p := by have := (Finset.mem_Icc.mp hp).1; omega
  have hq1 : 1 < q := by have := (Finset.mem_Icc.mp hq).1; omega
  rw [pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne hp1 hq1]
  ring

/-- **Unconditional Dominance of `sieveMeanCenteredPronicGramForm` over
`sieveEnergyCenteredPronicGramForm` (`sieveEnergyCenteredPronicGramForm_le_meanCentered`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`:
`sieveEnergyCenteredPronicGramForm N c ≤ sieveMeanCenteredPronicGramForm N c`. -/
theorem sieveEnergyCenteredPronicGramForm_le_meanCentered
    (N : ℕ) (c : ℕ → ℝ) :
    sieveEnergyCenteredPronicGramForm N c ≤ sieveMeanCenteredPronicGramForm N c := by
  rw [sieveMeanCenteredPronicGramForm_eq_energyCentered_add_sq]
  linarith [sq_nonneg (∑ e ∈ Finset.Icc 2 N, sieveCenteringDiscrepancy e * selbergMultiplesCoord N c e)]

/-- **Unconditional Lower Bound on `sieveMeanCenteredPronicGramForm` by the Centering Discrepancy Square
(`sieveCenteringDiscrepancy_sum_sq_le_meanCentered`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`:
`(∑ e ∈ Icc 2 N, sieveCenteringDiscrepancy e * selbergMultiplesCoord N c e)² ≤ sieveMeanCenteredPronicGramForm N c`. -/
theorem sieveCenteringDiscrepancy_sum_sq_le_meanCentered
    (N : ℕ) (c : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 2 N, sieveCenteringDiscrepancy e * selbergMultiplesCoord N c e) ^ (2 : ℕ) ≤
      sieveMeanCenteredPronicGramForm N c := by
  rw [sieveMeanCenteredPronicGramForm_eq_energyCentered_add_sq]
  linarith [sieveEnergyCenteredPronicGramForm_nonneg N c]

/-! ## §2. Exact Pure-Totient 3-Term Prime-Dilation Recurrence for `pmRamanujanMeanCenteredGram` -/

/-- Whenever `p` is prime, `q > 1`, and `¬ p ∣ q`, the coprime product `p * q` has
`vonMangoldt (p * q) = 0` and `φ(p * q) = (p - 1) * φ(q)`, so
`sieveCenteringDiscrepancy (p * q) = ((p : ℝ) - 1) * (q.totient : ℝ) / 2`. -/
theorem sieveCenteringDiscrepancy_prime_mul {p q : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hpq : ¬ p ∣ q) :
    sieveCenteringDiscrepancy (p * q) = ((p : ℝ) - 1) * (q.totient : ℝ) / 2 := by
  unfold sieveCenteringDiscrepancy
  rw [vonMangoldt_prime_mul_eq_zero_of_not_dvd hp hq hpq, sub_zero,
    Nat.totient_mul (hp.coprime_iff_not_dvd.mpr hpq), Nat.totient_prime hp,
    Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one]

/-- Symmetry of `pmRamanujanMeanCenteredGram`. -/
theorem pmRamanujanMeanCenteredGram_symm (p q : ℕ) :
    pmRamanujanMeanCenteredGram p q = pmRamanujanMeanCenteredGram q p := by
  unfold pmRamanujanMeanCenteredGram
  congr 1
  ext N
  ring

/-- **Pure-Totient 3-Term Prime-Dilation Recurrence for `pmRamanujanMeanCenteredGram`
(`pmRamanujanMeanCenteredGram_prime_pair`):**
For every prime `p` and moduli `q, r > 1` with `¬ p ∣ q` and `¬ p ∣ r`, all von Mangoldt terms
cancel identically in the mean-centered 3-term prime-dilation recurrence:
`G^mc(p*q, p*r) + G^mc(p*q, r) + G^mc(q, p*r) = (p - 1) * G^mc(q, r) + (p * (p - 1) / 4) * φ(q) * φ(r)`. -/
theorem pmRamanujanMeanCenteredGram_prime_pair {p q r : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hr : 1 < r) (hpq : ¬ p ∣ q) (hpr : ¬ p ∣ r) :
    pmRamanujanMeanCenteredGram (p * q) (p * r) +
      pmRamanujanMeanCenteredGram (p * q) r +
      pmRamanujanMeanCenteredGram q (p * r) =
      ((p : ℝ) - 1) * pmRamanujanMeanCenteredGram q r +
        (p : ℝ) * ((p : ℝ) - 1) / 4 * (q.totient : ℝ) * (r.totient : ℝ) := by
  have hpq1 : 1 < p * q := lt_of_lt_of_le hq (Nat.le_mul_of_pos_left q hp.pos)
  have hpr1 : 1 < p * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)
  rw [pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne hpq1 hpr1,
    pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne hpq1 hr,
    pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne hq hpr1,
    pmRamanujanMeanCenteredGram_eq_energyCentered_add_rankOne hq hr,
    sieveCenteringDiscrepancy_prime_mul hp hq hpq,
    sieveCenteringDiscrepancy_prime_mul hp hr hpr]
  have hec := pmRamanujanEnergyCenteredGram_prime_pair hp hq hr hpq hpr
  unfold sieveCenteringDiscrepancy
  linarith

/-- **Prime-Dilated Diagonal Recurrence for `pmRamanujanMeanCenteredGram`
(`pmRamanujanMeanCenteredGram_prime_mul_diag`):**
For every prime `p` and modulus `q > 1` with `¬ p ∣ q`:
`G^mc(p * q, p * q) = (p - 1) * G^mc(q, q) + (p * (p - 1) / 4) * φ(q)² - 2 * G^mc(p * q, q)`. -/
theorem pmRamanujanMeanCenteredGram_prime_mul_diag {p q : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hpq : ¬ p ∣ q) :
    pmRamanujanMeanCenteredGram (p * q) (p * q) =
      ((p : ℝ) - 1) * pmRamanujanMeanCenteredGram q q +
        (p : ℝ) * ((p : ℝ) - 1) / 4 * (q.totient : ℝ) ^ (2 : ℕ) -
        2 * pmRamanujanMeanCenteredGram (p * q) q := by
  have hpair := pmRamanujanMeanCenteredGram_prime_pair hp hq hq hpq hpq
  have hsymm := pmRamanujanMeanCenteredGram_symm q (p * q)
  linarith [show (p : ℝ) * ((p : ℝ) - 1) / 4 * (q.totient : ℝ) ^ (2 : ℕ) =
    (p : ℝ) * ((p : ℝ) - 1) / 4 * (q.totient : ℝ) * (q.totient : ℝ) by ring]

/-! ## §3. Large-Prime Asymptotic Limits of `pmRamanujanEnergyCenteredGram` -/

/-- **Large-Prime Limit of `pmRamanujanEnergyCenteredGram ((p : ℕ) * q) r`
(`tendsto_pmRamanujanEnergyCenteredGram_prime_mul`):**
For all moduli `q, r > 1`, as `p → ∞` through primes:
`pmRamanujanEnergyCenteredGram (p * q) r → φ(r) * Λ(q) / 2 - pmRamanujanPrimitiveGram q r`. -/
theorem tendsto_pmRamanujanEnergyCenteredGram_prime_mul {q r : ℕ}
    (hq : 1 < q) (hr : 1 < r) :
    Tendsto (fun p : {p : ℕ // p.Prime} =>
      pmRamanujanEnergyCenteredGram ((p : ℕ) * q) r) atTop
        (𝓝 ((r.totient : ℝ) * vonMangoldt q / 2 - pmRamanujanPrimitiveGram q r)) := by
  have hlim := tendsto_pmRamanujanPrimitiveGram_prime_mul hq hr
  have hnd : ∀ᶠ p : {p : ℕ // p.Prime} in atTop, ¬ (p : ℕ) ∣ q := by
    obtain ⟨P, hP, hPrime⟩ := Nat.exists_infinite_primes (q + 1)
    letI : Nonempty {p : ℕ // p.Prime} := ⟨⟨P, hPrime⟩⟩
    apply eventually_atTop.2
    refine ⟨⟨P, hPrime⟩, fun p hpp => ?_⟩
    change P ≤ (p : ℕ) at hpp
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  refine hlim.congr' ?_
  filter_upwards [hnd] with p hpq
  exact (pmRamanujanEnergyCenteredGram_prime_mul_left_eq p.property hq hr hpq).symm

/-- **Asymptotic Annihilation of Shifted Dilated Energy-Centered Covariance on Non-Prime-Powers
(`tendsto_pmRamanujanEnergyCenteredGram_prime_mul_add_of_not_isPrimePow`):**
Whenever `q, r > 1` and `¬ IsPrimePow q`, `vonMangoldt q = 0` and
`pmRamanujanEnergyCenteredGram q r = pmRamanujanPrimitiveGram q r`, so the shifted dilated sum
`pmRamanujanEnergyCenteredGram (p * q) r + pmRamanujanEnergyCenteredGram q r` converges to `0`
as `p → ∞` through primes. -/
theorem tendsto_pmRamanujanEnergyCenteredGram_prime_mul_add_of_not_isPrimePow {q r : ℕ}
    (hq : 1 < q) (hr : 1 < r) (hqp : ¬ IsPrimePow q) :
    Tendsto (fun p : {p : ℕ // p.Prime} =>
      pmRamanujanEnergyCenteredGram ((p : ℕ) * q) r +
        pmRamanujanEnergyCenteredGram q r) atTop (𝓝 0) := by
  have hvq : vonMangoldt q = 0 := vonMangoldt_eq_zero_iff.mpr hqp
  have hec : pmRamanujanEnergyCenteredGram q r = pmRamanujanPrimitiveGram q r := by
    have h := pmRamanujanPrimitiveGram_eq_energyCentered hq hr
    rw [hvq, zero_mul, zero_add] at h
    exact h.symm
  have hlim := (tendsto_pmRamanujanEnergyCenteredGram_prime_mul hq hr).add_const
    (pmRamanujanEnergyCenteredGram q r)
  have hval :
      (r.totient : ℝ) * vonMangoldt q / 2 - pmRamanujanPrimitiveGram q r +
        pmRamanujanEnergyCenteredGram q r = 0 := by
    rw [hvq, hec]
    ring
  rw [hval] at hlim
  exact hlim

end

end GaloisForLFunctions.BezoutValuationIncidence
