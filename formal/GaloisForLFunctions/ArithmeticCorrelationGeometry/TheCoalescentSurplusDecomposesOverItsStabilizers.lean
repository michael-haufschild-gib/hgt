import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheCoalescentSurplusIsPureGaugeCharge
import GaloisForLFunctions.ArithmeticCorrelationGeometry.FiniteGaugeSubgroupsResolveWhatTheArchimedeanLineCannot

/-!
# The coalescent surplus decomposes over its stabilizers

`TheCoalescentSurplusIsPureGaugeCharge` shows that the bandwidth-`4/3` coalescent statistic of the
primes vanishes on average over the whole gauge torus; the actual statistic is the value at the
gauge point `0`. This file computes its averages over the **finite** subgroups — the Dirichlet
characters of level `q` — which see the actual primes through their residues.

* **Coalescent primes are large** (`lt_of_coalWeight_ne_zero`). A pair `n ≠ m` of primes with
  `|log(n/m)| ≤ θ₀ ≤ ½` has `|n − m| ≥ 1`, hence `max(n, m) ≥ 1/θ₀`, and `n, m > max/2`; so both
  exceed every `q` with `2qθ₀ < 1`, and are prime to `q`.
* **The stabilizer average** (`sum_twistedPrimeCoalSum_dirichletGauge`). For every level
  `q < 1/(2θ₀)` the average of the twisted statistic over the Dirichlet characters mod `q` is the
  coalescent sum over the prime pairs **congruent mod `q`**. At bandwidth `4/3` with
  `θ₀ = T^{−1+η}` every level `q < T^{1−η}/2` qualifies.
* **The decomposition** (`primeCoalSum_eq_stabilizer_add_discrepancy`). The actual statistic is its
  level-`q` stabilizer average plus the sum over the pairs that are **not** congruent mod `q`; the
  second part has mean zero over the level-`q` subgroup
  (`sum_discrepancy_dirichletGauge_eq_zero`).

So Question 1 splits exactly: the congruent part is where the singular series lives (a pair at
shift `h` is congruent mod `q` iff `q ∣ h`), and the remainder is invisible to the finite
subgroup of level `q`. A bound on the actual surplus is a bound on how the prime pairs distribute
among residue classes at every admissible level, weighted by the signed coalescent kernel.
-/

open Finset
open scoped ComplexConjugate

open Zeta23 Zeta23.PrimeSide

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open TransThresholdPairCorrelation

/-- The defining condition of a nonzero coalescent weight. -/
theorem coalescent_of_coalWeight_ne_zero {Ω g : ℝ → ℝ} {θ₀ : ℝ} {n m : ℕ}
    (h : coalWeight Ω g θ₀ n m ≠ 0) :
    n.Prime ∧ m.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀ := by
  rw [coalWeight] at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

/-- **Coalescent primes are large.** Both members of a coalescent prime pair exceed every `q`
with `2qθ₀ < 1`. -/
theorem lt_of_coalWeight_ne_zero {Ω g : ℝ → ℝ} {θ₀ : ℝ} (hθ0 : 0 < θ₀) (hθ : θ₀ ≤ 1 / 2)
    {q : ℕ} (hq : 2 * (q : ℝ) * θ₀ < 1) {n m : ℕ} (h : coalWeight Ω g θ₀ n m ≠ 0) :
    q < n ∧ q < m := by
  obtain ⟨hnp, hmp, hnm, hgap⟩ := coalescent_of_coalWeight_ne_zero h
  have hn1 : 1 ≤ n := hnp.one_lt.le
  have hm1 : 1 ≤ m := hmp.one_lt.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  obtain ⟨hn2, hm2, -⟩ := coalescent_partner_Window_bounds hm1 hn1 hgap hθ
  have hsep := abs_log_sub_log_ge_abs_sub_div_max hm1 hn1
  have hone : (1 : ℝ) ≤ |(n : ℝ) - m| := by
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hlt
      rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hgt
      rw [abs_of_pos (by linarith)]; linarith
  set M := max (n : ℝ) (m : ℝ) with hM
  have hMpos : 0 < M := lt_max_of_lt_left hn0
  have hθM : 1 ≤ θ₀ * M := by
    have h1 : 1 / M ≤ |(n : ℝ) - m| / M := div_le_div_of_nonneg_right hone hMpos.le
    have h2 : 1 / M ≤ θ₀ := (h1.trans hsep).trans hgap
    rwa [div_le_iff₀ hMpos] at h2
  have hqM : 2 * (q : ℝ) < M := by
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_left hcon hθ0.le
    linarith
  have hnM : M < 2 * (n : ℝ) := by
    rcases le_total (n : ℝ) m with hle | hle
    · rw [hM, max_eq_right hle]; exact hm2
    · rw [hM, max_eq_left hle]; linarith
  have hmM : M < 2 * (m : ℝ) := by
    rcases le_total (n : ℝ) m with hle | hle
    · rw [hM, max_eq_right hle]; linarith
    · rw [hM, max_eq_left hle]; exact hn2
  constructor
  · have : (q : ℝ) < n := by linarith
    exact_mod_cast this
  · have : (q : ℝ) < m := by linarith
    exact_mod_cast this

/-- A prime larger than `q` is prime to `q`. -/
theorem coprime_of_prime_of_lt {p q : ℕ} (hp : p.Prime) (hq : 0 < q) (hlt : q < p) :
    Nat.Coprime p q :=
  (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => absurd (Nat.le_of_dvd hq hd) (not_le.mpr hlt)

variable {q : ℕ} [NeZero q]

/-- **The stabilizer average of the coalescent statistic.** For every level `q` with `2qθ₀ < 1`,
the sum over the Dirichlet characters mod `q` of the twisted statistic is `φ(q)` times the
coalescent sum over the prime pairs congruent mod `q`. -/
theorem sum_twistedPrimeCoalSum_dirichletGauge {Ω g : ℝ → ℝ} {X θ₀ : ℝ} (hθ0 : 0 < θ₀)
    (hθ : θ₀ ≤ 1 / 2) (hq : 2 * (q : ℝ) * θ₀ < 1) :
    ∑ χ : DirichletCharacter ℂ q, twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ) =
      (q.totient : ℂ) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        if (n : ZMod q) = m then (coalWeight Ω g θ₀ n m : ℂ) else 0 := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  simp only [twistedPrimeCoalSum]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.mul_sum]
  by_cases hw : coalWeight Ω g θ₀ n m = 0
  · simp [hw]
  · obtain ⟨hnp, hmp, -, -⟩ := coalescent_of_coalWeight_ne_zero hw
    obtain ⟨hqn, hqm⟩ := lt_of_coalWeight_ne_zero hθ0 hθ hq hw
    rw [sum_twist_dirichletGauge_mul_conj (pos_of_mem_primeRange hn) (pos_of_mem_primeRange hm)
      (coprime_of_prime_of_lt hnp hq0 hqn) (coprime_of_prime_of_lt hmp hq0 hqm)]
    split_ifs <;> ring

omit [NeZero q] in
/-- **The stabilizer decomposition.** The actual statistic is its congruent part plus the sum over
non-congruent pairs. -/
theorem primeCoalSum_eq_stabilizer_add_discrepancy (Ω g : ℝ → ℝ) (X θ₀ : ℝ) :
    (primeCoalSum Ω g X θ₀ : ℂ) =
      (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        if (n : ZMod q) = m then (coalWeight Ω g θ₀ n m : ℂ) else 0) +
      ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        if (n : ZMod q) = m then 0 else (coalWeight Ω g θ₀ n m : ℂ) := by
  rw [primeCoalSum_eq_sum_coalWeight, ← Finset.sum_add_distrib]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

/-- **The discrepancy is invisible to the level-`q` subgroup**: its twisted average over the
Dirichlet characters mod `q` vanishes. -/
theorem sum_discrepancy_dirichletGauge_eq_zero {Ω g : ℝ → ℝ} {X θ₀ : ℝ} (hθ0 : 0 < θ₀)
    (hθ : θ₀ ≤ 1 / 2) (hq : 2 * (q : ℝ) * θ₀ < 1) :
    ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      (if (n : ZMod q) = m then 0 else (coalWeight Ω g θ₀ n m : ℂ)) *
        (twist (dirichletGauge χ) n * conj (twist (dirichletGauge χ) m)) = 0 := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [← Finset.mul_sum]
  by_cases hc : (n : ZMod q) = m
  · simp [hc]
  · by_cases hw : coalWeight Ω g θ₀ n m = 0
    · simp [hw]
    · obtain ⟨hnp, hmp, -, -⟩ := coalescent_of_coalWeight_ne_zero hw
      obtain ⟨hqn, hqm⟩ := lt_of_coalWeight_ne_zero hθ0 hθ hq hw
      rw [sum_twist_dirichletGauge_mul_conj (pos_of_mem_primeRange hn) (pos_of_mem_primeRange hm)
        (coprime_of_prime_of_lt hnp hq0 hqn) (coprime_of_prime_of_lt hmp hq0 hqm), if_neg hc,
        if_neg hc, mul_zero]

end GaloisForLFunctions.ArithmeticCorrelationGeometry
