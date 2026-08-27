import GaloisForLFunctions.RHTower.Sieve.PrimePairWeightedPaperScale
import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicCoefficientBound
import GaloisForLFunctions.RHTower.Sieve.MinorantDecomposition

/-!
# Literal Matomäki--Teräväinen `c₃,n` coefficient

For each outer prime `q`, `lower q` is the unique `(1+δ_A)`-adic block bottom `Q` containing it.
This file defines the paper's complex-valued replacement error
`α_m (ρ(k,Q) - ρ(k,q))`, proves its exact Buchstab expansion, and transfers its ternary-divisor
weighted mean to the same-block prime-pair estimate.  No hypothesis substitutes for the Buchstab
support argument: every expanded prime is proved to yield a pair product dividing `n`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The literal `c₃,n` replacement error after assigning each outer prime its unique block bottom. -/
def mtC3Coefficient
    (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) (n : ℕ) : ℂ :=
  ∑ q ∈ S, if q ∣ n then
    ∑ m ∈ (n / q).divisors,
      α m * ((rho ((n / q) / m) (lower q) : ℂ) - (rho ((n / q) / m) q : ℂ))
  else 0

/-- Buchstab-expanded form of `mtC3Coefficient`. -/
def mtC3Expanded
    (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) (n : ℕ) : ℂ :=
  ∑ q ∈ S, if q ∣ n then
    ∑ m ∈ (n / q).divisors,
      α m * ∑ p ∈ primeWindow ((n / q) / m) (lower q) q,
        (rho (((n / q) / m) / p) p : ℂ)
  else 0

/-- Exact Buchstab expansion of the source's `ρ(k,Q) - ρ(k,q)` replacement error. -/
theorem mtC3Coefficient_eq_expanded
    (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hS : ∀ q ∈ S, q.Prime) (hlower : ∀ q ∈ S, lower q ≤ q) :
    mtC3Coefficient α S lower n = mtC3Expanded α S lower n := by
  unfold mtC3Coefficient mtC3Expanded
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hqn
  · apply Finset.sum_congr rfl
    intro m hm
    have hN : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn hqn) (hS q hq).pos
    have hmDvd : m ∣ n / q := (Nat.mem_divisors.mp hm).1
    have hk : 0 < (n / q) / m :=
      Nat.div_pos (Nat.le_of_dvd hN hmDvd) (Nat.pos_of_mem_divisors hm)
    have hbuch := buchstab_window (n := (n / q) / m)
      (w := lower q) (z := q) hk (hlower q hq)
    have hbuchC :
        (rho ((n / q) / m) q : ℂ) +
            ∑ p ∈ primeWindow ((n / q) / m) (lower q) q,
              (rho (((n / q) / m) / p) p : ℂ) =
          (rho ((n / q) / m) (lower q) : ℂ) := by
      exact_mod_cast hbuch
    rw [← hbuchC]
    ring
  · rfl

/-- Number of Buchstab prime terms in the literal expansion, before coefficient weights. -/
def mtC3ExpansionCount
    (S : Finset ℕ) (lower : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ q ∈ S, if q ∣ n then
    ∑ m ∈ (n / q).divisors,
      ((primeWindow ((n / q) / m) (lower q) q).card : ℝ)
  else 0

/-- Bounded coefficients reduce the literal complex error to its unsigned expansion count. -/
theorem norm_mtC3Coefficient_le_expansionCount
    (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hS : ∀ q ∈ S, q.Prime) (hlower : ∀ q ∈ S, lower q ≤ q)
    {B : ℝ} (hα : ∀ m, ‖α m‖ ≤ B) :
    ‖mtC3Coefficient α S lower n‖ ≤ B * mtC3ExpansionCount S lower n := by
  rw [mtC3Coefficient_eq_expanded α S lower hn hS hlower]
  unfold mtC3Expanded mtC3ExpansionCount
  calc
    ‖∑ q ∈ S, if q ∣ n then
        ∑ m ∈ (n / q).divisors,
          α m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
            (rho (n / q / m / p) p : ℂ)
      else 0‖ ≤
        ∑ q ∈ S, ‖if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            α m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
              (rho (n / q / m / p) p : ℂ)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ S, if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            B * ((primeWindow (n / q / m) (lower q) q).card : ℝ)
        else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      split_ifs with hqn
      · calc
          ‖∑ m ∈ (n / q).divisors,
              α m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                (rho (n / q / m / p) p : ℂ)‖ ≤
              ∑ m ∈ (n / q).divisors,
                ‖α m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                  (rho (n / q / m / p) p : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ (n / q).divisors,
                B * ((primeWindow (n / q / m) (lower q) q).card : ℝ) := by
            apply Finset.sum_le_sum
            intro m hm
            rw [norm_mul]
            apply mul_le_mul (hα m) _ (norm_nonneg _) (by
              exact (norm_nonneg (α m)).trans (hα m))
            calc
              ‖∑ p ∈ primeWindow (n / q / m) (lower q) q,
                  (rho (n / q / m / p) p : ℂ)‖ ≤
                  ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                    ‖(rho (n / q / m / p) p : ℂ)‖ := norm_sum_le _ _
              _ ≤ ∑ _p ∈ primeWindow (n / q / m) (lower q) q, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro p hp
                exact_mod_cast rho_le_one (n / q / m / p) p
              _ = ((primeWindow (n / q / m) (lower q) q).card : ℝ) := by simp
      · simp
    _ = B * ∑ q ∈ S, if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            ((primeWindow (n / q / m) (lower q) q).card : ℝ)
        else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs
      · rw [Finset.mul_sum]
      · simp

/-- Same-block lower primes whose product with the outer prime divides `n`. -/
def lowerPrimePairDivisorSet (lower : ℕ → ℕ) (q n : ℕ) : Finset ℕ :=
  (primesIco (lower q) q).filter (fun p => q * p ∣ n)

/-- Every Buchstab prime produces a genuine same-block pair divisor of `n`. -/
theorem primeWindow_subset_lowerPrimePairDivisorSet
    (lower : ℕ → ℕ) {n q m : ℕ} (hqn : q ∣ n) (hm : m ∈ (n / q).divisors) :
    primeWindow ((n / q) / m) (lower q) q ⊆ lowerPrimePairDivisorSet lower q n := by
  intro p hp
  rw [lowerPrimePairDivisorSet, Finset.mem_filter, mem_primesIco]
  have hpw := mem_primeWindow.mp hp
  refine ⟨⟨hpw.1.1, hpw.1.2, hpw.2.1⟩, ?_⟩
  have hmDvd : m ∣ n / q := (Nat.mem_divisors.mp hm).1
  have hkDvd : (n / q) / m ∣ n / q := by
    refine ⟨m, ?_⟩
    exact (Nat.div_mul_cancel hmDvd).symm
  have hqk : q * ((n / q) / m) ∣ n := (Nat.dvd_div_iff_mul_dvd hqn).mp hkDvd
  exact (Nat.mul_dvd_mul_left q hpw.2.2).trans hqk

/-- Cardinality form of the lower-fibre pair indicator. -/
theorem card_lowerPrimePairDivisorSet (lower : ℕ → ℕ) (q n : ℕ) :
    ((lowerPrimePairDivisorSet lower q n).card : ℝ) =
      ∑ p ∈ primesIco (lower q) q, if q * p ∣ n then 1 else 0 := by
  rw [lowerPrimePairDivisorSet, Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]

/-- The complete Buchstab expansion has at most `d(n)` copies of each same-block pair. -/
theorem mtC3ExpansionCount_le_pairDivisorCount
    (S : Finset ℕ) (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    mtC3ExpansionCount S lower n ≤
      (n.divisors.card : ℝ) *
        primePairDivisorCount S (fun q => primesIco (lower q) q) n := by
  unfold mtC3ExpansionCount primePairDivisorCount
  calc
    ∑ q ∈ S, (if q ∣ n then
        (∑ m ∈ (n / q).divisors,
          ((primeWindow (n / q / m) (lower q) q).card : ℝ))
      else 0) ≤
        ∑ q ∈ S, (n.divisors.card : ℝ) *
          (∑ p ∈ primesIco (lower q) q, if q * p ∣ n then 1 else 0) := by
      apply Finset.sum_le_sum
      intro q hq
      split_ifs with hqn
      · have hNdiv : n / q ∣ n := by
          refine ⟨q, ?_⟩
          exact (Nat.div_mul_cancel hqn).symm
        have hcardN : ((n / q).divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
          exact_mod_cast card_divisors_mono_of_dvd hNdiv hn.ne'
        calc
          ∑ m ∈ (n / q).divisors,
              ((primeWindow (n / q / m) (lower q) q).card : ℝ) ≤
              ∑ _m ∈ (n / q).divisors,
                ((lowerPrimePairDivisorSet lower q n).card : ℝ) := by
            apply Finset.sum_le_sum
            intro m hm
            exact_mod_cast Finset.card_le_card
              (primeWindow_subset_lowerPrimePairDivisorSet lower hqn hm)
          _ = ((n / q).divisors.card : ℝ) *
              ((lowerPrimePairDivisorSet lower q n).card : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (n.divisors.card : ℝ) *
              ((lowerPrimePairDivisorSet lower q n).card : ℝ) := by
            exact mul_le_mul_of_nonneg_right hcardN (Nat.cast_nonneg _)
          _ = (n.divisors.card : ℝ) *
              ∑ p ∈ primesIco (lower q) q, if q * p ∣ n then 1 else 0 := by
            rw [card_lowerPrimePairDivisorSet]
      · positivity
    _ = (n.divisors.card : ℝ) *
        (∑ q ∈ S, ∑ p ∈ primesIco (lower q) q,
          if q * p ∣ n then 1 else 0) := by
      rw [Finset.mul_sum]

/-- Pointwise source coefficient bound with same-block pair support retained. -/
theorem norm_mtC3Coefficient_le_divisor_mul_pairDivisorCount
    (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hS : ∀ q ∈ S, q.Prime) (hlower : ∀ q ∈ S, lower q ≤ q)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ‖mtC3Coefficient α S lower n‖ ≤
      B * (n.divisors.card : ℝ) *
        primePairDivisorCount S (fun q => primesIco (lower q) q) n := by
  calc
    ‖mtC3Coefficient α S lower n‖ ≤ B * mtC3ExpansionCount S lower n :=
      norm_mtC3Coefficient_le_expansionCount α S lower hn hS hlower hα
    _ ≤ B * ((n.divisors.card : ℝ) *
        primePairDivisorCount S (fun q => primesIco (lower q) q) n) := by
      exact mul_le_mul_of_nonneg_left (mtC3ExpansionCount_le_pairDivisorCount S lower hn) hB
    _ = B * (n.divisors.card : ℝ) *
        primePairDivisorCount S (fun q => primesIco (lower q) q) n := by ring

/-- Three-fold divisor function `d₃`, in its exact nested divisor-sum form. -/
def ternaryDivisorCount (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, (n / d).divisors.card

/-- Elementary pointwise comparison `d₃(n) ≤ d(n)²`. -/
theorem ternaryDivisorCount_le_sq {n : ℕ} (hn : 0 < n) :
    ternaryDivisorCount n ≤ n.divisors.card ^ 2 := by
  unfold ternaryDivisorCount
  calc
    ∑ d ∈ n.divisors, (n / d).divisors.card ≤
        ∑ _d ∈ n.divisors, n.divisors.card := by
      apply Finset.sum_le_sum
      intro d hd
      have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hquot : n / d ∣ n := by
        refine ⟨d, ?_⟩
        exact (Nat.div_mul_cancel hdDvd).symm
      exact card_divisors_mono_of_dvd hquot hn.ne'
    _ = n.divisors.card ^ 2 := by
      simp [Finset.sum_const, pow_two]

/-- The source weight `d₃(n)|c₃,n|` is bounded by the cube-weighted pair count. -/
theorem ternaryDivisorCount_mul_norm_mtC3Coefficient_le
    (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hS : ∀ q ∈ S, q.Prime) (hlower : ∀ q ∈ S, lower q ≤ q)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    (ternaryDivisorCount n : ℝ) * ‖mtC3Coefficient α S lower n‖ ≤
      B * weightedPrimePairDivisorCount 3 S (fun q => primesIco (lower q) q) n := by
  have hc3 := norm_mtC3Coefficient_le_divisor_mul_pairDivisorCount
    α S lower hn hS hlower hB hα
  have hd3 : (ternaryDivisorCount n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast ternaryDivisorCount_le_sq hn
  have hpair : 0 ≤ primePairDivisorCount S (fun q => primesIco (lower q) q) n := by
    unfold primePairDivisorCount
    positivity
  calc
    (ternaryDivisorCount n : ℝ) * ‖mtC3Coefficient α S lower n‖ ≤
        ((n.divisors.card : ℝ) ^ 2) *
          (B * (n.divisors.card : ℝ) *
            primePairDivisorCount S (fun q => primesIco (lower q) q) n) := by
      exact mul_le_mul hd3 hc3 (norm_nonneg _) (by positivity)
    _ = B * weightedPrimePairDivisorCount 3 S (fun q => primesIco (lower q) q) n := by
      unfold weightedPrimePairDivisorCount
      ring

/-- Mean source estimate under the exact reciprocal-mass premise later discharged at paper scale. -/
theorem sum_ternaryDivisorCount_mul_norm_mtC3Coefficient_le
    (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) (Y : ℕ) (hY : 1 ≤ Y)
    (hS : ∀ q ∈ S, q.Prime) (hlower : ∀ q ∈ S, lower q ≤ q)
    {B η : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B)
    (hmass : ∀ q ∈ S, ∑ p ∈ primesIco (lower q) q, 1 / (p : ℝ) ≤ η) :
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) * ‖mtC3Coefficient α S lower n‖ ≤
      B * ((4 : ℝ) ^ 3 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) * η *
          ∑ q ∈ S, 1 / (q : ℝ)) := by
  have hbase := sum_weightedPrimePairDivisorCount_le_of_fibreMass
    3 Y hY S (fun q => primesIco (lower q) q) hS
    (fun q hq p hp => (mem_primesIco.mp hp).2.2) hmass
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) * ‖mtC3Coefficient α S lower n‖ ≤
        ∑ n ∈ Finset.Icc 1 Y,
          B * weightedPrimePairDivisorCount 3 S (fun q => primesIco (lower q) q) n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := by
        rw [Finset.mem_Icc] at hn
        omega
      exact ternaryDivisorCount_mul_norm_mtC3Coefficient_le
        α S lower hnpos hS hlower hB hα
    _ = B * ∑ n ∈ Finset.Icc 1 Y,
        weightedPrimePairDivisorCount 3 S (fun q => primesIco (lower q) q) n := by
      rw [Finset.mul_sum]
    _ ≤ B * ((4 : ℝ) ^ 3 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) * η *
          ∑ q ∈ S, 1 / (q : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hbase hB

end

end RHTower.Sieve
