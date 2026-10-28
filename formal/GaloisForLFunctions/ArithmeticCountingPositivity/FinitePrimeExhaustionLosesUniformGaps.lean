import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHavePositiveHarmonicDensity
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonLawsHoldForProfilesOfBoundedVariation

/-!
# Finite prime exhaustion loses uniform positive gaps

Finite prime flips have positive harmonic density and positive prime gaps.
Flipping every prime below a cutoff nevertheless agrees exactly with
Liouville on every smaller integer. The Liouville zero-gap theorem therefore
rules out a positive gap with one horizon bound uniform in the prime cutoff.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics

/-- Once all prime factors of an integer are flipped, its sign is Liouville's. -/
theorem finiteFlip_eq_liouville_of_primeFactors_subset {F : Finset ℕ} {n : ℕ}
    (hF : n.primeFactors ⊆ F) : finiteFlip F n = liouvilleSign n := by
  rw [finiteFlip, liouvilleSign, ArithmeticFunction.cardFactors_eq_sum_factorization,
    Finsupp.sum, Nat.support_factorization, ← prod_pow_eq_pow_sum]
  exact (prod_subset hF fun p _ hp => by
    rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero]).symm

/-- A prime cutoff already agrees with Liouville below that cutoff. -/
theorem finiteFlip_primesBelow_eq_liouville {n Q : ℕ} (hnQ : n < Q) :
    finiteFlip (Nat.primesBelow Q) n = liouvilleSign n := by
  apply finiteFlip_eq_liouville_of_primeFactors_subset
  intro p hp
  obtain ⟨hprime, hpn, hn⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primesBelow.mpr
    ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn).trans_lt hnQ, hprime⟩

/-- The finite-prime exhaustion stabilizes at every integer, not merely in mean. -/
theorem finitePrimeExhaustion_eventually_eq_liouville (n : ℕ) :
    ∀ᶠ Q : ℕ in atTop, finiteFlip (Nat.primesBelow Q) n = liouvilleSign n := by
  filter_upwards [eventually_gt_atTop n] with Q hQ
  exact finiteFlip_primesBelow_eq_liouville hQ

/-- Each finite stage is multiplicative, positively gapped, and polar matched. -/
theorem finitePrimeExhaustion_each_stage_matched_positive (Q : ℕ) :
    IsSignGauge (finiteFlip (Nat.primesBelow Q)) ∧
      (∃ g : ℝ, 0 < g ∧ HasHyperplaneGap (finiteFlip (Nat.primesBelow Q)) g) ∧
      (∀ y : ℕ, 1 ≤ y →
        |gaugeMertensSum (finiteFlip (Nat.primesBelow Q)) y - Real.log y| ≤
          Real.log 4 + 4 + 2 * ∑ p ∈ Nat.primesBelow Q, Real.log p / ((p : ℝ) - 1)) := by
  have hF : ∀ p ∈ Nat.primesBelow Q, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  refine ⟨finiteFlip_isSignGauge _,
    ⟨2 * Real.log 2 * finiteFlipHarmonicDensity (Nat.primesBelow Q) ^ 2,
      ?_, finiteFlip_hasHyperplaneGap hF⟩, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) (Real.log_pos one_lt_two))
      (sq_pos_of_pos (finiteFlipHarmonicDensity_pos hF))
  · simpa only [one_mul] using (finiteFlip_matching hF).2

/-- No positive gap holds on a cofinal rectangle of horizons and prime cutoffs. -/
theorem finitePrimeExhaustion_no_uniform_positive_gap {g : ℝ} (hg : 0 < g) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ Q₀ N₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
      ∀ N : ℕ, N₀ ≤ N → ∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
        atomicWeilForm N (fun n => finiteFlip (Nat.primesBelow Q) n * x n) ≤
          (Real.log N - Real.eulerMascheroniConstant - g + ε) *
            ∑ n ∈ Icc 1 N, x n ^ 2) := by
  intro huniform
  apply not_liouville_hasHyperplaneGap hg
  intro ε hε
  obtain ⟨Q₀, N₀, hbound⟩ := huniform ε hε
  refine ⟨N₀, fun N hN x hx => ?_⟩
  let Q := max Q₀ (N + 1)
  have hQ₀ : Q₀ ≤ Q := le_max_left _ _
  have hNQ : N < Q := (Nat.lt_succ_self N).trans_le (le_max_right _ _)
  have h := hbound Q hQ₀ N hN x hx
  have he : atomicWeilForm N (fun n => finiteFlip (Nat.primesBelow Q) n * x n) =
      atomicWeilForm N (fun n => liouvilleSign n * x n) := by
    apply atomicWeilForm_congr
    intro n hn
    rw [finiteFlip_primesBelow_eq_liouville ((mem_Icc.mp hn).2.trans_lt hNQ)]
  rwa [he] at h

end GaloisForLFunctions.ArithmeticCountingPositivity
