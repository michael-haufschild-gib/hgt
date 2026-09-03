import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeReverseAbel
import GaloisForLFunctions.RHTower.Sieve.MenonPrimeTwistReverseAbel
import GaloisForLFunctions.RHTower.Sieve.PrimePowerDefectBound

/-!
# Menon's exceptional harmonic prime block to a full von Mangoldt prefix

The two reverse Abel selections are completed by charging the literal proper-prime-power defect.
An exceptional harmonic prime block therefore produces one actual full von Mangoldt prefix, ready
for the finite Heath--Brown identity.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The proper-prime-power mass is monotone in its integer cutoff. -/
theorem primePowerDefect_mono {K N : ℕ} (hKN : K ≤ N) :
    primePowerDefect K ≤ primePowerDefect N := by
  unfold primePowerDefect
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_range] at hn ⊢
    omega
  · intro n _hn _hnK
    by_cases hp : n.Prime
    · rw [if_pos hp, vonMangoldt_apply_prime hp, sub_self]
    · rw [if_neg hp, sub_zero]
      exact vonMangoldt_nonneg

/-- A log-weighted prime prefix above a threshold plus the terminal prime-power defect forces the
same threshold for the full von Mangoldt prefix. -/
theorem norm_partialSum_vonMangoldtTwist_gt_of_prime_gt
    (tau : ℝ) {m b : ℕ} (hmb : m ≤ b) {V : ℝ}
    (hlarge : V + primePowerDefect b <
      ‖∑ n ∈ Finset.range (m + 1), vonMangoldtPrimeTwist tau n‖) :
    V < ‖∑ n ∈ Finset.range (m + 1), vonMangoldtTwist tau n‖ := by
  have hdefect := primePowerDefect_mono hmb
  have hupper := norm_partialSum_vonMangoldtPrimeTwist_le tau m
    (B := ‖∑ n ∈ Finset.range (m + 1), vonMangoldtTwist tau n‖) le_rfl
  linarith

/-- An exceptional ordinary prime interval produces one full von Mangoldt prefix after paying the
exact terminal proper-prime-power defect and the exact reciprocal-log Abel factor. -/
theorem exists_norm_vonMangoldtTwist_prefix_gt_of_primeBlockPoly_gt
    {B : Finset ℕ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b))
    (w : ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hlarge : 2 * ((V + primePowerDefect b) *
        (1 / Real.log 2 + 1 / Real.log ((a + 1 : ℕ) : ℝ))) <
      ‖primeBlockPoly B w‖) :
    ∃ m : ℕ, m ≤ b ∧
      V < ‖∑ n ∈ Finset.range (m + 1),
        vonMangoldtTwist (-(2 * Real.pi * w)) n‖ := by
  have hM : 0 ≤ V + primePowerDefect b :=
    add_nonneg hV (primePowerDefect_nonneg b)
  obtain ⟨K, hKb, m, hmK, hmLarge⟩ :=
    exists_norm_vonMangoldtPrimeTwist_prefix_gt_of_primeBlockPoly_gt
      ha hab hB w hM hlarge
  refine ⟨m, hmK.trans hKb, ?_⟩
  exact norm_partialSum_vonMangoldtTwist_gt_of_prime_gt
    (-(2 * Real.pi * w)) (hmK.trans hKb) hmLarge

/-- **Exact exceptional-block handoff.**  A harmonic prime interval above the displayed reciprocal
Abel threshold yields a full von Mangoldt prefix at the same frequency.  Every endpoint, Abel loss,
and proper-prime-power correction is retained literally. -/
theorem exists_norm_vonMangoldtTwist_prefix_gt_of_harmonicPrimeBlockPoly_gt
    {B : Finset ℕ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b))
    (w : ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hlarge :
      (2 * ((V + primePowerDefect b) *
          (1 / Real.log 2 + 1 / Real.log ((a + 1 : ℕ) : ℝ)))) /
          ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly B w‖) :
    ∃ m : ℕ, m ≤ b ∧
      V < ‖∑ n ∈ Finset.range (m + 1),
        vonMangoldtTwist (-(2 * Real.pi * w)) n‖ := by
  obtain ⟨u, hau, hub, huLarge⟩ :=
    exists_norm_primeBlockPoly_prefix_gt_of_harmonicPrimeBlockPoly_gt
      hab hB w hlarge
  have haUpper : a ≤ u - 1 := by omega
  have huUpper : u - 1 ≤ b := by omega
  have hprimeRange : ∀ p, p ∈ primesRange a (u - 1) ↔
      (p.Prime ∧ a < p ∧ p ≤ u - 1) := fun p => mem_primesRange
  have hdefect : primePowerDefect (u - 1) ≤ primePowerDefect b :=
    primePowerDefect_mono huUpper
  have haCast : (1 : ℝ) < ((a + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 < a + 1)
  have hfactor0 : 0 ≤
      1 / Real.log 2 + 1 / Real.log ((a + 1 : ℕ) : ℝ) := by
    positivity
  have hthreshold :
      2 * ((V + primePowerDefect (u - 1)) *
          (1 / Real.log 2 + 1 / Real.log ((a + 1 : ℕ) : ℝ))) ≤
        2 * ((V + primePowerDefect b) *
          (1 / Real.log 2 + 1 / Real.log ((a + 1 : ℕ) : ℝ))) := by
    gcongr
  have huLarge' :
      2 * ((V + primePowerDefect (u - 1)) *
          (1 / Real.log 2 + 1 / Real.log ((a + 1 : ℕ) : ℝ))) <
        ‖primeBlockPoly (primesRange a (u - 1)) w‖ :=
    lt_of_le_of_lt hthreshold huLarge
  obtain ⟨m, hmu, hmLarge⟩ :=
    exists_norm_vonMangoldtTwist_prefix_gt_of_primeBlockPoly_gt
      ha haUpper hprimeRange w hV huLarge'
  exact ⟨m, hmu.trans huUpper, hmLarge⟩

end

end RHTower.Sieve
