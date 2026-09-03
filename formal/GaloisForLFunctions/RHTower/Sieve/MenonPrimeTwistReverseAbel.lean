import GaloisForLFunctions.RHTower.Sieve.PrimeBlockTwistBound

/-!
# Reverse logarithmic Abel selection for Menon's exceptional prime block

An exceptional prime-indicator twist forces an exceptional log-weighted prime prefix.  Combining
this with the exact range identity routes an exceptional ordinary prime block to one literal
Chebyshev-prime prefix without inserting a proxy polynomial.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Converse selection implicit in summation by parts against `1/log`: if an initial prime twist
exceeds the Abel image of a uniform threshold, one actual log-weighted prefix exceeds it. -/
theorem exists_norm_vonMangoldtPrimeTwist_prefix_gt_of_primeTwist_gt
    (tau : ℝ) (N : ℕ) {M : ℝ}
    (hlarge : M *
        (1 / Real.log 2 + 1 / Real.log ((N + 1 : ℕ) : ℝ)) <
      ‖∑ n ∈ Finset.range (N + 1), primeTwist tau n‖) :
    ∃ m : ℕ, m ≤ N ∧
      M < ‖∑ n ∈ Finset.range (m + 1), vonMangoldtPrimeTwist tau n‖ := by
  by_contra hnot
  push Not at hnot
  have hprefix : ∀ m, m ≤ N →
      ‖∑ n ∈ Finset.range (m + 1), vonMangoldtPrimeTwist tau n‖ ≤ M := by
    intro m hm
    exact hnot m hm
  have hupper := norm_sum_primeTwist_le_of_monotone_bound tau N (fun _ => M)
    (fun m hm => hprefix m hm) (fun _ _ => le_rfl)
  simpa only using (not_lt_of_ge hupper hlarge)

/-- An exceptional ordinary prime interval forces one literal log-weighted prime prefix.  The
displayed Abel factor is evaluated at the lower endpoint, hence uniformly dominates both endpoint
factors in the exact range identity. -/
theorem exists_norm_vonMangoldtPrimeTwist_prefix_gt_of_primeBlockPoly_gt
    {B : Finset ℕ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b))
    (w : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hlarge : 2 * (M *
        (1 / Real.log 2 + 1 / Real.log ((a + 1 : ℕ) : ℝ))) <
      ‖primeBlockPoly B w‖) :
    ∃ K : ℕ, K ≤ b ∧ ∃ m : ℕ, m ≤ K ∧
      M < ‖∑ n ∈ Finset.range (m + 1),
        vonMangoldtPrimeTwist (-(2 * Real.pi * w)) n‖ := by
  let tau : ℝ := -(2 * Real.pi * w)
  let R : ℝ := M *
    (1 / Real.log 2 + 1 / Real.log ((a + 1 : ℕ) : ℝ))
  have hrange := norm_primeBlockPoly_le_of_range hab hB w
  have hend : R < ‖∑ n ∈ Finset.range (b + 1), primeTwist tau n‖ ∨
      R < ‖∑ n ∈ Finset.range (a + 1), primeTwist tau n‖ := by
    by_contra hnot
    push Not at hnot
    have hrange' : ‖primeBlockPoly B w‖ ≤
        ‖∑ n ∈ Finset.range (b + 1), primeTwist tau n‖ +
          ‖∑ n ∈ Finset.range (a + 1), primeTwist tau n‖ := by
      simpa only [tau] using hrange
    dsimp only [R] at hlarge hnot
    linarith [hrange']
  have hfactor :
      1 / Real.log 2 + 1 / Real.log ((b + 1 : ℕ) : ℝ) ≤
        1 / Real.log 2 + 1 / Real.log ((a + 1 : ℕ) : ℝ) := by
    have haR : (1 : ℝ) < ((a + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < a + 1)
    have haR0 : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by linarith
    have habR : (((a + 1 : ℕ) : ℝ)) ≤ ((b + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : a + 1 ≤ b + 1)
    have hlog := Real.log_le_log haR0 habR
    have hlogPos : 0 < Real.log (((a + 1 : ℕ) : ℝ)) := Real.log_pos haR
    have hinv := one_div_le_one_div_of_le hlogPos hlog
    linarith
  rcases hend with hb | haend
  · have hthreshold : M *
        (1 / Real.log 2 + 1 / Real.log ((b + 1 : ℕ) : ℝ)) <
          ‖∑ n ∈ Finset.range (b + 1), primeTwist tau n‖ := by
      have hmul := mul_le_mul_of_nonneg_left hfactor hM
      exact lt_of_le_of_lt hmul hb
    obtain ⟨m, hm, hmlarge⟩ :=
      exists_norm_vonMangoldtPrimeTwist_prefix_gt_of_primeTwist_gt tau b hthreshold
    exact ⟨b, le_rfl, m, hm, hmlarge⟩
  · obtain ⟨m, hm, hmlarge⟩ :=
      exists_norm_vonMangoldtPrimeTwist_prefix_gt_of_primeTwist_gt tau a haend
    exact ⟨a, hab, m, hm, hmlarge⟩

end

end RHTower.Sieve
