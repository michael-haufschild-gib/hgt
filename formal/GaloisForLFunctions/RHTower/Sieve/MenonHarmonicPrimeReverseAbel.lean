import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeAbel

/-!
# Reverse reciprocal Abel selection for Menon's harmonic prime block

An exceptional harmonic prime block forces one of its literal ordinary-prime prefixes to be
exceptional.  This is the exact contrapositive of the existing reciprocal Abel estimate.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- If a full harmonic prime interval exceeds the reciprocal Abel threshold, then one of the
actual prefixes `(a,m-1]` exceeds the underlying ordinary-prime threshold. -/
theorem exists_norm_primeBlockPoly_prefix_gt_of_harmonicPrimeBlockPoly_gt
    {B : Finset ℕ} {a b : ℕ} (hab : a ≤ b)
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b))
    (w : ℝ) {E : ℝ}
    (hlarge : E / ((a + 1 : ℕ) : ℝ) < ‖harmonicPrimeBlockPoly B w‖) :
    ∃ m : ℕ, a + 1 ≤ m ∧ m ≤ b + 1 ∧
      E < ‖primeBlockPoly (primesRange a (m - 1)) w‖ := by
  by_contra hnot
  push Not at hnot
  have hprefix : ∀ m : ℕ, a + 1 ≤ m → m ≤ b + 1 →
      ‖primeBlockPoly (primesRange a (m - 1)) w‖ ≤ E := by
    intro m ham hmb
    exact hnot m ham hmb
  have hupper := norm_harmonicPrimeBlockPoly_le_of_prefix hab hB w hprefix
  linarith

end

end RHTower.Sieve
