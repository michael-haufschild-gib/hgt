import GaloisForLFunctions.RHTower.Sieve.GSTailAssembly
import GaloisForLFunctions.RHTower.Sieve.MoebiusFrequencyDistance
import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange

/-!
# The pretentious distance from its tail alone

Every term of `∑_{p ≤ z}(1 + cos(t log p))/p` is nonnegative, so the distance is bounded below by the
part of the sum above any cutoff.  On that part the harmonic mass is `mertensS z − mertensS y` and
the oscillation is the Granville–Soundararajan tail.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The distance from its tail.** -/
theorem mulDistSqPair_ge_tail {f : ℕ → ℂ} {z y : ℕ} (hyz : y ≤ z)
    (hf : ∀ p ∈ Nat.primesLE z, f p = -1) (t : ℝ) :
    (mertensS z - mertensS y)
        + ∑ p ∈ primesRange y z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)
      ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  classical
  rw [mulDistSqPair_neg_one_split hf t]
  have hsub : primesRange y z ⊆ Nat.primesLE z := Finset.sdiff_subset
  have hsplitP : (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ))
        + ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)
      = ∑ p ∈ Nat.primesLE z, (1 / (p : ℝ) + Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)) := by
    rw [Finset.sum_add_distrib]
  have hsplitR : (∑ p ∈ primesRange y z, 1 / (p : ℝ))
        + ∑ p ∈ primesRange y z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)
      = ∑ p ∈ primesRange y z, (1 / (p : ℝ) + Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)) := by
    rw [Finset.sum_add_distrib]
  have hnonneg : ∀ p ∈ Nat.primesLE z, p ∉ primesRange y z →
      0 ≤ 1 / (p : ℝ) + Real.cos (t * Real.log (p : ℝ)) / (p : ℝ) := by
    intro p hp _
    have hprime : p.Prime := (Nat.mem_primesLE.1 hp).2
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hcos : (-1 : ℝ) ≤ Real.cos (t * Real.log (p : ℝ)) := Real.neg_one_le_cos _
    have hval : 1 / (p : ℝ) + Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)
        = (1 + Real.cos (t * Real.log (p : ℝ))) / (p : ℝ) := by ring
    rw [hval]
    exact div_nonneg (by linarith) hp0.le
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hmass : (∑ p ∈ primesRange y z, 1 / (p : ℝ)) = mertensS z - mertensS y :=
    sum_inv_primesRange hyz
  rw [hsplitP]
  refine le_trans (le_of_eq ?_) hmono
  rw [← hsplitR, hmass]

end

end RHTower.Sieve
