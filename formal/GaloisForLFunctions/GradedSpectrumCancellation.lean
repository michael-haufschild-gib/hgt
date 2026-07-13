import Mathlib

/-!
# Finite graded-spectrum cancellation

A signed or graded spectral presentation becomes a positive moment tower when every odd mode is
paired with an equal even mode and the unpaired even spectrum is nonnegative.  This is the finite
power-sum core of supersymmetric/Koszul cancellation: the common spectrum cancels before the
residual positive trace is read.
-/

namespace GaloisForLFunctions

/-- Power sum of a finite real spectrum with multiplicity. -/
def multisetPowerSum (s : Multiset ℝ) (n : ℕ) : ℝ :=
  (s.map fun x => x ^ n).sum

/-- Supertrace power sum of a finite graded real spectrum. -/
def gradedPowerSum (even odd : Multiset ℝ) (n : ℕ) : ℝ :=
  multisetPowerSum even n - multisetPowerSum odd n

theorem multisetPowerSum_add (s t : Multiset ℝ) (n : ℕ) :
    multisetPowerSum (s + t) n = multisetPowerSum s n + multisetPowerSum t n := by
  simp [multisetPowerSum]

/-- Equal paired modes cancel from every supertrace power simultaneously. -/
theorem gradedPowerSum_common_cancel (residual paired : Multiset ℝ) (n : ℕ) :
    gradedPowerSum (residual + paired) paired n = multisetPowerSum residual n := by
  rw [gradedPowerSum, multisetPowerSum_add]
  ring

/-- A finite nonnegative spectrum has nonnegative power sums in every degree. -/
theorem multisetPowerSum_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (n : ℕ) :
    0 ≤ multisetPowerSum s n := by
  unfold multisetPowerSum
  apply Multiset.sum_nonneg
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  exact pow_nonneg (hs x hx) n

/-- Positive cohomology statement: after common even/odd cancellation, a nonnegative unpaired
even spectrum has nonnegative supertrace powers in every degree. -/
theorem gradedPowerSum_common_cancel_nonneg
    {residual paired : Multiset ℝ} (hres : ∀ x ∈ residual, 0 ≤ x) (n : ℕ) :
    0 ≤ gradedPowerSum (residual + paired) paired n := by
  rw [gradedPowerSum_common_cancel]
  exact multisetPowerSum_nonneg hres n

end GaloisForLFunctions
