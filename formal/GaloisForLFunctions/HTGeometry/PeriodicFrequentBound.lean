import GaloisForLFunctions.HTGeometry.OscillatingRootLimsup

/-!
# Periodic sequences are bounded and frequently non-degenerate

A sequence with a positive period is bounded, and if it is positive at one index
then it is bounded below by that value infinitely often — namely along the whole
arithmetic progression through that index.

Together with the root-limsup law for bounded, frequently non-degenerate
factors, this handles the oscillating factor of the independent cusp-constant
computation: `k ↦ cos(π(1-s+k)/2)` has period four, and cannot vanish on every
residue because `cos² + sin² = 1`.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section Periodic

variable {f : ℕ → ℝ} {p : ℕ}

/-- A periodic index sequence advances by whole periods. -/
theorem periodic_add_mul (hper : ∀ k, f (k + p) = f k) (k n : ℕ) :
    f (k + n * p) = f k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have : k + (n + 1) * p = (k + n * p) + p := by ring
      rw [this, hper, ih]

/-- **A periodic sequence is bounded.** -/
theorem exists_bound_of_periodic (hp : 0 < p) (hper : ∀ k, f (k + p) = f k) :
    ∃ C : ℝ, ∀ k, f k ≤ C := by
  classical
  refine ⟨Finset.sup' (Finset.range p) (by simp [hp.ne']) f, fun k => ?_⟩
  have hmod : f k = f (k % p) := by
    conv_lhs => rw [← Nat.mod_add_div k p]
    rw [mul_comm p (k / p)]
    exact periodic_add_mul hper (k % p) (k / p)
  rw [hmod]
  exact Finset.le_sup' f (Finset.mem_range.mpr (Nat.mod_lt k hp))

/-- **A periodic sequence positive somewhere is frequently bounded below.** -/
theorem frequently_le_of_periodic (hp : 0 < p) (hper : ∀ k, f (k + p) = f k)
    (k₀ : ℕ) :
    ∃ᶠ k in atTop, f k₀ ≤ f k := by
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨k₀ + N * p, ?_, ?_⟩
  · have hNp : N ≤ N * p := Nat.le_mul_of_pos_right N hp
    omega
  · rw [periodic_add_mul hper k₀ N]

/-- **The root limsup of a periodic factor is one.**  A periodic sequence that is
non-negative and positive somewhere contributes nothing to the root growth. -/
theorem limsup_rpow_inv_eq_one_of_periodic (hp : 0 < p)
    (hper : ∀ k, f (k + p) = f k) (hnn : ∀ k, 0 ≤ f k) {k₀ : ℕ} (hk₀ : 0 < f k₀) :
    limsup (fun k : ℕ => (f k) ^ (1 / (k : ℝ))) atTop = 1 := by
  obtain ⟨C, hC⟩ := exists_bound_of_periodic hp hper
  have hCpos : 0 < C := lt_of_lt_of_le hk₀ (hC k₀)
  exact limsup_rpow_inv_eq_one hCpos hk₀ hnn hC
    (frequently_le_of_periodic hp hper k₀)

end Periodic

end GaloisForLFunctions.HTGeometry
