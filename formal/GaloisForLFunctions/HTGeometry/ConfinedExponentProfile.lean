import GaloisForLFunctions.HTGeometry.BoundedRelationConfinement

/-!
# An explicit super-increasing exponent profile

A sequence of natural numbers in which each term exceeds every bounded-height combination of its
predecessors has bounded-relation confinement: in a relation of height at most `D`, the largest
index carries a coefficient smaller than one in absolute value once that index is at least `D`.

The profile realized here is `e n = (n + 1) · (e 0 + ⋯ + e (n-1)) + 1`, whose partial sums satisfy
the closed recursion `S (n+1) = (n+2) · S n + 1`.  It grows at least quadratically, so the power
series `∑ t ^ (e n) X ^ n` has infinite radius of convergence for `|t| < 1`.
-/

open Filter Finset

namespace GaloisForLFunctions

noncomputable section

/-- Partial sums of the super-increasing exponent profile. -/
def confinedProfileSum : ℕ → ℕ
  | 0 => 0
  | (n + 1) => (n + 2) * confinedProfileSum n + 1

/-- A super-increasing exponent profile: each term exceeds `n + 1` times the sum of its
predecessors. -/
def confinedProfile (n : ℕ) : ℕ := (n + 1) * confinedProfileSum n + 1

@[simp] theorem confinedProfileSum_zero : confinedProfileSum 0 = 0 := rfl

theorem confinedProfileSum_succ (n : ℕ) :
    confinedProfileSum (n + 1) = (n + 2) * confinedProfileSum n + 1 := rfl

theorem confinedProfile_pos (n : ℕ) : 0 < confinedProfile n := by
  rw [confinedProfile]; omega

/-- The partial sums are the partial sums. -/
theorem sum_range_confinedProfile (n : ℕ) :
    ∑ k ∈ Finset.range n, confinedProfile k = confinedProfileSum n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, confinedProfileSum_succ, confinedProfile]
      ring

/-- Each term dominates every combination of its predecessors with coefficients of height at most
its index. -/
theorem confinedProfile_dominates {D n : ℕ} (hD : D ≤ n + 1) :
    D * confinedProfileSum n < confinedProfile n := by
  rw [confinedProfile]
  have := Nat.mul_le_mul_right (confinedProfileSum n) hD
  omega

theorem le_confinedProfileSum (n : ℕ) : n ≤ confinedProfileSum n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [confinedProfileSum_succ]
      nlinarith [ih]

/-- The profile grows at least quadratically. -/
theorem sq_le_confinedProfile (n : ℕ) : n * n ≤ confinedProfile n := by
  have h := le_confinedProfileSum n
  rw [confinedProfile]
  nlinarith [h]

/-- **The profile has bounded-relation confinement.**  In a relation of height at most `D`, the
largest participating index cannot be at least `D`: its own term would then exceed the total mass of
all the smaller terms. -/
theorem boundedRelationConfinement_confinedProfile :
    BoundedRelationConfinement (fun n => ((confinedProfile n : ℤ))) := by
  classical
  intro D
  refine ⟨D, ?_⟩
  intro d hd hrel n hn
  by_contra hlt
  have hle : D ≤ n := Nat.not_lt.mp hlt
  have hne : d.support.Nonempty := ⟨n, hn⟩
  set m : ℕ := d.support.max' hne with hm
  have hmmem : m ∈ d.support := Finset.max'_mem _ hne
  have hnm : n ≤ m := Finset.le_max' _ n hn
  have hDm : D ≤ m := le_trans hle hnm
  have hsum : ∑ k ∈ d.support, d k * (confinedProfile k : ℤ) = 0 := by
    rw [← hrel, Finsupp.sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul]
  have hsplit : d m * (confinedProfile m : ℤ) +
      ∑ k ∈ d.support.erase m, d k * (confinedProfile k : ℤ) = 0 := by
    rw [← Finset.add_sum_erase _ _ hmmem] at hsum
    exact hsum
  have hsubset : d.support.erase m ⊆ Finset.range m := by
    intro k hk
    obtain ⟨hkm, hks⟩ := Finset.mem_erase.mp hk
    have : k ≤ m := Finset.le_max' _ k hks
    exact Finset.mem_range.mpr (lt_of_le_of_ne this hkm)
  have hbound : |∑ k ∈ d.support.erase m, d k * (confinedProfile k : ℤ)| ≤
      (D : ℤ) * (confinedProfileSum m : ℤ) := by
    calc |∑ k ∈ d.support.erase m, d k * (confinedProfile k : ℤ)|
        ≤ ∑ k ∈ d.support.erase m, |d k * (confinedProfile k : ℤ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range m, (D : ℤ) * (confinedProfile k : ℤ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_ |>.trans' ?_
          · intro k _ _
            positivity
          · refine Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (confinedProfile k : ℤ))]
            exact mul_le_mul_of_nonneg_right (hd k) (by positivity)
      _ = (D : ℤ) * (confinedProfileSum m : ℤ) := by
          rw [← Finset.mul_sum, ← Nat.cast_sum, sum_range_confinedProfile]
  have hstrict : (D : ℤ) * (confinedProfileSum m : ℤ) < (confinedProfile m : ℤ) := by
    have := confinedProfile_dominates (D := D) (n := m) (by omega)
    exact_mod_cast this
  have hdm : |d m| * (confinedProfile m : ℤ) < (confinedProfile m : ℤ) := by
    have habs : |d m * (confinedProfile m : ℤ)| =
        |∑ k ∈ d.support.erase m, d k * (confinedProfile k : ℤ)| := by
      rw [show d m * (confinedProfile m : ℤ) =
        -(∑ k ∈ d.support.erase m, d k * (confinedProfile k : ℤ)) by linarith [hsplit], abs_neg]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (confinedProfile m : ℤ))] at habs
    calc |d m| * (confinedProfile m : ℤ) ≤ (D : ℤ) * (confinedProfileSum m : ℤ) := habs ▸ hbound
      _ < (confinedProfile m : ℤ) := hstrict
  have hpos : (0 : ℤ) < (confinedProfile m : ℤ) := by
    exact_mod_cast confinedProfile_pos m
  have hzero : d m = 0 := by
    have habs : |d m| < 1 := by
      by_contra hcon
      exact absurd hdm (not_lt.mpr (le_mul_of_one_le_left hpos.le (not_lt.mp hcon)))
    have := abs_lt.mp habs
    omega
  exact (Finsupp.mem_support_iff.mp hmmem) hzero

end

end GaloisForLFunctions
