import Mathlib

/-!
# Counting wholly bad intervals

Disjoint half-open intervals of a common length `h`, all contained in a set of measure at most `M`,
number at most `M / h`.

This is the accounting that lets a Wiman–Valiron argument use a partition into short intervals: the
exceptional set has finite measure, so at most `M/h` of the `N = (T − t₀)/h` intervals can miss a
good radius entirely, and the total decrease accumulated over the remaining ones is
`(N − M/h)·σch/2 = σc(T − t₀ − M)/2`, which is independent of `h`.  Since that total cannot exceed
the initial value of `e^{-σφ}`, the length `T − t₀` is bounded.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal

/-- **Counting the wholly bad intervals.**  Disjoint half-open intervals of length `h` contained in a
set of measure at most `M` number at most `M / h`. -/
theorem card_mul_le_of_subset_of_volume_le {B : Set ℝ} {M h t₀ : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (hB : volume B ≤ ENNReal.ofReal M) {S : Finset ℕ}
    (hsub : ∀ i ∈ S, Ico (t₀ + i * h) (t₀ + (i + 1) * h) ⊆ B) :
    (S.card : ℝ) * h ≤ M := by
  classical
  set I : ℕ → Set ℝ := fun i => Ico (t₀ + i * h) (t₀ + (i + 1) * h) with hI
  have hdisj : (S : Set ℕ).PairwiseDisjoint I := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr ?_
    rintro x hx hx'
    rw [hI] at hx hx'
    simp only [mem_Ico] at hx hx'
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hlt
      nlinarith [hx.2, hx'.1, hh]
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hgt
      nlinarith [hx'.2, hx.1, hh]
  have hmeas : ∀ i, MeasurableSet (I i) := fun i => measurableSet_Ico
  have hunion : volume (⋃ i ∈ S, I i) = ∑ i ∈ S, volume (I i) :=
    measure_biUnion_finset hdisj (fun i _ => hmeas i)
  have hvol : ∀ i, volume (I i) = ENNReal.ofReal h := by
    intro i
    rw [hI, Real.volume_Ico]
    congr 1
    ring
  have hsubB : (⋃ i ∈ S, I i) ⊆ B := by
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨i, hiS, hxi⟩ := hx
    exact hsub i hiS hxi
  have hle : ∑ i ∈ S, volume (I i) ≤ ENNReal.ofReal M :=
    le_trans (hunion ▸ measure_mono hsubB) hB
  have hsum : ∑ i ∈ S, volume (I i) = (S.card : ℕ) • ENNReal.ofReal h := by
    rw [Finset.sum_congr rfl (fun i _ => hvol i), Finset.sum_const]
  rw [hsum, nsmul_eq_mul] at hle
  have hcast : ((S.card : ℕ) : ENNReal) * ENNReal.ofReal h
      = ENNReal.ofReal ((S.card : ℝ) * h) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [ENNReal.ofReal_natCast]
  rw [hcast] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hM).mp hle

end GaloisForLFunctions.HTGeometry
