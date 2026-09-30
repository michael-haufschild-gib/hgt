import GaloisForLFunctions.RHTower.SteinhausSmoothRoughPairCount
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open scoped BigOperators

noncomputable section
namespace RHTower
open SteinhausModel

private theorem hasSum_roughCount_smoothPair (y N : ℕ) (F : ℕ → ℕ → ℂ) :
    HasSum (fun ac : Nat.smoothNumbers y × Nat.smoothNumbers y =>
      (roughCount (Nat.primesBelow y) ((N : ℝ) / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)) : ℂ) *
        F ac.1 ac.2)
      (∑ a ∈ Nat.smoothNumbersUpTo N y, ∑ c ∈ Nat.smoothNumbersUpTo N y,
        (roughCount (Nat.primesBelow y) ((N : ℝ) / (max a c : ℕ)) : ℂ) * F a c) := by
  classical
  let A := Nat.smoothNumbersUpTo N y
  let S : Finset (Nat.smoothNumbers y) := A.subtype (fun a => a ∈ Nat.smoothNumbers y)
  let g (a c : ℕ) : ℂ :=
    (roughCount (Nat.primesBelow y) ((N : ℝ) / (max a c : ℕ)) : ℂ) * F a c
  have hmem (a : Nat.smoothNumbers y) : a ∈ S ↔ (a : ℕ) ≤ N := by
    simp only [S, A, Finset.mem_subtype, Nat.mem_smoothNumbersUpTo, a.property, and_true]
  have hA (a : ℕ) (ha : a ∈ A) : a ∈ Nat.smoothNumbers y :=
    (Nat.mem_smoothNumbersUpTo.mp ha).2
  have hz (ac : Nat.smoothNumbers y × Nat.smoothNumbers y) (h : ac ∉ S.product S) :
      g ac.1 ac.2 = 0 := by
    have hlarge : N < max (ac.1 : ℕ) (ac.2 : ℕ) := by
      by_contra hlarge
      have hle := Nat.le_of_not_gt hlarge
      exact h (Finset.mem_product.mpr
        ⟨(hmem ac.1).mpr ((le_max_left _ _).trans hle),
          (hmem ac.2).mpr ((le_max_right _ _).trans hle)⟩)
    simp only [g, roughCount_nat_div_eq_zero_of_lt _ hlarge, Nat.cast_zero, zero_mul]
  have h : HasSum (fun ac : Nat.smoothNumbers y × Nat.smoothNumbers y => g ac.1 ac.2)
      (∑ ac ∈ S.product S, g ac.1 ac.2) := hasSum_sum_of_ne_finset_zero hz
  have heq : (∑ ac ∈ S.product S, g ac.1 ac.2) = ∑ a ∈ A, ∑ c ∈ A, g a c := by
    calc
      _ = ∑ a ∈ S, ∑ c ∈ S, g a c := Finset.sum_product S S (fun ac => g ac.1 ac.2)
      _ = ∑ a ∈ S, ∑ c ∈ A, g a c := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_subtype_of_mem (fun c => g a c) hA
      _ = _ := Finset.sum_subtype_of_mem (fun a => ∑ c ∈ A, g a c) hA
  rw [heq] at h
  exact h

/-- The finite literal conditional variance is the sum of its zero-extended smooth-pair coefficients. -/
theorem hasSum_steinhausSummatory_frozenPrefix_pairCount (y N : ℕ) (ω : Omega) :
    HasSum (fun ac : Nat.smoothNumbers y × Nat.smoothNumbers y =>
      (roughCount (Nat.primesBelow y) ((N : ℝ) / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)) : ℂ) *
        (X ac.1 ω * (starRingEnd ℂ) (X ac.2 ω)))
      ((∫ η, ‖∑ n ∈ Finset.Icc 1 N,
        X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η)‖ ^ (2 : ℕ)
          ∂steinhausMeasure : ℝ) : ℂ) := by
  rw [integral_normSq_steinhausSummatory_frozenPrefix_eq_pairCount]
  exact hasSum_roughCount_smoothPair y N (fun a c => X a ω * (starRingEnd ℂ) (X c ω))

/-- Exact normalized arithmetic coefficient series, including the zero cutoff. -/
theorem hasSum_steinhausSummatory_frozenPrefix_normalizedPairCount (y N : ℕ) (ω : Omega) :
    HasSum (fun ac : Nat.smoothNumbers y × Nat.smoothNumbers y =>
      (((roughCount (Nat.primesBelow y) ((N : ℝ) / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)) : ℝ) /
        N : ℝ) : ℂ) * (X ac.1 ω * (starRingEnd ℂ) (X ac.2 ω)))
      (((∫ η, ‖∑ n ∈ Finset.Icc 1 N,
        X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η)‖ ^ (2 : ℕ)
          ∂steinhausMeasure) / N : ℝ) : ℂ) := by
  have h := (hasSum_steinhausSummatory_frozenPrefix_pairCount y N ω).div_const (N : ℂ)
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast, div_mul_eq_mul_div] using h

end RHTower
