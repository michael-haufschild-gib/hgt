import GaloisForLFunctions.RHTower.WeilLogShiftEdgeMidpoint

/-! Exact mean and variance identities for the uniform-endpoint edge representation. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalEdgeIndexMean (r k : ℕ) : ℝ :=
  ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * ((i : ℕ) : ℝ)

def finiteWeilCanonicalMidpointIndexMean (r k : ℕ) : ℝ :=
  ∑ u : Fin (r + 2), finiteWeilCanonicalMixture r k (1 / 2) u * ((u : ℕ) : ℝ)

theorem finiteWeilCanonicalMidpointIndexMean_eq_edge (r k : ℕ) :
    finiteWeilCanonicalMidpointIndexMean r k = finiteWeilCanonicalEdgeIndexMean r k + 1 / 2 := by
  unfold finiteWeilCanonicalMidpointIndexMean
  rw [finiteWeilCanonicalMixture_midpoint_edge_pairing]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  have hs : (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
      (((i : ℕ) : ℝ) + (((i : ℕ) : ℝ) + 1))) = 2 * finiteWeilCanonicalEdgeIndexMean r k + 1 := by
    calc
      _ = ∑ i : Fin (r + 1), (2 * (finiteWeilCanonicalEdgeMass r k i * ((i : ℕ) : ℝ)) +
          finiteWeilCanonicalEdgeMass r k i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, finiteWeilCanonicalEdgeMass_sum]
        rfl
  rw [hs]
  ring

theorem finiteWeilCanonicalMixture_midpoint_edge_second_moment (r k : ℕ) (c : ℝ) :
    (∑ u : Fin (r + 2), finiteWeilCanonicalMixture r k (1 / 2) u * (((u : ℕ) : ℝ) - c) ^ 2) =
      (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        (((i : ℕ) : ℝ) + 1 / 2 - c) ^ 2) + 1 / 4 := by
  rw [finiteWeilCanonicalMixture_midpoint_edge_pairing]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  have hs : (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
      ((((i : ℕ) : ℝ) - c) ^ 2 + (((i : ℕ) : ℝ) + 1 - c) ^ 2)) =
      2 * (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        (((i : ℕ) : ℝ) + 1 / 2 - c) ^ 2) + 1 / 2 := by
    calc
      _ = ∑ i : Fin (r + 1), (2 * (finiteWeilCanonicalEdgeMass r k i *
          (((i : ℕ) : ℝ) + 1 / 2 - c) ^ 2) + (1 / 2) * finiteWeilCanonicalEdgeMass r k i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, finiteWeilCanonicalEdgeMass_sum]
        ring
  rw [hs]
  ring

theorem finiteWeilCanonicalMixture_midpoint_edge_variance (r k : ℕ) :
    (∑ u : Fin (r + 2), finiteWeilCanonicalMixture r k (1 / 2) u *
      (((u : ℕ) : ℝ) - finiteWeilCanonicalMidpointIndexMean r k) ^ 2) =
      (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) ^ 2) + 1 / 4 := by
  rw [finiteWeilCanonicalMixture_midpoint_edge_second_moment, finiteWeilCanonicalMidpointIndexMean_eq_edge]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteWeilCanonicalMixture_midpoint_edge_half_centered_second_moment (r k : ℕ) :
    (∑ u : Fin (r + 2), finiteWeilCanonicalMixture r k (1 / 2) u *
      (((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) =
      (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
        (((i : ℕ) : ℝ) - (r : ℝ) / 2) ^ 2) + 1 / 4 := by
  rw [finiteWeilCanonicalMixture_midpoint_edge_second_moment]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

end RHTower
