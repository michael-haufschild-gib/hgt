import GaloisForLFunctions.HTGeometry.HermitianSpectralWindowBounds
import Mathlib.Tactic.Linarith

/-!
# Energy as a chain of distances to nested spectral spaces

Successive level gaps weight squared distances to successive spectral cutoffs.
The identity is finite summation by parts followed by Parseval. It is the
finite-dimensional mechanism behind the stability chain in Theorem 1.2 of
Do–Duong–Lam–Lu–Nguyen, *Second order Heisenberg Uncertainty Principle for
solenoidal fields*, https://arxiv.org/abs/2611.00362, equation (5.5).
-/

noncomputable section
open Finset
open scoped BigOperators RealInnerProductSpace
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.BiScaleUncertainty

/-- A truncated chain of level increments telescopes at the coordinate's level. -/
theorem level_chain_telescope (energy : ℕ → ℝ) (N j : ℕ) :
    (∑ k ∈ range N, if k < j then energy (k + 1) - energy k else 0) =
      energy (min j N) - energy 0 := by
  have hsub : range (min j N) ⊆ range N := range_mono (min_le_right _ _)
  calc
    _ = ∑ k ∈ range (min j N), if k < j then energy (k + 1) - energy k else 0 := by
      symm
      apply sum_subset hsub
      intro k hk hnot
      have hkN := mem_range.mp hk
      have hkm := not_lt.mp (fun h => hnot (mem_range.mpr h))
      rw [if_neg (by omega)]
    _ = ∑ k ∈ range (min j N), (energy (k + 1) - energy k) := by
      apply sum_congr rfl
      intro k hk
      exact if_pos (lt_of_lt_of_le (mem_range.mp hk) (min_le_left _ _))
    _ = _ := sum_range_sub energy _

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℝ}

/-- The spectral space spanned by coordinates whose assigned level is at most `k`. -/
def levelProjection (hA : A.IsHermitian) (level : I → ℕ) (k : ℕ)
    (v : EuclideanSpace ℝ I) : EuclideanSpace ℝ I :=
  hermitianEigenProjection hA (univ.filter (fun i => level i ≤ k)) v

/-- Parseval identifies distance to a spectral cutoff with the omitted coordinate mass. -/
theorem levelProjection_error (hA : A.IsHermitian) (level : I → ℕ) (k : ℕ)
    (v : EuclideanSpace ℝ I) :
    ‖v - levelProjection hA level k v‖ ^ 2 =
      ∑ i, if k < level i then ⟪v, hA.eigenvectorBasis i⟫ ^ 2 else 0 := by
  rw [← hA.eigenvectorBasis.sum_sq_inner_left]
  apply sum_congr rfl
  intro i _
  rw [inner_sub_left, levelProjection, inner_hermitianEigenProjection]
  simp only [mem_filter, mem_univ, true_and]
  by_cases hi : level i ≤ k
  · rw [if_pos hi, sub_self,
      zero_pow (by omega), if_neg (not_lt.mpr hi)]
  · rw [if_neg hi,
      sub_zero, if_pos (lt_of_not_ge hi)]

/-- Exact finite stability chain, with each coordinate's energy capped at the last level. -/
theorem nested_projection_energy (hA : A.IsHermitian) (level : I → ℕ)
    (energy : ℕ → ℝ) (N : ℕ) (v : EuclideanSpace ℝ I) :
    (∑ k ∈ range N, (energy (k + 1) - energy k) * ‖v - levelProjection hA level k v‖ ^ 2) =
      ∑ i, (energy (min (level i) N) - energy 0) * ⟪v, hA.eigenvectorBasis i⟫ ^ 2 := by
  simp_rw [levelProjection_error, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  calc
    _ = (∑ k ∈ range N, if k < level i then energy (k + 1) - energy k else 0) *
        ⟪v, hA.eigenvectorBasis i⟫ ^ 2 := by
      rw [sum_mul]
      apply sum_congr rfl
      intro k _
      split_ifs <;> simp only [mul_zero, zero_mul]
    _ = _ := by rw [level_chain_telescope]

/-- The decreasing spectral enumeration, extended by zero beyond the dimension. -/
def eigenvalueAt (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  if hk : k < Fintype.card I then hA.eigenvalues₀ ⟨k, hk⟩ else 0

/-- The position of an eigenvector in the decreasing spectral enumeration. -/
def eigenvalueIndex (i : I) : ℕ :=
  ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card I))).symm i).val

omit [DecidableEq I] in
theorem eigenvalueIndex_lt (i : I) : eigenvalueIndex i < Fintype.card I :=
  ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card I))).symm i).isLt

theorem eigenvalueAt_index (hA : A.IsHermitian) (i : I) :
    eigenvalueAt hA (eigenvalueIndex i) = hA.eigenvalues i := by
  rw [eigenvalueAt, dif_pos (eigenvalueIndex_lt i)]
  rfl

/-- Every successive spectral gap is nonnegative within the matrix dimension. -/
theorem eigenvalueAt_gap_nonneg (hA : A.IsHermitian) (k : ℕ)
    (hk : k + 1 < Fintype.card I) :
    0 ≤ eigenvalueAt hA k - eigenvalueAt hA (k + 1) := by
  rw [eigenvalueAt, dif_pos (by omega), eigenvalueAt, dif_pos hk]
  exact sub_nonneg.mpr (hA.eigenvalues₀_antitone (by exact Nat.le_succ k))

/-- The Rayleigh deficit is exactly the full chain of distances to top spectral spaces.
Repeated eigenvalues cause zero increments and require no separate assumptions. -/
theorem hermitian_deficit_eq_nested_distances (hA : A.IsHermitian)
    (v : EuclideanSpace ℝ I) :
    eigenvalueAt hA 0 * ‖v‖ ^ 2 - ⟪Matrix.toEuclideanLin A v, v⟫ =
      ∑ k ∈ range (Fintype.card I - 1),
        (eigenvalueAt hA k - eigenvalueAt hA (k + 1)) *
          ‖v - levelProjection hA eigenvalueIndex k v‖ ^ 2 := by
  have h := nested_projection_energy hA eigenvalueIndex
    (fun k => -eigenvalueAt hA k) (Fintype.card I - 1) v
  simp only [neg_sub_neg] at h
  rw [shiftedHermitianEnergy_eq_sum, h]
  apply sum_congr rfl
  intro i _
  have hi : eigenvalueIndex i ≤ Fintype.card I - 1 := by
    have := eigenvalueIndex_lt i
    omega
  rw [min_eq_left hi, eigenvalueAt_index]

/-- Arbitrary chain weights act on a spectral coordinate by their prefix sum. -/
theorem weighted_projection_chain (hA : A.IsHermitian) (level : I → ℕ)
    (w : ℕ → ℝ) (N : ℕ) (v : EuclideanSpace ℝ I) :
    (∑ k ∈ range N, w k * ‖v - levelProjection hA level k v‖ ^ 2) =
      ∑ i, (∑ k ∈ range (min (level i) N), w k) * ⟪v, hA.eigenvectorBasis i⟫ ^ 2 := by
  have h := nested_projection_energy hA level (fun j => ∑ k ∈ range j, w k) N v
  simpa only [sum_range_succ, add_sub_cancel_left, sum_range_zero, sub_zero] using h

/-- A stability chain holds for every vector exactly when every cumulative
weight is bounded by the corresponding spectral deficit. Testing individual
eigenvectors proves necessity, so the criterion loses no constants. -/
theorem projection_chain_bound_iff (hA : A.IsHermitian) (level : I → ℕ)
    (w : ℕ → ℝ) (N : ℕ) (c : ℝ) :
    (∀ v : EuclideanSpace ℝ I,
      (∑ k ∈ range N, w k * ‖v - levelProjection hA level k v‖ ^ 2) ≤
        c * ‖v‖ ^ 2 - ⟪Matrix.toEuclideanLin A v, v⟫) ↔
      ∀ i, (∑ k ∈ range (min (level i) N), w k) ≤ c - hA.eigenvalues i := by
  constructor
  · intro h i
    have hi := h (hA.eigenvectorBasis i)
    rw [weighted_projection_chain hA, shiftedHermitianEnergy_eq_sum hA] at hi
    simpa [hA.eigenvectorBasis.inner_eq_ite] using hi
  · intro h v
    rw [weighted_projection_chain hA, shiftedHermitianEnergy_eq_sum hA]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

/-- Every initial segment of the exact spectral chain is a valid lower bound. -/
theorem partial_spectral_chain_le_deficit (hA : A.IsHermitian) (N : ℕ)
    (hN : N ≤ Fintype.card I - 1) (v : EuclideanSpace ℝ I) :
    (∑ k ∈ range N, (eigenvalueAt hA k - eigenvalueAt hA (k + 1)) *
        ‖v - levelProjection hA eigenvalueIndex k v‖ ^ 2) ≤
      eigenvalueAt hA 0 * ‖v‖ ^ 2 - ⟪Matrix.toEuclideanLin A v, v⟫ := by
  rw [hermitian_deficit_eq_nested_distances]
  apply sum_le_sum_of_subset_of_nonneg (range_mono hN)
  intro k hk _
  have hk' := mem_range.mp hk
  exact mul_nonneg (eigenvalueAt_gap_nonneg hA k (by omega)) (sq_nonneg _)

#print axioms nested_projection_energy
#print axioms hermitian_deficit_eq_nested_distances
#print axioms projection_chain_bound_iff
#print axioms partial_spectral_chain_le_deficit
end GaloisForLFunctions.BiScaleUncertainty
