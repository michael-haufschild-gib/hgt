import Mathlib

/-!
# Positivity of a diagonally dominant quadratic form with a bounded perturbation

A quadratic form whose diagonal entries are bounded below by `e > 0` and whose off-diagonal
entries are small stays positive definite; scaling it by a large factor `c` also absorbs any
perturbation whose entries are bounded by a fixed constant.

This is the finite-dimensional core of the prolate trial-space estimate: the Gram matrix of a
rescaled Hermite family is diagonally dominant once the bandwidth is large, and the bandwidth
factor on the rung term outgrows the bounded corrections.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **Diagonally dominant positivity with a bounded perturbation.** -/
theorem gramForm_pos_of_bounds {j : ℕ} {Gw Cr : Fin (j + 1) → Fin (j + 1) → ℝ}
    {c e C θ : ℝ}
    (hdiag : ∀ i, e ≤ Gw i i)
    (hoff : ∀ i k, i ≠ k → |Gw i k| ≤ θ)
    (hCr : ∀ i k, |Cr i k| ≤ C)
    (he : 0 < e) (hθ0 : 0 ≤ θ) (hC0 : 0 ≤ C)
    (hθ : θ * ((j : ℝ) + 1) ≤ e / 2)
    (hc : 0 < c) (hcbig : C * ((j : ℝ) + 1) < c * (e / 2))
    (a : Fin (j + 1) → ℝ) (ha : ∃ i, a i ≠ 0) :
    0 < c * (∑ i, ∑ k, a i * a k * Gw i k) + ∑ i, ∑ k, a i * a k * Cr i k := by
  classical
  obtain ⟨i₀, hi₀⟩ := ha
  set A : ℝ := ∑ i, |a i| with hAdef
  set T : ℝ := ∑ i, a i ^ (2 : ℕ) with hTdef
  have hTpos : 0 < T := by
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i₀, Finset.mem_univ _, ?_⟩
    positivity
  have hA2 : A ^ (2 : ℕ) ≤ ((j : ℝ) + 1) * T := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (j + 1))))
      (f := fun i => |a i|)
    simpa [hAdef, hTdef, sq_abs, Finset.card_univ] using h
  -- the diagonal/off-diagonal split
  have hsplit : ∀ M : Fin (j + 1) → Fin (j + 1) → ℝ,
      (∑ i, ∑ k, a i * a k * M i k)
        = (∑ i, a i ^ (2 : ℕ) * M i i) + ∑ i, ∑ k ∈ Finset.univ.erase i, a i * a k * M i k := by
    intro M
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase Finset.univ (fun k => a i * a k * M i k) (Finset.mem_univ i)]
    congr 1
    ring
  -- a double sum of absolute values factors
  have hdouble : ∀ t : ℝ, (∑ i : Fin (j + 1), ∑ k : Fin (j + 1), t * (|a i| * |a k|)) = t * A ^ (2 : ℕ) := by
    intro t
    have : ∀ i : Fin (j + 1), (∑ k : Fin (j + 1), t * (|a i| * |a k|)) = t * |a i| * A := by
      intro i
      rw [hAdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl fun i _ => this i]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hAdef]
    ring
  -- bound for an off-diagonal double sum
  have hoffbound : ∀ (M : Fin (j + 1) → Fin (j + 1) → ℝ) (t : ℝ),
      (∀ i k, i ≠ k → |M i k| ≤ t) → 0 ≤ t →
      |∑ i, ∑ k ∈ Finset.univ.erase i, a i * a k * M i k| ≤ t * A ^ (2 : ℕ) := by
    intro M t hM ht
    have step1 : |∑ i, ∑ k ∈ Finset.univ.erase i, a i * a k * M i k|
        ≤ ∑ i, ∑ k ∈ Finset.univ.erase i, t * (|a i| * |a k|) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k hk => ?_)
      have hik : i ≠ k := fun h => (Finset.mem_erase.1 hk).1 h.symm
      rw [abs_mul, abs_mul]
      have h1 : |M i k| ≤ t := hM i k hik
      have h2 : (0 : ℝ) ≤ |a i| * |a k| := by positivity
      nlinarith [h1, h2, abs_nonneg (a i), abs_nonneg (a k)]
    refine le_trans step1 ?_
    rw [← hdouble t]
    refine Finset.sum_le_sum fun i _ => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun k _ _ => ?_
    positivity
  -- bound for a full double sum
  have hfullbound : ∀ (M : Fin (j + 1) → Fin (j + 1) → ℝ) (t : ℝ),
      (∀ i k, |M i k| ≤ t) → 0 ≤ t → |∑ i, ∑ k, a i * a k * M i k| ≤ t * A ^ (2 : ℕ) := by
    intro M t hM ht
    refine le_trans ?_ (le_of_eq (hdouble t))
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_mul]
    have h1 : |M i k| ≤ t := hM i k
    have h2 : (0 : ℝ) ≤ |a i| * |a k| := by positivity
    nlinarith [h1, h2, abs_nonneg (a i), abs_nonneg (a k)]
  -- the diagonal part
  have hdiagsum : e * T ≤ ∑ i, a i ^ (2 : ℕ) * Gw i i := by
    rw [hTdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hdiag i
    nlinarith [sq_nonneg (a i), this]
  have hoffsum : |∑ i, ∑ k ∈ Finset.univ.erase i, a i * a k * Gw i k| ≤ θ * A ^ (2 : ℕ) :=
    hoffbound Gw θ hoff hθ0
  have hcrsum : |∑ i, ∑ k, a i * a k * Cr i k| ≤ C * A ^ (2 : ℕ) := hfullbound Cr C hCr hC0
  have hAT : θ * A ^ (2 : ℕ) ≤ (e / 2) * T := by
    have h1 : θ * A ^ (2 : ℕ) ≤ θ * (((j : ℝ) + 1) * T) := by
      exact mul_le_mul_of_nonneg_left hA2 hθ0
    nlinarith [h1, hθ, hTpos.le]
  have hCT : C * A ^ (2 : ℕ) ≤ (C * ((j : ℝ) + 1)) * T := by
    have h1 : C * A ^ (2 : ℕ) ≤ C * (((j : ℝ) + 1) * T) := mul_le_mul_of_nonneg_left hA2 hC0
    nlinarith [h1]
  -- assemble
  have hS1 : (e / 2) * T ≤ ∑ i, ∑ k, a i * a k * Gw i k := by
    rw [hsplit Gw]
    have habs := abs_le.1 hoffsum
    nlinarith [hdiagsum, habs.1, hAT]
  have hS2 : -((C * ((j : ℝ) + 1)) * T) ≤ ∑ i, ∑ k, a i * a k * Cr i k := by
    have habs := abs_le.1 hcrsum
    nlinarith [habs.1, hCT]
  nlinarith [hS1, hS2, hTpos, hc, hcbig]

end GaloisForLFunctions.HTGeometry
