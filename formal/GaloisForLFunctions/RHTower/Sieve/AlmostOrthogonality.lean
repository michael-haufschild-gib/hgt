import GaloisForLFunctions.RHTower.Sieve.LargeSieveDuality

/-!
# Almost orthogonality

A family that is not orthogonal still behaves like one as long as its Gram matrix has small rows.
Expanding `‖∑_r c_r φ_r‖²` into the Gram double sum and applying `|c_r||c_t| ≤ (|c_r|² + |c_t|²)/2`
splits it into two pieces, one controlled by the row sums and one by the column sums; the Gram
matrix is Hermitian, so both are the same bound.  Hence

`‖∑_r c_r φ_r‖² ≤ (max_r ∑_t |⟪φ_r, φ_t⟫|) ∑_r |c_r|²`,

and by the duality principle the Bessel form follows with the same constant.

This is the standard supplier of large sieve inequalities: an analytic input is needed only to bound
the Gram rows, after which the sieve inequality itself is formal.  The diagonal term `‖φ_r‖²` is
included in the row sum, so an exactly orthogonal family recovers Bessel's inequality with
`Δ = max_r ‖φ_r‖²`.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Gram matrix is Hermitian, so its entries have symmetric absolute values. -/
theorem norm_inner_symm (x y : H) : ‖⟪x, y⟫_ℂ‖ = ‖⟪y, x⟫_ℂ‖ := by
  rw [← inner_conj_symm x y, RCLike.norm_conj]

/-- The energy of a combination expanded over the Gram matrix. -/
theorem inner_sum_smul_sum_smul (s : Finset ι) (φ : ι → H) (c : ι → ℂ) :
    ⟪∑ r ∈ s, c r • φ r, ∑ t ∈ s, c t • φ t⟫_ℂ
      = ∑ r ∈ s, ∑ t ∈ s, (starRingEnd ℂ) (c r) * c t * ⟪φ r, φ t⟫_ℂ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

/-- **Almost-orthogonality, bilinear form.**  Small Gram rows give a large sieve inequality. -/
theorem norm_sum_smul_sq_le_of_schur (s : Finset ι) (φ : ι → H) {Δ : ℝ}
    (hrow : ∀ r ∈ s, ∑ t ∈ s, ‖⟪φ r, φ t⟫_ℂ‖ ≤ Δ) (c : ι → ℂ) :
    ‖∑ r ∈ s, c r • φ r‖ ^ (2 : ℕ) ≤ Δ * ∑ r ∈ s, ‖c r‖ ^ (2 : ℕ) := by
  classical
  set v : H := ∑ r ∈ s, c r • φ r with hv
  have hnormself : ‖v‖ ^ (2 : ℕ) = ‖⟪v, v⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [hnormself, hv, inner_sum_smul_sum_smul]
  have houter : ‖∑ r ∈ s, ∑ t ∈ s, (starRingEnd ℂ) (c r) * c t * ⟪φ r, φ t⟫_ℂ‖
      ≤ ∑ r ∈ s, ∑ t ∈ s, ‖c r‖ * ‖c t‖ * ‖⟪φ r, φ t⟫_ℂ‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro r _
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro t _
    rw [norm_mul, norm_mul]
    simp
  refine le_trans houter ?_
  have hamgm : ∑ r ∈ s, ∑ t ∈ s, ‖c r‖ * ‖c t‖ * ‖⟪φ r, φ t⟫_ℂ‖
      ≤ ∑ r ∈ s, ∑ t ∈ s,
          ((‖c r‖ ^ (2 : ℕ) + ‖c t‖ ^ (2 : ℕ)) / 2) * ‖⟪φ r, φ t⟫_ℂ‖ := by
    refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun t _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    nlinarith [sq_nonneg (‖c r‖ - ‖c t‖)]
  refine le_trans hamgm ?_
  have hsplit : ∑ r ∈ s, ∑ t ∈ s, ((‖c r‖ ^ (2 : ℕ) + ‖c t‖ ^ (2 : ℕ)) / 2) * ‖⟪φ r, φ t⟫_ℂ‖
      = (∑ r ∈ s, ∑ t ∈ s, (‖c r‖ ^ (2 : ℕ) / 2) * ‖⟪φ r, φ t⟫_ℂ‖)
        + ∑ r ∈ s, ∑ t ∈ s, (‖c t‖ ^ (2 : ℕ) / 2) * ‖⟪φ r, φ t⟫_ℂ‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [hsplit]
  have hfirst : ∑ r ∈ s, ∑ t ∈ s, (‖c r‖ ^ (2 : ℕ) / 2) * ‖⟪φ r, φ t⟫_ℂ‖
      ≤ Δ / 2 * ∑ r ∈ s, ‖c r‖ ^ (2 : ℕ) := by
    have hstep : ∀ r ∈ s, ∑ t ∈ s, (‖c r‖ ^ (2 : ℕ) / 2) * ‖⟪φ r, φ t⟫_ℂ‖
        ≤ (Δ / 2) * ‖c r‖ ^ (2 : ℕ) := by
      intro r hr
      rw [← Finset.mul_sum]
      have := mul_le_mul_of_nonneg_left (hrow r hr) (by positivity : (0 : ℝ) ≤ ‖c r‖ ^ (2 : ℕ) / 2)
      linarith [this]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.mul_sum]
  have hsecond : ∑ r ∈ s, ∑ t ∈ s, (‖c t‖ ^ (2 : ℕ) / 2) * ‖⟪φ r, φ t⟫_ℂ‖
      ≤ Δ / 2 * ∑ r ∈ s, ‖c r‖ ^ (2 : ℕ) := by
    rw [Finset.sum_comm]
    have hstep : ∀ t ∈ s, ∑ r ∈ s, (‖c t‖ ^ (2 : ℕ) / 2) * ‖⟪φ r, φ t⟫_ℂ‖
        ≤ (Δ / 2) * ‖c t‖ ^ (2 : ℕ) := by
      intro t ht
      have hsymm : ∑ r ∈ s, ‖⟪φ r, φ t⟫_ℂ‖ = ∑ r ∈ s, ‖⟪φ t, φ r⟫_ℂ‖ :=
        Finset.sum_congr rfl fun r _ => norm_inner_symm _ _
      rw [← Finset.mul_sum, hsymm]
      have := mul_le_mul_of_nonneg_left (hrow t ht) (by positivity : (0 : ℝ) ≤ ‖c t‖ ^ (2 : ℕ) / 2)
      linarith [this]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.mul_sum]
  linarith

/-- **Almost-orthogonality, Bessel form.**  Composing with the duality principle. -/
theorem sum_norm_inner_sq_le_of_schur (s : Finset ι) (φ : ι → H) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hrow : ∀ r ∈ s, ∑ t ∈ s, ‖⟪φ r, φ t⟫_ℂ‖ ≤ Δ) (a : H) :
    ∑ r ∈ s, ‖⟪φ r, a⟫_ℂ‖ ^ (2 : ℕ) ≤ Δ * ‖a‖ ^ (2 : ℕ) :=
  sum_norm_inner_sq_le_of_bilinear s φ hΔ (norm_sum_smul_sq_le_of_schur s φ hrow) a

end RHTower.Sieve
