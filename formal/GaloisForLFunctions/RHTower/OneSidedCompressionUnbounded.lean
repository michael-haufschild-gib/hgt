import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

/-!
# A one-sided compression bound does not produce a bounded operator

The negative diagonal form `k[v] = -∑ n |v n|²` on the finitely supported vectors of `ℓ²(ℕ)`
satisfies the one-sided inequality `k[v] ≤ ‖v‖²`, and so does every finite compression.  No bounded
operator represents it: a bounded operator has uniformly bounded diagonal inner products, while the
diagonal entries of this form are `-n`.

A finite one-sided form inequality therefore does not by itself construct a bounded self-adjoint
contraction.
-/

noncomputable section

namespace RHTower

open scoped BigOperators

/-- The negative diagonal form is bounded above by the norm form on every finitely supported
vector, because it is nonpositive. -/
theorem negDiagonalForm_le_normForm (S : Finset ℕ) (v : ℕ → ℂ) :
    -∑ n ∈ S, (n : ℝ) * ‖v n‖ ^ (2 : ℕ) ≤ ∑ n ∈ S, ‖v n‖ ^ (2 : ℕ) := by
  have hneg : -∑ n ∈ S, (n : ℝ) * ‖v n‖ ^ (2 : ℕ) ≤ 0 := by
    rw [neg_nonpos]
    exact Finset.sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
  have hpos : (0 : ℝ) ≤ ∑ n ∈ S, ‖v n‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  linarith

/-- Every finite compression of the diagonal form satisfies the same one-sided inequality. -/
theorem negDiagonalCompression_le_normForm (d : ℕ) (v : Fin d → ℂ) :
    -∑ i : Fin d, ((i : ℕ) + 1 : ℝ) * ‖v i‖ ^ (2 : ℕ) ≤ ∑ i : Fin d, ‖v i‖ ^ (2 : ℕ) := by
  have hneg : -∑ i : Fin d, ((i : ℕ) + 1 : ℝ) * ‖v i‖ ^ (2 : ℕ) ≤ 0 := by
    rw [neg_nonpos]
    refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (sq_nonneg _)
    positivity
  have hpos : (0 : ℝ) ≤ ∑ i : Fin d, ‖v i‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The diagonal inner products of a bounded operator along a family of unit vectors are bounded by
its operator norm. -/
theorem norm_inner_apply_le_opNorm (K : H →L[ℂ] H) (x : H) (hx : ‖x‖ = 1) :
    ‖(inner ℂ (K x) x : ℂ)‖ ≤ ‖K‖ := by
  calc ‖(inner ℂ (K x) x : ℂ)‖ ≤ ‖K x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖K‖ * ‖x‖) * ‖x‖ := by
        gcongr
        exact K.le_opNorm x
    _ = ‖K‖ := by rw [hx]; ring

/-- **No bounded representer.**  No bounded operator has diagonal entries `-n` along a family of
unit vectors. -/
theorem not_exists_bounded_diagonal_neg_natCast (e : ℕ → H) (he : ∀ n, ‖e n‖ = 1) :
    ¬ ∃ K : H →L[ℂ] H, ∀ n : ℕ, (inner ℂ (K (e n)) (e n) : ℂ) = -(n : ℂ) := by
  rintro ⟨K, hK⟩
  obtain ⟨N, hN⟩ := exists_nat_gt ‖K‖
  have hbound := norm_inner_apply_le_opNorm K (e N) (he N)
  rw [hK N] at hbound
  rw [norm_neg, Complex.norm_natCast] at hbound
  linarith

end Abstract

/-- The sequence Hilbert space `ℓ²(ℕ, ℂ)`. -/
abbrev OneSidedEllTwo : Type := lp (fun _ : ℕ => ℂ) 2

/-- The `n`-th standard basis vector of `ℓ²(ℕ, ℂ)`. -/
def ellTwoBasis (n : ℕ) : OneSidedEllTwo := lp.single 2 n (1 : ℂ)

theorem norm_ellTwoBasis (n : ℕ) : ‖ellTwoBasis n‖ = 1 := by
  rw [ellTwoBasis, lp.norm_single (by norm_num), norm_one]

/-- **Concrete form.**  On `ℓ²(ℕ)` no bounded operator has the negative diagonal form of the card
as its quadratic form. -/
theorem not_exists_bounded_ellTwo_diagonal_neg_natCast :
    ¬ ∃ K : OneSidedEllTwo →L[ℂ] OneSidedEllTwo,
      ∀ n : ℕ, (inner ℂ (K (ellTwoBasis n)) (ellTwoBasis n) : ℂ) = -(n : ℂ) :=
  not_exists_bounded_diagonal_neg_natCast ellTwoBasis norm_ellTwoBasis

end RHTower
