import GaloisForLFunctions.RHTower.FiniteCliqueCollectiveGap

/-!
# Diagonal reserves with the collective correction retained

Uniform diagonal and interaction bounds give a quantitative reserve for a
finite symmetric form. The clique correction remains available on top of it.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteSignedSeparateLower_uniform_gap (M : ι → ι → ℝ) (d e : ℝ)
    (he : 0 ≤ e) (hd : ∀ i, d ≤ M i i)
    (hoff : ∀ i j, i ≠ j → |M i j| ≤ e) (x : ι → ℝ) :
    (d - Fintype.card ι * e) * (∑ i, x i ^ 2) ≤ finiteSignedSeparateLower M x := by
  have hrow (i : ι) : (∑ j, |finiteSignedOffDiagonal M i j|) ≤ Fintype.card ι * e := by
    calc
      _ ≤ ∑ _j : ι, e := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · simpa only [finiteSignedOffDiagonal, hij, ite_true, abs_zero] using he
        · simpa only [finiteSignedOffDiagonal, if_neg hij] using hoff i j hij
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold finiteSignedSeparateLower
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (sub_le_sub (hd i) (hrow i)) (sq_nonneg _)

theorem finiteSignedClique_uniform_gap (M : ι → ι → ℝ)
    (hsym : ∀ i j, M i j = M j i) (d e : ℝ)
    (he : 0 ≤ e) (hd : ∀ i, d ≤ M i i)
    (hoff : ∀ i j, i ≠ j → |M i j| ≤ e) (x : ι → ℝ) :
    (d - Fintype.card ι * e) * (∑ i, x i ^ 2) + finiteSignedCliqueCorrection M x ≤
      finiteSignedQuadratic M x :=
  (add_le_add (finiteSignedSeparateLower_uniform_gap M d e he hd hoff x) le_rfl).trans
    (finiteSignedClique_lower M hsym x)

end RHTower
