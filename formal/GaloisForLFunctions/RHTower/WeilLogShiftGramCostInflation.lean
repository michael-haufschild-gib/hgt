import GaloisForLFunctions.RHTower.WeilLogShiftGramImage

/-! Signed duplication preserves actual Gram forms while inflating their tail cost. -/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

theorem finiteWeilGramTailCost_ofFinite (B : ℝ) {ι : Type} [Fintype ι]
    (x u : ι → ℝ) (a : NNReal) :
    finiteWeilGramTailCost B (finiteWeilGramTestOfFinite x u a) =
      (a : ℝ) * ∑ i, ∑ j, |u i * u j| * (B * Real.exp (2 * |x j - x i|)) := by
  simp only [finiteWeilGramTestOfFinite, finiteWeilGramTailCost, Function.comp_apply]
  congr 1
  calc
    (∑ i : Fin (Fintype.card ι), ∑ j : Fin (Fintype.card ι),
        |u ((Fintype.equivFin ι).symm i) * u ((Fintype.equivFin ι).symm j)| *
          (B * Real.exp (2 * |x ((Fintype.equivFin ι).symm j) -
            x ((Fintype.equivFin ι).symm i)|))) =
        ∑ i : Fin (Fintype.card ι), ∑ j : ι,
          |u ((Fintype.equivFin ι).symm i) * u j| *
            (B * Real.exp (2 * |x j - x ((Fintype.equivFin ι).symm i)|)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Fintype.equivFin ι).symm.sum_comp (fun j : ι =>
        |u ((Fintype.equivFin ι).symm i) * u j| *
          (B * Real.exp (2 * |x j - x ((Fintype.equivFin ι).symm i)|)))
    _ = ∑ i : ι, ∑ j : ι, |u i * u j| * (B * Real.exp (2 * |x j - x i|)) :=
      (Fintype.equivFin ι).symm.sum_comp (fun i : ι =>
        ∑ j : ι, |u i * u j| * (B * Real.exp (2 * |x j - x i|)))

/-- Each node is duplicated with signed amplitude coefficients `1+r` and `-r`. -/
def finiteWeilGramSignedDuplicate (r : NNReal) : FiniteWeilGramTest → FiniteWeilGramTest
  | ⟨N, x, u, a⟩ => finiteWeilGramTestOfFinite (Sum.elim x x)
      (Sum.elim (fun i : Fin N => (1 + (r : ℝ)) * u i)
        (fun i : Fin N => -(r : ℝ) * u i)) a

theorem finiteWeilGramCoefficientVector_signedDuplicate (s : Finset ℕ) (r : NNReal)
    (w : FiniteWeilGramTest) :
    finiteWeilGramCoefficientVector s (finiteWeilGramSignedDuplicate r w) =
      finiteWeilGramCoefficientVector s w := by
  rcases w with ⟨N, x, u, a⟩
  funext k
  dsimp only [finiteWeilGramSignedDuplicate]
  rw [finiteWeilGramCoefficientVector_ofFinite, finiteWeilGramCoefficientVector_apply]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finiteWeilGramForm_signedDuplicate (s : Finset ℕ) (r : NNReal)
    (w : FiniteWeilGramTest) :
    finiteWeilGramForm s (finiteWeilGramSignedDuplicate r w) = finiteWeilGramForm s w := by
  apply LinearMap.ext
  intro c
  simp only [finiteWeilGramCoefficientVector_pairing,
    finiteWeilGramCoefficientVector_signedDuplicate]

/-- The same duplication scales every tail-cost normalization, without using
any property of the arithmetic kernel beyond coincident nodes. -/
theorem finiteWeilGramTailCost_signedDuplicate (B : ℝ) (r : NNReal)
    (w : FiniteWeilGramTest) :
    finiteWeilGramTailCost B (finiteWeilGramSignedDuplicate r w) =
      (1 + 2 * (r : ℝ)) ^ 2 * finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramSignedDuplicate]
  rw [finiteWeilGramTailCost_ofFinite]
  dsimp only [finiteWeilGramTailCost]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    ← Finset.sum_add_distrib]
  rw [_root_.mul_left_comm ((1 + 2 * (r : ℝ)) ^ 2) (a : ℝ)]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hr : 0 ≤ 1 + (r : ℝ) := by positivity
  simp only [abs_mul, abs_neg, abs_of_nonneg (NNReal.coe_nonneg r), abs_of_nonneg hr]
  ring

/-- Every larger positive unit cost can be realized without changing the Gram
functional on any coefficient support. -/
theorem exists_finiteWeilGram_cost_inflation (w : FiniteWeilGramTest) (C : ℝ)
    (hk : 0 < finiteWeilGramTailCost 1 w) (hC : finiteWeilGramTailCost 1 w ≤ C) :
    ∃ z : FiniteWeilGramTest,
      (∀ s : Finset ℕ, finiteWeilGramForm s z = finiteWeilGramForm s w) ∧
      finiteWeilGramTailCost 1 z = C := by
  have hratio : 1 ≤ C / finiteWeilGramTailCost 1 w :=
    (le_div_iff₀ hk).mpr (by simpa only [one_mul] using hC)
  have hroot : 1 ≤ Real.sqrt (C / finiteWeilGramTailCost 1 w) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hratio
  let r : NNReal := NNReal.mk ((Real.sqrt (C / finiteWeilGramTailCost 1 w) - 1) / 2)
    (by linarith only [hroot])
  refine ⟨finiteWeilGramSignedDuplicate r w,
    fun s => finiteWeilGramForm_signedDuplicate s r w, ?_⟩
  have hr : 1 + 2 * (r : ℝ) = Real.sqrt (C / finiteWeilGramTailCost 1 w) := by
    simp only [r, NNReal.coe_mk]
    ring
  rw [finiteWeilGramTailCost_signedDuplicate, hr,
    Real.sq_sqrt (by linarith only [hratio]), div_mul_cancel₀ _ hk.ne']

end RHTower
