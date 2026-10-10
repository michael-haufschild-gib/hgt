import GaloisForLFunctions.RHTower.WeilLogShiftGramCostInflation

/-! Supremum amplitude control bounds actual native cost on arbitrary fixed nodes. -/

open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilGramTailCost_one_nonneg (w : FiniteWeilGramTest) :
    0 ≤ finiteWeilGramTailCost 1 w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramTailCost]
  positivity

theorem finiteWeilGramTailCost_amplitude_bound {ι J : Type} [Fintype ι] [Fintype J]
    (x u : ι → ℝ) (q : ι → J) (t : J → ℝ) :
    finiteWeilGramTailCost 1 (finiteWeilGramTestOfFinite x (fun i => t (q i) * u i) 1) ≤
      ‖t‖ ^ 2 * finiteWeilGramTailCost 1 (finiteWeilGramTestOfFinite x u 1) := by
  rw [finiteWeilGramTailCost_ofFinite, finiteWeilGramTailCost_ofFinite]
  simp only [NNReal.coe_one, one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hi : |t (q i)| ≤ ‖t‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm t (q i)
  have hj : |t (q j)| ≤ ‖t‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm t (q j)
  have hmul : |t (q i)| * |t (q j)| ≤ ‖t‖ ^ 2 := by
    have h := mul_le_mul hi hj (abs_nonneg (t (q j))) (norm_nonneg t)
    nlinarith only [h]
  calc
    |t (q i) * u i * (t (q j) * u j)| * Real.exp (2 * |x j - x i|) =
        (|t (q i)| * |t (q j)|) * (|u i * u j| * Real.exp (2 * |x j - x i|)) := by
      simp only [abs_mul]
      ring
    _ ≤ ‖t‖ ^ 2 * (|u i * u j| * Real.exp (2 * |x j - x i|)) :=
      mul_le_mul_of_nonneg_right hmul (by positivity)

end RHTower
