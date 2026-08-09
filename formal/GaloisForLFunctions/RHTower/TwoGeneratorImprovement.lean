import GaloisForLFunctions.RHTower.HalfQuarterGram

/-!
# Two generators strictly beat one

`SingleGeneratorUseless` shows each generator alone contributes `O((log m)²/m)`, and
`UniformDistanceBound` freezes the best single-generator bound.  Whether *combining* generators gains anything
is a different question, and the `{2,4}` Gram matrix answers it concretely.

With the rational coefficient pair `c = (2, 1)` on the moduli `(2, 4)` the quadratic form of
`bdDist_sq_le_quadratic` evaluates, using `bdGram_half`, `bdGram_half_quarter` and `bdGram_quarter`, to

**`bdDist_sq_le_two_generator` — `d² ≤ 1 − (3/8)·log 2 − (5/32)·π` for the family `{1/2, 1/4}`,**

and that is strictly smaller than the single-generator value `1 − log 2` of `BaezDuarteHalfBound`:

**`two_generator_lt_single` — `1 − (3/8)log 2 − (5/32)π < 1 − log 2`.**

So the collective effect is real and quantified at the smallest possible scale: the pair does better than either
member, with no optimisation — `c = (2,1)` is chosen for arithmetic convenience, not optimality, and the optimal
pair does better still.  This is the first positive evidence in the development that combining moduli gains
something, complementing the negative result that no single modulus can.
-/

open Finset

noncomputable section

namespace RHTower

/-- **A two-generator bound with rational coefficients.** -/
theorem bdDist_sq_le_two_generator :
    bdDist (![1 / (2 : ℝ), 1 / (4 : ℝ)]) ^ 2
      ≤ 1 - 3 * Real.log 2 / 8 - 5 * Real.pi / 32 := by
  have hθ : ∀ i : Fin 2, 0 < (![1 / (2 : ℝ), 1 / (4 : ℝ)]) i
      ∧ (![1 / (2 : ℝ), 1 / (4 : ℝ)]) i ≤ 1 := by
    intro i
    fin_cases i <;> norm_num
  have h := bdDist_sq_le_quadratic
    (![1 / (2 : ℝ), 1 / (4 : ℝ)]) hθ
    (![(2 : ℝ), 1])
  refine le_trans h ?_
  have hlog2 : Real.log (1 / (2 : ℝ)) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hlog4 : Real.log (1 / (4 : ℝ)) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = (2 : ℝ) ^ 2 from by norm_num, Real.log_pow]
    push_cast
    ring
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hlog2, hlog4, bdGram_half, bdGram_quarter, bdGram_half_quarter,
    bdGram_symm (1 / (4 : ℝ)) (1 / (2 : ℝ)), bdGram_half_quarter]
  ring_nf
  exact le_rfl

/-- The two-generator value is strictly below the single-generator value `1 − log 2`. -/
theorem two_generator_lt_single :
    1 - 3 * Real.log 2 / 8 - 5 * Real.pi / 32 < 1 - Real.log 2 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h3 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  nlinarith [h2, h2', h3]

end RHTower

end
