import GaloisForLFunctions.HTGeometry.ProductBlockTransfer

/-!
# The checkerboard block

The eigenspace of a checkerboard block of a `2 × 2` product grid is spanned by the two diagonal
frame vectors.  A decomposable tensor lying in it has a coordinate array which is an outer product
vanishing off the diagonal, and such an array is concentrated at a single diagonal point: if
`x₀ y₁ = 0` and `x₁ y₀ = 0` with `x` and `y` nonzero, then one common index carries both.

Consequently a nonzero decomposable tensor in a checkerboard eigenspace is a multiple of one of the
two diagonal frame vectors, so its factors lie on the frame's own axes.  This is the last of the
three `2 + 2` sub-cases.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- **Checkerboard support.**  An outer product on a `2 × 2` grid vanishing off the diagonal is
concentrated at a single diagonal point. -/
theorem segreTensor_concentrated_of_offDiagonal_zero {x y : Fin 2 → K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h01 : criticalHorizonSegreTensor x y 0 1 = 0)
    (h10 : criticalHorizonSegreTensor x y 1 0 = 0) :
    ∃ i : Fin 2, (∃ c : K, c ≠ 0 ∧ x = c • indexIndicator i) ∧
      (∃ d : K, d ≠ 0 ∧ y = d • indexIndicator i) := by
  simp only [criticalHorizonSegreTensor] at h01 h10
  by_cases h0 : x 0 = 0
  · have hx1 : x 1 ≠ 0 := by
      intro h1
      refine hx ?_
      funext j
      fin_cases j <;> simp [h0, h1]
    have hy0 : y 0 = 0 := by
      rcases mul_eq_zero.mp h10 with h | h
      · exact absurd h hx1
      · exact h
    have hy1 : y 1 ≠ 0 := by
      intro h1
      refine hy ?_
      funext j
      fin_cases j <;> simp [hy0, h1]
    refine ⟨1, ⟨x 1, hx1, ?_⟩, ⟨y 1, hy1, ?_⟩⟩
    · funext j
      fin_cases j <;> simp [indexIndicator, h0]
    · funext j
      fin_cases j <;> simp [indexIndicator, hy0]
  · have hy1 : y 1 = 0 := by
      rcases mul_eq_zero.mp h01 with h | h
      · exact absurd h h0
      · exact h
    have hy0 : y 0 ≠ 0 := by
      intro h1
      refine hy ?_
      funext j
      fin_cases j <;> simp [h1, hy1]
    have hx1 : x 1 = 0 := by
      rcases mul_eq_zero.mp h10 with h | h
      · exact h
      · exact absurd h hy0
    refine ⟨0, ⟨x 0, h0, ?_⟩, ⟨y 0, hy0, ?_⟩⟩
    · funext j
      fin_cases j <;> simp [indexIndicator, hx1]
    · funext j
      fin_cases j <;> simp [indexIndicator, hy1]

/-- **Checkerboard case.**  A nonzero decomposable tensor whose expansion in a product frame has
vanishing off-diagonal coefficients has both factors on the frame's own axes, at a common index. -/
theorem checkerboardFactors_eq_smul {a b : Fin 2 → (Fin 2 → K)} {x y : Fin 2 → K}
    (hx : x ≠ 0) (hy : y ≠ 0) (h01 : x 0 * y 1 = 0) (h10 : x 1 * y 0 = 0) :
    ∃ i : Fin 2, (∃ c : K, c ≠ 0 ∧ (∑ k, x k • a k) = c • a i) ∧
      (∃ d : K, d ≠ 0 ∧ (∑ l, y l • b l) = d • b i) := by
  obtain ⟨i, ⟨c, hc, hxc⟩, ⟨d, hd, hyd⟩⟩ :=
    segreTensor_concentrated_of_offDiagonal_zero hx hy h01 h10
  refine ⟨i, ⟨c, hc, ?_⟩, ⟨d, hd, ?_⟩⟩
  · rw [Fin.sum_univ_two, hxc]
    fin_cases i <;> simp [indexIndicator]
  · rw [Fin.sum_univ_two, hyd]
    fin_cases i <;> simp [indexIndicator]

end GaloisForLFunctions.HTGeometry
