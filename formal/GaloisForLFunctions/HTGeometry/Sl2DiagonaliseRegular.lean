import GaloisForLFunctions.HTGeometry.Sl2RegularElement

/-!
# Diagonalising a regular element of `sl₂`

A traceless `2 × 2` matrix of nonzero determinant has two distinct eigenvalues `±μ` with
`μ² = -det X`, so over an algebraically closed field it is conjugate to `μ h`.  The conjugator is
written down explicitly from the eigenvectors, so the statement is proved without any spectral
theory: `X P = P (μ h)` with `det P ≠ 0`.

This is step two of Cassidy's reduction, after `exists_det_ne_zero_of_mem_span` produces the regular
element.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {U : Type*} [Field U]

/-- A traceless `2 × 2` matrix in explicit form. -/
theorem eq_traceless_matrix {X : Matrix (Fin 2) (Fin 2) U} (htr : X.trace = 0) :
    X = !![X 0 0, X 0 1; X 1 0, -(X 0 0)] := by
  have h11 : X 1 1 = -(X 0 0) := by
    have := htr
    rw [Matrix.trace_fin_two] at this
    linear_combination this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h11]

/-- **Step two of Cassidy's reduction.**  A regular element of `sl₂` is conjugate to `μ h`. -/
theorem exists_conj_toral_of_det_ne_zero [IsAlgClosed U] (htwo : (2 : U) ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) U) (htr : X.trace = 0) (hdet : X.det ≠ 0) :
    ∃ (μ : U) (P : Matrix (Fin 2) (Fin 2) U), μ ≠ 0 ∧ P.det ≠ 0 ∧
      X * P = P * (μ • sl2H U) := by
  obtain ⟨a, b, c, hX⟩ : ∃ a b c : U, X = !![a, b; c, -a] :=
    ⟨X 0 0, X 0 1, X 1 0, eq_traceless_matrix htr⟩
  have hdet' : a * a + b * c ≠ 0 := by
    intro h0
    apply hdet
    rw [hX, Matrix.det_fin_two_of]
    linear_combination -h0
  by_cases hbz : b = 0
  · have haz : a ≠ 0 := by
      intro h0
      apply hdet'
      rw [h0, hbz]
      ring
    refine ⟨a, !![2 * a, 0; c, 1], haz, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simpa using mul_ne_zero htwo haz
    · rw [hX, hbz]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sl2H, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (a * a + b * c) (n := 2) (by norm_num)
    have hμ2 : μ * μ = a * a + b * c := by
      rw [← hμ]; ring
    have hμz : μ ≠ 0 := by
      intro h0
      apply hdet'
      rw [← hμ2, h0]
      ring
    refine ⟨μ, !![b, b; μ - a, -μ - a], hμz, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      have : b * (-μ - a) - b * (μ - a) = -(2 * (b * μ)) := by ring
      rw [this]
      simpa using mul_ne_zero htwo (mul_ne_zero hbz hμz)
    · have hbc : c * b = μ ^ 2 - a ^ 2 := by linear_combination -hμ2
      rw [hX]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sl2H, Matrix.mul_apply, Fin.sum_univ_two, hbc] <;> ring

end

end GaloisForLFunctions.HTGeometry
