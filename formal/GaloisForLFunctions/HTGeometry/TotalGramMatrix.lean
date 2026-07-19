import GaloisForLFunctions.HTGeometry.MeasureGramMatrix

/-!
# The total scaled Gram matrix

The Pick Gram of a chamber member is the atomic part plus the measure part.  Its deviation from the
diagonal of coefficients splits accordingly, so the entrywise estimates of the two parts combine by
the triangle inequality.

Both deviations vanish with the height, so the total converges entrywise to the diagonal of
coefficients — the hypothesis of the eventual negative definiteness criterion.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Matrix

noncomputable section

/-- The total scaled Pick Gram at the nodes above the atoms. -/
def totalGram {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ) (y : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  atomicGram a c y + measureGram ν a y

@[simp]
theorem totalGram_apply {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ) (y : ℝ) (l m : Fin d) :
    totalGram ν a c y l m = atomicGram a c y l m + measureGram ν a y l m := rfl

/-- **The deviation from the diagonal splits into the two parts.** -/
theorem totalGram_sub_diagonal {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ) (y : ℝ)
    (l m : Fin d) :
    totalGram ν a c y l m - (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)) l m
      = (atomicGram a c y l m - (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)) l m)
        + measureGram ν a y l m := by
  rw [totalGram_apply]
  ring

/-- **The entrywise deviation is bounded by the two parts separately.** -/
theorem norm_totalGram_sub_diagonal_le {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ) (y : ℝ)
    (l m : Fin d) :
    ‖totalGram ν a c y l m - (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)) l m‖
      ≤ ‖atomicGram a c y l m - (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)) l m‖
        + ‖measureGram ν a y l m‖ := by
  rw [totalGram_sub_diagonal]
  exact norm_add_le _ _

/-- On the diagonal the reference matrix is the coefficient itself. -/
@[simp]
theorem diagonal_apply_self {d : ℕ} (c : Fin d → ℝ) (l : Fin d) :
    (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)) l l = ((c l : ℝ) : ℂ) :=
  Matrix.diagonal_apply_eq _ l

/-- Off the diagonal the reference matrix vanishes, so the deviation is the entry itself. -/
@[simp]
theorem diagonal_apply_ne {d : ℕ} (c : Fin d → ℝ) {l m : Fin d} (h : l ≠ m) :
    (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)) l m = 0 :=
  Matrix.diagonal_apply_ne _ h

end

end GaloisForLFunctions.HTGeometry
