import GaloisForLFunctions.HTGeometry.GomesMomentFrameTransport
import GaloisForLFunctions.HTGeometry.GomesJacobiReconstruction
import GaloisForLFunctions.HTGeometry.PoleUnitGammaBase

/-!
# Gamma moment recurrences as internal frames

Applications of https://arxiv.org/abs/2607.24901 and
https://arxiv.org/abs/2404.10461 to the existing gamma moment family.
Positivity is discharged by the corpus's closed moment theorem; no positivity
premise is added. The Gamma shape is `exp r`, so every real parameter yields a positive shape.
Results cover actual two-solution frame evolution, orientation, metric existence,
complex flux signs, and exact coefficient reconstruction between levels.
-/

open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- The actual gamma recurrence has a strictly positive area character at every level. -/
theorem gomesGammaFrame_recurOff_pos (r : ℝ) (n : ℕ) : 0 < recurOff (gammaShapeMoment (Real.exp r)) n := by
  exact div_pos ((gammaShapeMoment_positiveMomentForm (Real.exp_pos r)).pos_of_ne_zero _ (monicOrtho_ne_zero (gammaShapeMoment (Real.exp r)) (n+1)))
    ((gammaShapeMoment_positiveMomentForm (Real.exp_pos r)).pos_of_ne_zero _ (monicOrtho_ne_zero (gammaShapeMoment (Real.exp r)) n))

/-- Both existing gamma polynomial solutions advance by the same internal frame step. -/
theorem gomesGammaFrame_advance (r : ℝ) (n : ℕ) (x : ℝ) :
    gomesMomentFrame (gammaShapeMoment (Real.exp r)) (n+1) x =
      gomesJacobiStep (recurDiag (gammaShapeMoment (Real.exp r)) n) (recurOff (gammaShapeMoment (Real.exp r)) n) x * gomesMomentFrame (gammaShapeMoment (Real.exp r)) n x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesMomentFrame,gomesJacobiStep,Matrix.mul_apply,Fin.sum_univ_two,
      monicOrtho_succ_succ_eval (gammaShapeMoment_positiveMomentForm (Real.exp_pos r)),secondKind_succ_succ_eval] <;> ring

/-- The gamma frame has an exact, spectrally constant, norm-ratio area transport law. -/
theorem gomesGammaFrame_area (r : ℝ) (n : ℕ) (x : ℝ) :
    (gomesMomentFrame (gammaShapeMoment (Real.exp r)) n x)ᵀ * gomesShearAreaMatrix ℝ * gomesMomentFrame (gammaShapeMoment (Real.exp r)) n x =
      (-(momentInner (gammaShapeMoment (Real.exp r)) (monicOrtho (gammaShapeMoment (Real.exp r)) n) (monicOrtho (gammaShapeMoment (Real.exp r)) n) /
        momentInner (gammaShapeMoment (Real.exp r)) (monicOrtho (gammaShapeMoment (Real.exp r)) 0) (monicOrtho (gammaShapeMoment (Real.exp r)) 0))) • gomesShearAreaMatrix ℝ := by
  rw [gomesMomentFrame_area,momentWronskian_eq (gammaShapeMoment_positiveMomentForm (Real.exp_pos r)),Polynomial.eval_C]

/-- The two-solution gamma frame is everywhere nonsingular and reverses orientation. -/
theorem gomesGammaFrame_det_neg (r : ℝ) (n : ℕ) (x : ℝ) :
    (gomesMomentFrame (gammaShapeMoment (Real.exp r)) n x).det < 0 := by
  rw [gomesMomentFrame_det,momentWronskian_eq (gammaShapeMoment_positiveMomentForm (Real.exp_pos r)),Polynomial.eval_C]
  exact neg_neg_of_pos (div_pos
    ((gammaShapeMoment_positiveMomentForm (Real.exp_pos r)).pos_of_ne_zero _ (monicOrtho_ne_zero (gammaShapeMoment (Real.exp r)) n))
    ((gammaShapeMoment_positiveMomentForm (Real.exp_pos r)).pos_of_ne_zero _ (monicOrtho_ne_zero (gammaShapeMoment (Real.exp r)) 0)))

/-- No positive Hermitian metric follows every spectral step of this gamma recurrence. -/
theorem gomesGammaFrame_no_common_positive_metric (r : ℝ) (n : ℕ) :
    ¬∃ H : Matrix (Fin 2) (Fin 2) ℂ, H.PosDef ∧ ∀ x : ℝ,
      (gomesJacobiComplexStep (recurDiag (gammaShapeMoment (Real.exp r)) n) (recurOff (gammaShapeMoment (Real.exp r)) n) x)ᴴ * H *
        gomesJacobiComplexStep (recurDiag (gammaShapeMoment (Real.exp r)) n) (recurOff (gammaShapeMoment (Real.exp r)) n) x =
        (recurOff (gammaShapeMoment (Real.exp r)) n : ℂ) • H :=
  gomesJacobiComplexStep_no_common_positive_metric _ _

/-- The positive-metric region of the actual gamma step is its exact elliptic interval. -/
theorem gomesGammaFrame_positive_metric_iff (r : ℝ) (n : ℕ) (x : ℝ) :
    (∃ B : Matrix (Fin 2) (Fin 2) ℝ, B.PosDef ∧
      (gomesJacobiStep (recurDiag (gammaShapeMoment (Real.exp r)) n) (recurOff (gammaShapeMoment (Real.exp r)) n) x)ᵀ * B *
        gomesJacobiStep (recurDiag (gammaShapeMoment (Real.exp r)) n) (recurOff (gammaShapeMoment (Real.exp r)) n) x = recurOff (gammaShapeMoment (Real.exp r)) n • B) ↔
      (x-recurDiag (gammaShapeMoment (Real.exp r)) n)^2 < 4*recurOff (gammaShapeMoment (Real.exp r)) n :=
  gomesJacobiStep_exists_positive_metric_iff _ _ _

/-- The gamma complex step's Hermitian defect detects exactly the closed upper half-plane. -/
theorem gomesGammaFrame_flux_defect_nonneg (r : ℝ) (n : ℕ) (z : ℂ) :
    ((gomesJacobiComplexStep (recurDiag (gammaShapeMoment (Real.exp r)) n) (recurOff (gammaShapeMoment (Real.exp r)) n) z)ᴴ * gomesJacobiFlux *
      gomesJacobiComplexStep (recurDiag (gammaShapeMoment (Real.exp r)) n) (recurOff (gammaShapeMoment (Real.exp r)) n) z -
      (recurOff (gammaShapeMoment (Real.exp r)) n : ℂ) • gomesJacobiFlux).PosSemidef ↔ 0 ≤ z.im :=
  gomesJacobiComplexStep_flux_defect_nonneg _ _ _

/-- Nonzero constant intertwiners between gamma levels exist exactly when both coefficients match. -/
theorem gomesGammaFrame_level_intertwiner_iff (r : ℝ) (m n : ℕ) :
    (∃ P : Matrix (Fin 2) (Fin 2) ℝ, P ≠ 0 ∧ ∀ x : ℝ,
      P * gomesJacobiStep (recurDiag (gammaShapeMoment (Real.exp r)) m) (recurOff (gammaShapeMoment (Real.exp r)) m) x =
        gomesJacobiStep (recurDiag (gammaShapeMoment (Real.exp r)) n) (recurOff (gammaShapeMoment (Real.exp r)) n) x * P) ↔
      recurDiag (gammaShapeMoment (Real.exp r)) m = recurDiag (gammaShapeMoment (Real.exp r)) n ∧ recurOff (gammaShapeMoment (Real.exp r)) m = recurOff (gammaShapeMoment (Real.exp r)) n :=
  gomesJacobiStep_nonzero_intertwiner_iff _ _ _ _

end GaloisForLFunctions.HTGeometry
