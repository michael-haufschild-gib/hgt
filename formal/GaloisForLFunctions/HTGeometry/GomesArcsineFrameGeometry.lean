import GaloisForLFunctions.HTGeometry.GomesMomentFrameTransport
import GaloisForLFunctions.HTGeometry.GomesJacobiReconstruction
import GaloisForLFunctions.HTGeometry.ArcsineHankelPositiveDefinite

/-!
# Arcsine moment recurrences as internal frames

Applications of https://arxiv.org/abs/2607.24901 and
https://arxiv.org/abs/2404.10461 to the existing arcsine moment family.
Positivity is discharged by the corpus's closed moment theorem; no positivity
premise is added. The normalized central-binomial moments supply the arcsine family.
Results cover actual two-solution frame evolution, orientation, metric existence,
complex flux signs, and exact coefficient reconstruction between levels.
-/

open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- The actual arcsine recurrence has a strictly positive area character at every level. -/
theorem gomesArcsineFrame_recurOff_pos (n : ℕ) : 0 < recurOff normalizedCentralBinom n := by
  exact div_pos (normalizedCentralBinom_positiveMomentForm.pos_of_ne_zero _ (monicOrtho_ne_zero normalizedCentralBinom (n+1)))
    (normalizedCentralBinom_positiveMomentForm.pos_of_ne_zero _ (monicOrtho_ne_zero normalizedCentralBinom n))

/-- Both existing arcsine polynomial solutions advance by the same internal frame step. -/
theorem gomesArcsineFrame_advance (n : ℕ) (x : ℝ) :
    gomesMomentFrame normalizedCentralBinom (n+1) x =
      gomesJacobiStep (recurDiag normalizedCentralBinom n) (recurOff normalizedCentralBinom n) x * gomesMomentFrame normalizedCentralBinom n x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesMomentFrame,gomesJacobiStep,Matrix.mul_apply,Fin.sum_univ_two,
      monicOrtho_succ_succ_eval normalizedCentralBinom_positiveMomentForm,secondKind_succ_succ_eval] <;> ring

/-- The arcsine frame has an exact, spectrally constant, norm-ratio area transport law. -/
theorem gomesArcsineFrame_area (n : ℕ) (x : ℝ) :
    (gomesMomentFrame normalizedCentralBinom n x)ᵀ * gomesShearAreaMatrix ℝ * gomesMomentFrame normalizedCentralBinom n x =
      (-(momentInner normalizedCentralBinom (monicOrtho normalizedCentralBinom n) (monicOrtho normalizedCentralBinom n) /
        momentInner normalizedCentralBinom (monicOrtho normalizedCentralBinom 0) (monicOrtho normalizedCentralBinom 0))) • gomesShearAreaMatrix ℝ := by
  rw [gomesMomentFrame_area,momentWronskian_eq normalizedCentralBinom_positiveMomentForm,Polynomial.eval_C]

/-- The two-solution arcsine frame is everywhere nonsingular and reverses orientation. -/
theorem gomesArcsineFrame_det_neg (n : ℕ) (x : ℝ) :
    (gomesMomentFrame normalizedCentralBinom n x).det < 0 := by
  rw [gomesMomentFrame_det,momentWronskian_eq normalizedCentralBinom_positiveMomentForm,Polynomial.eval_C]
  exact neg_neg_of_pos (div_pos
    (normalizedCentralBinom_positiveMomentForm.pos_of_ne_zero _ (monicOrtho_ne_zero normalizedCentralBinom n))
    (normalizedCentralBinom_positiveMomentForm.pos_of_ne_zero _ (monicOrtho_ne_zero normalizedCentralBinom 0)))

/-- No positive Hermitian metric follows every spectral step of this arcsine recurrence. -/
theorem gomesArcsineFrame_no_common_positive_metric (n : ℕ) :
    ¬∃ H : Matrix (Fin 2) (Fin 2) ℂ, H.PosDef ∧ ∀ x : ℝ,
      (gomesJacobiComplexStep (recurDiag normalizedCentralBinom n) (recurOff normalizedCentralBinom n) x)ᴴ * H *
        gomesJacobiComplexStep (recurDiag normalizedCentralBinom n) (recurOff normalizedCentralBinom n) x =
        (recurOff normalizedCentralBinom n : ℂ) • H :=
  gomesJacobiComplexStep_no_common_positive_metric _ _

/-- The positive-metric region of the actual arcsine step is its exact elliptic interval. -/
theorem gomesArcsineFrame_positive_metric_iff (n : ℕ) (x : ℝ) :
    (∃ B : Matrix (Fin 2) (Fin 2) ℝ, B.PosDef ∧
      (gomesJacobiStep (recurDiag normalizedCentralBinom n) (recurOff normalizedCentralBinom n) x)ᵀ * B *
        gomesJacobiStep (recurDiag normalizedCentralBinom n) (recurOff normalizedCentralBinom n) x = recurOff normalizedCentralBinom n • B) ↔
      (x-recurDiag normalizedCentralBinom n)^(2 : ℕ) < 4*recurOff normalizedCentralBinom n :=
  gomesJacobiStep_exists_positive_metric_iff _ _ _

/-- The arcsine complex step's Hermitian defect detects exactly the closed upper half-plane. -/
theorem gomesArcsineFrame_flux_defect_nonneg (n : ℕ) (z : ℂ) :
    ((gomesJacobiComplexStep (recurDiag normalizedCentralBinom n) (recurOff normalizedCentralBinom n) z)ᴴ * gomesJacobiFlux *
      gomesJacobiComplexStep (recurDiag normalizedCentralBinom n) (recurOff normalizedCentralBinom n) z -
      (recurOff normalizedCentralBinom n : ℂ) • gomesJacobiFlux).PosSemidef ↔ 0 ≤ z.im :=
  gomesJacobiComplexStep_flux_defect_nonneg _ _ _

/-- Nonzero constant intertwiners between arcsine levels exist exactly when both coefficients match. -/
theorem gomesArcsineFrame_level_intertwiner_iff (m n : ℕ) :
    (∃ P : Matrix (Fin 2) (Fin 2) ℝ, P ≠ 0 ∧ ∀ x : ℝ,
      P * gomesJacobiStep (recurDiag normalizedCentralBinom m) (recurOff normalizedCentralBinom m) x =
        gomesJacobiStep (recurDiag normalizedCentralBinom n) (recurOff normalizedCentralBinom n) x * P) ↔
      recurDiag normalizedCentralBinom m = recurDiag normalizedCentralBinom n ∧ recurOff normalizedCentralBinom m = recurOff normalizedCentralBinom n :=
  gomesJacobiStep_nonzero_intertwiner_iff _ _ _ _

end GaloisForLFunctions.HTGeometry
