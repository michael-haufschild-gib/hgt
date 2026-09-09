import GaloisForLFunctions.HTGeometry.GomesMomentFrameTransport
import GaloisForLFunctions.HTGeometry.GomesJacobiReconstruction
import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircle

/-!
# Closed free-Fock frame geometry from arbitrary matrix data

Application of invariant tensors, joint kernels, and internal frames from
https://arxiv.org/abs/2607.24901, https://arxiv.org/abs/2509.25276, and
https://arxiv.org/abs/2404.10461 to the actual free-Fock moment construction.
Arbitrary finite matrix data are completed by adjoining the identity and taking
Hermitian parts. This changes the input family explicitly and discharges every
positivity condition internally. The resulting moments inherit exact frame
transport, orientation, metric boundaries, flux signs, and coefficient rigidity.
-/

open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Complete arbitrary matrix data by adjoining the identity and taking Hermitian parts.
The identity guarantees that no nonzero internal vector is invisible to every generator. -/
def gomesCompletedFockGenerators {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Option (Fin k) → Matrix (Fin (d+1)) (Fin (d+1)) ℂ
  | none => 1
  | some i => B i + (B i)ᴴ

/-- The completed generators are self-adjoint for every input matrix family. -/
theorem gomesCompletedFockGenerators_hermitian {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (i : Option (Fin k)) :
    (gomesCompletedFockGenerators B i)ᴴ = gomesCompletedFockGenerators B i := by
  cases i <;> simp [gomesCompletedFockGenerators,add_comm]

/-- The identity component makes the completed family jointly faithful on internal vectors. -/
theorem gomesCompletedFockGenerators_commonKernel {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    HasTrivialCommonKernel (gomesCompletedFockGenerators B) := by
  intro x hx
  ext i
  have h := hx none i
  simpa [gomesCompletedFockGenerators,Matrix.one_apply] using h

/-- Actual free-Fock trace moments of the completed matrix generator family. -/
def gomesCompletedFockMoment {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) : ℕ → ℝ :=
  freeFockTraceMoment (gomesCompletedFockGenerators B)

/-- The existing Fock energy theorem closes positivity for arbitrary input matrix data. -/
theorem gomesCompletedFockMoment_positiveMomentForm {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    PositiveMomentForm (gomesCompletedFockMoment B) :=
  freeFockTraceMoment_positiveMomentForm _ (gomesCompletedFockGenerators_hermitian B)
    (gomesCompletedFockGenerators_commonKernel B)


/-- The actual completed free-Fock recurrence has a strictly positive area character at every level. -/
theorem gomesCompletedFockFrame_recurOff_pos {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (n : ℕ) : 0 < recurOff (gomesCompletedFockMoment B) n := by
  exact div_pos ((gomesCompletedFockMoment_positiveMomentForm B).pos_of_ne_zero _ (monicOrtho_ne_zero (gomesCompletedFockMoment B) (n+1)))
    ((gomesCompletedFockMoment_positiveMomentForm B).pos_of_ne_zero _ (monicOrtho_ne_zero (gomesCompletedFockMoment B) n))

/-- Both existing completed free-Fock polynomial solutions advance by the same internal frame step. -/
theorem gomesCompletedFockFrame_advance {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (n : ℕ) (x : ℝ) :
    gomesMomentFrame (gomesCompletedFockMoment B) (n+1) x =
      gomesJacobiStep (recurDiag (gomesCompletedFockMoment B) n) (recurOff (gomesCompletedFockMoment B) n) x * gomesMomentFrame (gomesCompletedFockMoment B) n x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesMomentFrame,gomesJacobiStep,Matrix.mul_apply,Fin.sum_univ_two,
      monicOrtho_succ_succ_eval (gomesCompletedFockMoment_positiveMomentForm B),secondKind_succ_succ_eval] <;> ring

/-- The completed free-Fock frame has an exact, spectrally constant, norm-ratio area transport law. -/
theorem gomesCompletedFockFrame_area {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (n : ℕ) (x : ℝ) :
    (gomesMomentFrame (gomesCompletedFockMoment B) n x)ᵀ * gomesShearAreaMatrix ℝ * gomesMomentFrame (gomesCompletedFockMoment B) n x =
      (-(momentInner (gomesCompletedFockMoment B) (monicOrtho (gomesCompletedFockMoment B) n) (monicOrtho (gomesCompletedFockMoment B) n) /
        momentInner (gomesCompletedFockMoment B) (monicOrtho (gomesCompletedFockMoment B) 0) (monicOrtho (gomesCompletedFockMoment B) 0))) • gomesShearAreaMatrix ℝ := by
  rw [gomesMomentFrame_area,momentWronskian_eq (gomesCompletedFockMoment_positiveMomentForm B),Polynomial.eval_C]

/-- The two-solution completed free-Fock frame is everywhere nonsingular and reverses orientation. -/
theorem gomesCompletedFockFrame_det_neg {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (n : ℕ) (x : ℝ) :
    (gomesMomentFrame (gomesCompletedFockMoment B) n x).det < 0 := by
  rw [gomesMomentFrame_det,momentWronskian_eq (gomesCompletedFockMoment_positiveMomentForm B),Polynomial.eval_C]
  exact neg_neg_of_pos (div_pos
    ((gomesCompletedFockMoment_positiveMomentForm B).pos_of_ne_zero _ (monicOrtho_ne_zero (gomesCompletedFockMoment B) n))
    ((gomesCompletedFockMoment_positiveMomentForm B).pos_of_ne_zero _ (monicOrtho_ne_zero (gomesCompletedFockMoment B) 0)))

/-- No positive Hermitian metric follows every spectral step of this completed free-Fock recurrence. -/
theorem gomesCompletedFockFrame_no_common_positive_metric {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (n : ℕ) :
    ¬∃ H : Matrix (Fin 2) (Fin 2) ℂ, H.PosDef ∧ ∀ x : ℝ,
      (gomesJacobiComplexStep (recurDiag (gomesCompletedFockMoment B) n) (recurOff (gomesCompletedFockMoment B) n) x)ᴴ * H *
        gomesJacobiComplexStep (recurDiag (gomesCompletedFockMoment B) n) (recurOff (gomesCompletedFockMoment B) n) x =
        (recurOff (gomesCompletedFockMoment B) n : ℂ) • H :=
  gomesJacobiComplexStep_no_common_positive_metric _ _

/-- The positive-metric region of the actual completed free-Fock step is its exact elliptic interval. -/
theorem gomesCompletedFockFrame_positive_metric_iff {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (n : ℕ) (x : ℝ) :
    (∃ M : Matrix (Fin 2) (Fin 2) ℝ, M.PosDef ∧
      (gomesJacobiStep (recurDiag (gomesCompletedFockMoment B) n) (recurOff (gomesCompletedFockMoment B) n) x)ᵀ * M *
        gomesJacobiStep (recurDiag (gomesCompletedFockMoment B) n) (recurOff (gomesCompletedFockMoment B) n) x = recurOff (gomesCompletedFockMoment B) n • M) ↔
      (x-recurDiag (gomesCompletedFockMoment B) n)^2 < 4*recurOff (gomesCompletedFockMoment B) n :=
  gomesJacobiStep_exists_positive_metric_iff _ _ _

/-- The completed free-Fock complex step's Hermitian defect detects exactly the closed upper half-plane. -/
theorem gomesCompletedFockFrame_flux_defect_nonneg {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (n : ℕ) (z : ℂ) :
    ((gomesJacobiComplexStep (recurDiag (gomesCompletedFockMoment B) n) (recurOff (gomesCompletedFockMoment B) n) z)ᴴ * gomesJacobiFlux *
      gomesJacobiComplexStep (recurDiag (gomesCompletedFockMoment B) n) (recurOff (gomesCompletedFockMoment B) n) z -
      (recurOff (gomesCompletedFockMoment B) n : ℂ) • gomesJacobiFlux).PosSemidef ↔ 0 ≤ z.im :=
  gomesJacobiComplexStep_flux_defect_nonneg _ _ _

/-- Nonzero constant intertwiners between completed free-Fock levels exist exactly when both coefficients match. -/
theorem gomesCompletedFockFrame_level_intertwiner_iff {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (m n : ℕ) :
    (∃ P : Matrix (Fin 2) (Fin 2) ℝ, P ≠ 0 ∧ ∀ x : ℝ,
      P * gomesJacobiStep (recurDiag (gomesCompletedFockMoment B) m) (recurOff (gomesCompletedFockMoment B) m) x =
        gomesJacobiStep (recurDiag (gomesCompletedFockMoment B) n) (recurOff (gomesCompletedFockMoment B) n) x * P) ↔
      recurDiag (gomesCompletedFockMoment B) m = recurDiag (gomesCompletedFockMoment B) n ∧ recurOff (gomesCompletedFockMoment B) m = recurOff (gomesCompletedFockMoment B) n :=
  gomesJacobiStep_nonzero_intertwiner_iff _ _ _ _

end GaloisForLFunctions.HTGeometry
