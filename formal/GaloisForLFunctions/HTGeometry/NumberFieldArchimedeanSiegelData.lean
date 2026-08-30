import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanSiegelReduction
import GaloisForLFunctions.HTGeometry.ComplexJacobiLeadingMinors

/-!
# Real and complex Siegel views of number-field Jacobi data

Simultaneous number-field Jacobi coordinates induce the existing real Jacobi data at every real
place and the Hermitian Jacobi data at every complex place.  Reality of every complex diagonal and
both local form identities are derived from the original positive decomposition.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Real local Jacobi view of simultaneous archimedean data. -/
def NumberFieldArchimedeanJacobiData.realJacobiData
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (w : {w : InfinitePlace K // w.IsReal}) : JacobiData n where
  U := J.realU w
  d := J.realD w
  pos := J.realPos w
  upper := J.realUpper w
  unit := J.realUnit w

omit [NumberField K] in
/-- The real local Jacobi view reconstructs the original real-place form. -/
theorem NumberFieldArchimedeanJacobiData.realJacobiData_form
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (J.realJacobiData w).form = (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) := by
  exact (J.realForm w).symm

omit [NumberField K] in
/-- Complex local Jacobi view with its positive diagonal represented over `ℝ`. -/
def NumberFieldArchimedeanJacobiData.complexJacobiData
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (w : {w : InfinitePlace K // w.IsComplex}) : ComplexJacobiData n where
  U := J.complexU w
  d := fun i => (J.complexD w i).re
  pos := fun i => (Complex.lt_def.1 (J.complexPos w i)).1
  upper := J.complexUpper w
  unit := J.complexUnit w

omit [NumberField K] in
/-- A positive complex Jacobi diagonal entry equals its real-part embedding. -/
theorem NumberFieldArchimedeanJacobiData.complexD_eq_ofReal_re
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (w : {w : InfinitePlace K // w.IsComplex}) (i : Fin n) :
    J.complexD w i = ((J.complexD w i).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using (Complex.lt_def.1 (J.complexPos w i)).2.symm

omit [NumberField K] in
/-- The complex local Jacobi view reconstructs the original complex-place form. -/
theorem NumberFieldArchimedeanJacobiData.complexJacobiData_form
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (J.complexJacobiData w).form = (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) := by
  change Matrix.conjTranspose (J.complexU w) *
    Matrix.diagonal (fun i => ((J.complexD w i).re : ℂ)) * J.complexU w = _
  rw [J.complexForm w]
  rw [show (fun i => ((J.complexD w i).re : ℂ)) = J.complexD w from
    funext fun i => (J.complexD_eq_ofReal_re w i).symm]

/-- Simultaneous real/Hermitian Siegel bounds at every infinite place. -/
def NumberFieldArchimedeanJacobiData.IsSiegel
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (t u : ℝ) : Prop :=
  (∀ w, (J.realJacobiData w).IsSiegel t u) ∧
    ∀ w, (J.complexJacobiData w).IsSiegel t u

omit [NumberField K] in
/-- Expanded entrywise form of simultaneous archimedean Siegel bounds. -/
theorem NumberFieldArchimedeanJacobiData.isSiegel_iff
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (t u : ℝ) :
    J.IsSiegel t u ↔
      ((∀ w (i j : Fin n), (i : ℕ) + 1 = (j : ℕ) →
          J.realD w i ≤ t * J.realD w j) ∧
       (∀ w (i j : Fin n), |J.realU w i j| ≤ u)) ∧
      ((∀ w (i j : Fin n), (i : ℕ) + 1 = (j : ℕ) →
          (J.complexD w i).re ≤ t * (J.complexD w j).re) ∧
       ∀ w (i j : Fin n), ‖J.complexU w i j‖ ≤ u) := by
  rfl

end

end GaloisForLFunctions.HTGeometry
