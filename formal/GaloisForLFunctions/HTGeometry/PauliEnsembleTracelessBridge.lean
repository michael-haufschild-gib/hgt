import GaloisForLFunctions.HTGeometry.PauliEnsembleCliffordCovariance
import GaloisForLFunctions.HTGeometry.PauliTwoLocalEmbedding

/-!
# The weighted Pauli ensemble as a traceless bounded-weight family

A weight function supported on the nonidentity Pauli strings of bounded weight makes the weighted
Pauli ensemble a member of the traceless bounded-weight polynomial family, at the coefficients
obtained by multiplying the weight into the coefficient vector.
-/

open Matrix

open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n q : ℕ}

/-- **The ensemble is a traceless bounded-weight evaluation.** -/
theorem pauliEnsemble_eq_tracelessEval (w J : (Fin n → Option (Fin 3)) → ℝ)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0) :
    pauliEnsemble w J =
      (pauliTracelessPolynomialMatrix n q).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun P : PauliTracelessLabel n q => ((w P.1 * J P.1 : ℝ) : ℂ))) := by
  classical
  ext x y
  rw [eval_pauliTracelessPolynomialMatrix, pauliEnsemble, Matrix.sum_apply]
  have hfilter : ∀ P : Fin n → Option (Fin 3),
      P ∈ Finset.univ.filter (fun P => pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) ↔
        (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) := by
    intro P
    simp
  have hsubtype :
      (∑ P ∈ Finset.univ.filter (fun P => pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n),
          ((w P * J P : ℝ) : ℂ) * finitePauliMatrix P x y) =
        ∑ P : PauliTracelessLabel n q,
          ((w P.1 * J P.1 : ℝ) : ℂ) * finitePauliMatrix P.1 x y :=
    Finset.sum_subtype _ hfilter _
  rw [← hsubtype]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun P _ hP => ?_).symm
  have hzero : w P = 0 := by
    refine hw P ?_
    intro hcon
    exact hP ((hfilter P).mpr hcon)
  rw [hzero]
  simp

/-- The same identity in the numbered coefficient presentation used by the genericity theorem. -/
theorem pauliEnsemble_eq_tracelessFinEval (w J : (Fin n → Option (Fin 3)) → ℝ)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0) :
    pauliEnsemble w J =
      (pauliTracelessFinPolynomialMatrix n q).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        fun t => (((fun P : PauliTracelessLabel n q => w P.1 * J P.1)
          ((pauliTracelessLabelEquivFin n q).symm t) : ℝ) : ℂ)) := by
  classical
  rw [pauliEnsemble_eq_tracelessEval w J hw, map_eval_pauliTracelessFinPolynomialMatrix]
  congr 1
  funext P
  simp

end GaloisForLFunctions.HTGeometry
