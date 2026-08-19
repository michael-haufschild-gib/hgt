/-
# The shell coefficients of the action polynomial scale

The coefficient of `Y^n` in the symmetrised action polynomial is homogeneous of the complementary
degree in the eigenvalue variables, and the spectrum of the family scales with the coordinates.
Hence the shell polynomial representing that coefficient scales by the corresponding power.

Main results:
* `isHomogeneous_labeledAction`, `isHomogeneous_coeff_labeledActionPoly` — the degrees.
* `spectralEnsembleMatrix_smul`, `eigenvalues_spectralEnsembleMatrix_smul` — the family is linear
  in the coordinates, so its spectrum scales.
* `eval_shellCoeff_smul` — **the shell coefficients scale**.
-/
import GaloisForLFunctions.HTGeometry.ProdXSubCCoeffHomogeneous
import GaloisForLFunctions.HTGeometry.SymmetricEigenvalueScaling
import GaloisForLFunctions.HTGeometry.ShellActionRelation

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommRing R]

theorem isHomogeneous_labeledAction [DecidableEq σ] (k : σ → R) (π : Equiv.Perm σ) :
    (labeledAction k π).IsHomogeneous 1 := by
  rw [labeledAction]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
  simpa using (MvPolynomial.isHomogeneous_C σ (k j)).mul (MvPolynomial.isHomogeneous_X R (π j))

theorem isHomogeneous_coeff_labeledActionPoly [DecidableEq σ] [Nontrivial R] (k : σ → R) (n : ℕ) :
    ((labeledActionPoly k).coeff n).IsHomogeneous
      ((Finset.univ : Finset (Equiv.Perm σ)).card - n) :=
  isHomogeneous_coeff_prod_X_sub_C (labeledAction k) (isHomogeneous_labeledAction k)
    Finset.univ n

variable {N D : ℕ}

theorem spectralEnsembleMatrix_smul (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (t : ℝ)
    (θ : Fin N → ℝ) :
    spectralEnsembleMatrix P (fun a => t * θ a)
      = (((t : ℝ) : ℂ)) • spectralEnsembleMatrix P θ := by
  rw [spectralEnsembleMatrix, spectralEnsembleMatrix, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

theorem eigenvalues_spectralEnsembleMatrix_smul {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (t : ℝ) (θ : Fin N → ℝ)
    (hsm : ((((t : ℝ) : ℂ)) • spectralEnsembleMatrix P θ).IsHermitian) :
    (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)).eigenvalues = hsm.eigenvalues :=
  (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
    (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)) hsm).2
    (congrArg Matrix.charpoly (spectralEnsembleMatrix_smul P t θ))

/-- **The shell coefficients of the symmetrised action polynomial scale.** -/
theorem eval_shellCoeff_smul {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (hc : ∀ (n : ℕ) (θ : Fin N → ℝ),
      MvPolynomial.eval
          (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i)
          ((labeledActionPoly k).coeff n)
        = MvPolynomial.eval θ (c n))
    (n : ℕ) (t : ℝ) (θ : Fin N → ℝ) :
    MvPolynomial.eval (fun a => t * θ a) (c n)
      = t ^ ((Finset.univ : Finset (Equiv.Perm (Fin D))).card - n)
        * MvPolynomial.eval θ (c n) := by
  classical
  have hsm : ((((t : ℝ) : ℂ)) • spectralEnsembleMatrix P θ).IsHermitian := by
    rw [← spectralEnsembleMatrix_smul P t θ]
    exact isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)
  have heig := eigenvalues_spectralEnsembleMatrix_smul hP t θ hsm
  calc MvPolynomial.eval (fun a => t * θ a) (c n)
      = MvPolynomial.eval
          (fun i => (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)).eigenvalues i)
          ((labeledActionPoly k).coeff n) := (hc n (fun a => t * θ a)).symm
    _ = MvPolynomial.eval (fun i => hsm.eigenvalues i) ((labeledActionPoly k).coeff n) := by
        rw [heig]
    _ = MvPolynomial.eval
          (fun i => t * (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i)
          ((labeledActionPoly k).coeff n) :=
        eval_symmetric_eigenvalues_smul _ (isSymmetric_coeff_labeledActionPoly k n)
          (isHermitian_spectralEnsembleMatrix hP θ) t hsm
    _ = t ^ ((Finset.univ : Finset (Equiv.Perm (Fin D))).card - n) *
          MvPolynomial.eval
            (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i)
            ((labeledActionPoly k).coeff n) :=
        eval_smul_of_isHomogeneous (isHomogeneous_coeff_labeledActionPoly k n) t _
    _ = t ^ ((Finset.univ : Finset (Equiv.Perm (Fin D))).card - n)
          * MvPolynomial.eval θ (c n) := by rw [hc n θ]

end

end GaloisForLFunctions.HTGeometry
