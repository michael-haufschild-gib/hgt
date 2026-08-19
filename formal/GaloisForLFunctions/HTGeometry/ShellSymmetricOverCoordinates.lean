/-
# Symmetric spectral functions with coordinate-ring coefficients

The symmetrisation of the criticality expression over labellings is symmetric in the eigenvalue
variables but has coefficients in the coordinate ring, not in the reals.  Newton inversion works
over any `ℚ`-algebra, so it applies verbatim; substituting the power sums by the trace polynomials
of the family turns such an object into a single polynomial in the coordinates.

Main results:
* `exists_shellPoly_of_isSymmetric_over` — **the shell polynomial of a symmetric spectral function
  with coordinate-ring coefficients**.
-/
import GaloisForLFunctions.HTGeometry.CriticalitySquareSum

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- **The shell polynomial of a symmetric spectral function with coordinate-ring coefficients.** -/
theorem exists_shellPoly_of_isSymmetric_over {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian)
    (p : MvPolynomial (Fin D) (MvPolynomial (Fin N) ℝ)) (hp : p.IsSymmetric) :
    ∃ G : MvPolynomial (Fin N) ℝ, ∀ θ : Fin N → ℝ,
      MvPolynomial.eval₂ (MvPolynomial.eval θ)
          (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) p
        = MvPolynomial.eval θ G := by
  classical
  obtain ⟨W, hW⟩ := exists_aeval_psum_repr_of_isSymmetric p hp
  choose T hT using fun j : ℕ => exists_realShellPoly_of_isSymmetric hP
    (MvPolynomial.psum (Fin D) ℝ j) (MvPolynomial.psum_isSymmetric (Fin D) ℝ j)
  refine ⟨MvPolynomial.eval₂ (RingHom.id (MvPolynomial (Fin N) ℝ))
    (fun j : ℕ => T (j + 1)) W, fun θ => ?_⟩
  set lam : Fin D → ℝ :=
    fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i with hlam
  have hpsumEval : ∀ j : ℕ,
      (MvPolynomial.eval₂Hom (MvPolynomial.eval θ) lam)
          (MvPolynomial.psum (Fin D) (MvPolynomial (Fin N) ℝ) (j + 1))
        = MvPolynomial.eval θ (T (j + 1)) := by
    intro j
    have hL : (MvPolynomial.eval₂Hom (MvPolynomial.eval θ) lam)
        (MvPolynomial.psum (Fin D) (MvPolynomial (Fin N) ℝ) (j + 1))
        = ∑ i, lam i ^ (j + 1) := by
      rw [MvPolynomial.psum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by simp
    have hR : MvPolynomial.eval lam (MvPolynomial.psum (Fin D) ℝ (j + 1))
        = ∑ i, lam i ^ (j + 1) := by
      rw [MvPolynomial.psum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by simp
    rw [hL, ← hR, hT (j + 1) θ]
  have hLHS : MvPolynomial.eval₂ (MvPolynomial.eval θ) lam p
      = MvPolynomial.eval₂ (MvPolynomial.eval θ)
          (fun j : ℕ => MvPolynomial.eval θ (T (j + 1))) W := by
    rw [← hW, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
    have hcomp := MvPolynomial.eval₂_comp_left
      (MvPolynomial.eval₂Hom (MvPolynomial.eval θ) lam)
      (MvPolynomial.C : MvPolynomial (Fin N) ℝ →+*
        MvPolynomial (Fin D) (MvPolynomial (Fin N) ℝ))
      (fun j : ℕ => MvPolynomial.psum (Fin D) (MvPolynomial (Fin N) ℝ) (j + 1)) W
    refine Eq.trans hcomp ?_
    congr 1
    · exact RingHom.ext fun r => by simp
    · funext j
      exact hpsumEval j
  have hRHS : MvPolynomial.eval θ
        (MvPolynomial.eval₂ (RingHom.id (MvPolynomial (Fin N) ℝ)) (fun j : ℕ => T (j + 1)) W)
      = MvPolynomial.eval₂ (MvPolynomial.eval θ)
          (fun j : ℕ => MvPolynomial.eval θ (T (j + 1))) W := by
    have hcomp := MvPolynomial.eval₂_comp_left (MvPolynomial.eval θ)
      (RingHom.id (MvPolynomial (Fin N) ℝ)) (fun j : ℕ => T (j + 1)) W
    refine Eq.trans hcomp ?_
    congr 1
  rw [hLHS, hRHS]

end

end GaloisForLFunctions.HTGeometry
