/-
# A symmetric function of the shell spectrum is a polynomial in the shell coordinates

The Hamiltonian of a Hermitian interaction family is linear in its coordinates, so the traces of
its powers are polynomials in them.  A symmetric function of the spectrum is a polynomial in those
traces, hence a polynomial in the coordinates -- with one and the same polynomial for every
coordinate vector.

This is the link that turns the symmetrised spectral constructions into genuine polynomials on the
shell, where the polynomial sublevel bounds apply.

Main results:
* `exists_shellPoly_of_isSymmetric` — **the shell polynomial of a symmetric spectral function**.
-/
import GaloisForLFunctions.HTGeometry.SymmetricTraceRepresentation
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {N D : ℕ}

/-- **The shell polynomial of a symmetric spectral function.** -/
theorem exists_shellPoly_of_isSymmetric {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (p : MvPolynomial (Fin D) ℂ) (hp : p.IsSymmetric) :
    ∃ G : MvPolynomial (Fin N) ℂ, ∀ θ : Fin N → ℝ,
      MvPolynomial.eval
          (fun i => (((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i : ℝ) : ℂ)) p
        = MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ)) G := by
  obtain ⟨W, hW⟩ := exists_trace_repr_of_isSymmetric p hp
  refine ⟨MvPolynomial.aeval
    (fun j : ℕ => ((spectralGenericMatrix P) ^ (j + 1)).trace) W, fun θ => ?_⟩
  have htr : ∀ j : ℕ,
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun a => ((θ a : ℝ) : ℂ)))
          (((spectralGenericMatrix P) ^ (j + 1)).trace)
        = ((spectralEnsembleMatrix P θ) ^ (j + 1)).trace := by
    intro j
    have hpow : (MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ))).mapMatrix
        ((spectralGenericMatrix P) ^ (j + 1)) = (spectralEnsembleMatrix P θ) ^ (j + 1) := by
      rw [map_pow, mapMatrix_spectralGenericMatrix]
    have h1 : ((MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ))).mapMatrix
        ((spectralGenericMatrix P) ^ (j + 1))).trace
        = MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ))
            (((spectralGenericMatrix P) ^ (j + 1)).trace) := trace_mapMatrix _ _
    rw [hpow] at h1
    exact h1.symm
  have hb := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ) (fun a => ((θ a : ℝ) : ℂ))
    (fun j : ℕ => ((spectralGenericMatrix P) ^ (j + 1)).trace) W
  rw [← MvPolynomial.aeval_eq_bind₁] at hb
  rw [hW (spectralEnsembleMatrix P θ) (isHermitian_spectralEnsembleMatrix hP θ)]
  refine Eq.trans ?_ hb.symm
  rw [funext htr]
  rfl

end

end GaloisForLFunctions.HTGeometry
