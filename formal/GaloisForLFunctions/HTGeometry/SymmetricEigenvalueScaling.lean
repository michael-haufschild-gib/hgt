/-
# Symmetric functions of a Hermitian spectrum scale with the matrix

Scaling a Hermitian matrix by a real number scales its spectrum, but only up to the ordering that
the canonical eigenvalue list imposes.  A symmetric function does not see the ordering, and it is a
polynomial in the power sums, which scale exactly; so every symmetric function of the spectrum
scales by the corresponding power.

Main results:
* `sum_pow_eigenvalues_smul` — the power sums scale.
* `eval_symmetric_eigenvalues_smul` — **every symmetric function of the spectrum scales**.
-/
import GaloisForLFunctions.HTGeometry.SymmetricTraceRepresentation

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {D : ℕ}

/-- The power sums of the spectrum scale with the matrix. -/
theorem sum_pow_eigenvalues_smul {H : Matrix (Fin D) (Fin D) ℂ} (hH : H.IsHermitian) (t : ℝ)
    (hHt : (((t : ℝ) : ℂ) • H).IsHermitian) (n : ℕ) :
    ∑ i, (hHt.eigenvalues i) ^ n = ∑ i, (t * hH.eigenvalues i) ^ n := by
  have hC : ∑ i, ((hHt.eigenvalues i : ℝ) : ℂ) ^ n
      = ∑ i, ((t * hH.eigenvalues i : ℝ) : ℂ) ^ n := by
    have h1 : ((((t : ℝ) : ℂ) • H) ^ n).trace = ∑ i, ((hHt.eigenvalues i : ℝ) : ℂ) ^ n :=
      trace_pow_eq_sum_eigenvalues_pow hHt n
    have h2 : (H ^ n).trace = ∑ i, ((hH.eigenvalues i : ℝ) : ℂ) ^ n :=
      trace_pow_eq_sum_eigenvalues_pow hH n
    have h3 : ((((t : ℝ) : ℂ) • H) ^ n).trace = (((t : ℝ) : ℂ)) ^ n * (H ^ n).trace := by
      rw [smul_pow, Matrix.trace_smul, smul_eq_mul]
    rw [← h1, h3, h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have := hC
  exact_mod_cast this

/-- **Every symmetric function of a Hermitian spectrum scales with the matrix.** -/
theorem eval_symmetric_eigenvalues_smul (p : MvPolynomial (Fin D) ℝ) (hp : p.IsSymmetric)
    {H : Matrix (Fin D) (Fin D) ℂ} (hH : H.IsHermitian) (t : ℝ)
    (hHt : (((t : ℝ) : ℂ) • H).IsHermitian) :
    MvPolynomial.eval (fun i => hHt.eigenvalues i) p
      = MvPolynomial.eval (fun i => t * hH.eigenvalues i) p := by
  obtain ⟨W, hW⟩ := exists_aeval_psum_repr_of_isSymmetric p hp
  have hpsum : ∀ (lam : Fin D → ℝ) (j : ℕ),
      MvPolynomial.eval lam (MvPolynomial.psum (Fin D) ℝ (j + 1))
        = ∑ i, lam i ^ (j + 1) := by
    intro lam j
    rw [MvPolynomial.psum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hgen : ∀ lam : Fin D → ℝ,
      MvPolynomial.eval lam p
        = MvPolynomial.eval₂ (RingHom.id ℝ) (fun j : ℕ => ∑ i, lam i ^ (j + 1)) W := by
    intro lam
    rw [← hW, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
    have hcomp := MvPolynomial.eval₂_comp_left
      (MvPolynomial.eval₂Hom (RingHom.id ℝ) lam)
      (MvPolynomial.C : ℝ →+* MvPolynomial (Fin D) ℝ)
      (fun j : ℕ => MvPolynomial.psum (Fin D) ℝ (j + 1)) W
    refine Eq.trans hcomp ?_
    congr 1
    · exact RingHom.ext fun r => by simp
    · funext j
      exact hpsum lam j
  rw [hgen (fun i => hHt.eigenvalues i), hgen (fun i => t * hH.eigenvalues i)]
  congr 1
  funext j
  exact sum_pow_eigenvalues_smul hH t hHt (j + 1)

end

end GaloisForLFunctions.HTGeometry
