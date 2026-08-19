/-
# The shell polynomial of the criticality product scales

Transporting the joint scaling law across the descent needs the ordering-free spectral scaling in
its general form: for a symmetric polynomial over any `ℚ`-algebra and any coefficient homomorphism,
the value at the spectrum of a scaled Hermitian matrix is the value at the scaled spectrum.  With
that, the shell polynomial inherits the fixed-power scaling of the joint product.

Main results:
* `eval₂_symmetric_eigenvalues_smul` — **the spectral scaling with a general coefficient
  homomorphism**.
* `eval_shellPoly_jointCriticalProduct_smul` — **the shell polynomial scales by a fixed power**.
-/
import GaloisForLFunctions.HTGeometry.JointDescent

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- **The spectral scaling with a general coefficient homomorphism.** -/
theorem eval₂_symmetric_eigenvalues_smul {R : Type*} [CommRing R] [Algebra ℚ R]
    (A : MvPolynomial (Fin D) R) (hA : A.IsSymmetric) (f : R →+* ℝ)
    {H : Matrix (Fin D) (Fin D) ℂ} (hH : H.IsHermitian) (t : ℝ)
    (hHt : ((((t : ℝ) : ℂ)) • H).IsHermitian) :
    MvPolynomial.eval₂ f (fun i => hHt.eigenvalues i) A
      = MvPolynomial.eval₂ f (fun i => t * hH.eigenvalues i) A := by
  obtain ⟨W, hW⟩ := exists_aeval_psum_repr_of_isSymmetric A hA
  have hpsum : ∀ (lam : Fin D → ℝ) (j : ℕ),
      (MvPolynomial.eval₂Hom f lam) (MvPolynomial.psum (Fin D) R (j + 1))
        = ∑ i, lam i ^ (j + 1) := by
    intro lam j
    rw [MvPolynomial.psum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hgen : ∀ lam : Fin D → ℝ,
      MvPolynomial.eval₂ f lam A
        = MvPolynomial.eval₂ f (fun j : ℕ => ∑ i, lam i ^ (j + 1)) W := by
    intro lam
    rw [← hW, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
    have hcomp := MvPolynomial.eval₂_comp_left
      (MvPolynomial.eval₂Hom f lam)
      (MvPolynomial.C : R →+* MvPolynomial (Fin D) R)
      (fun j : ℕ => MvPolynomial.psum (Fin D) R (j + 1)) W
    refine Eq.trans hcomp ?_
    congr 1
    · exact RingHom.ext fun r => by simp
    · funext j
      exact hpsum lam j
  rw [hgen (fun i => hHt.eigenvalues i), hgen (fun i => t * hH.eigenvalues i)]
  congr 1
  funext j
  exact sum_pow_eigenvalues_smul hH t hHt (j + 1)

/-- **The shell polynomial of the criticality product scales by a fixed power.** -/
theorem eval_shellPoly_jointCriticalProduct_smul {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (hc : ∀ n, (c n).IsHomogeneous (M - n)) (k : Fin D → ℝ) (G : MvPolynomial (Fin N) ℝ)
    (hG : ∀ θ : Fin N → ℝ, MvPolynomial.eval θ G
      = MvPolynomial.eval
          (Sum.elim (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) θ)
          (jointCriticalProduct M c k))
    (t : ℝ) (θ : Fin N → ℝ) :
    MvPolynomial.eval (fun a => t * θ a) G
      = t ^ ((Finset.univ : Finset (Equiv.Perm (Fin D))).card * ((M + 1) * 2))
        * MvPolynomial.eval θ G := by
  classical
  have hsm : ((((t : ℝ) : ℂ)) • spectralEnsembleMatrix P θ).IsHermitian := by
    rw [← spectralEnsembleMatrix_smul P t θ]
    exact isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)
  have heig := eigenvalues_spectralEnsembleMatrix_smul hP t θ hsm
  set A := (MvPolynomial.sumAlgEquiv ℝ (Fin D) (Fin N)) (jointCriticalProduct M c k) with hA
  have hAsym : A.IsSymmetric := isSymmetric_sumAlgEquiv_jointCriticalProduct M c k
  calc MvPolynomial.eval (fun a => t * θ a) G
      = MvPolynomial.eval₂ (MvPolynomial.eval (fun a => t * θ a))
          (fun i => (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)).eigenvalues i) A := by
        rw [hG (fun a => t * θ a), hA, eval_sumAlgEquiv]
    _ = MvPolynomial.eval₂ (MvPolynomial.eval (fun a => t * θ a))
          (fun i => hsm.eigenvalues i) A := by rw [heig]
    _ = MvPolynomial.eval₂ (MvPolynomial.eval (fun a => t * θ a))
          (fun i => t * (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) A :=
        eval₂_symmetric_eigenvalues_smul A hAsym _ (isHermitian_spectralEnsembleMatrix hP θ) t hsm
    _ = MvPolynomial.eval
          (Sum.elim (fun i => t * (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i)
            (fun a => t * θ a)) (jointCriticalProduct M c k) := by
        rw [hA, eval_sumAlgEquiv]
    _ = t ^ ((Finset.univ : Finset (Equiv.Perm (Fin D))).card * ((M + 1) * 2))
          * MvPolynomial.eval
            (Sum.elim (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) θ)
            (jointCriticalProduct M c k) :=
        eval_jointCriticalProduct_smul M c hc k θ _ t
    _ = t ^ ((Finset.univ : Finset (Equiv.Perm (Fin D))).card * ((M + 1) * 2))
          * MvPolynomial.eval θ G := by rw [hG θ]

end

end GaloisForLFunctions.HTGeometry
