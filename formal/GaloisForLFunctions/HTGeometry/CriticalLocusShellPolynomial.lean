/-
# The critical-locus shell polynomial

Symmetrising the criticality square sum over all labellings of the spectrum produces a symmetric
spectral function with coordinate-ring coefficients, hence a single real polynomial in the shell
coordinates.  That polynomial vanishes at every coordinate vector at which the tangential gradient
of some labelled spectral action vanishes.

This is the polynomial the transversality tail needs.

Main results:
* `exists_criticalLocusShellPoly` — **a real shell polynomial vanishing on the critical locus**.
-/
import GaloisForLFunctions.HTGeometry.ShellSymmetricOverCoordinates

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- **A real shell polynomial vanishing on the critical locus.**  It comes with the polynomial
relation satisfied by every labelled spectral action, and vanishes wherever the tangential gradient
of one of them does. -/
theorem exists_criticalLocusShellPoly {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) :
    ∃ (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (G : MvPolynomial (Fin N) ℝ),
      (∀ (π₀ : Equiv.Perm (Fin D)) (θ : Fin N → ℝ),
        ∑ n ∈ Finset.range m, MvPolynomial.eval θ (c n)
          * (shellSpectralAction hP k π₀ θ) ^ n = 0) ∧
      (∀ (π₀ : Equiv.Perm (Fin D)) (θ₀ : Fin N → ℝ),
        (∀ i : Fin N, HasDerivAt (fun t : ℝ =>
            shellSpectralAction hP k π₀ (fun j => θ₀ j + (if j = i then t else 0)))
          (shellSpectralAction hP k π₀ θ₀ * θ₀ i) 0) →
        MvPolynomial.eval θ₀ G = 0) := by
  classical
  obtain ⟨m, c, hrel⟩ := exists_shellRelation_labeledAction hP k
  set Q : Polynomial (MvPolynomial (Fin N) ℝ) := criticalitySquareSum m c with hQ
  set kC : Fin D → MvPolynomial (Fin N) ℝ := fun j => MvPolynomial.C (k j) with hkC
  obtain ⟨G, hG⟩ := exists_shellPoly_of_isSymmetric_over hP (actionValueProduct Q kC)
    (isSymmetric_actionValueProduct Q kC)
  refine ⟨m, c, G, hrel, fun π₀ θ₀ hcrit => ?_⟩
  have hprod := eval₂_actionValueProduct (MvPolynomial.eval θ₀)
    (fun i => (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues i) Q kC
  have hfac : ∀ π : Equiv.Perm (Fin D),
      Polynomial.eval₂ (MvPolynomial.eval θ₀)
          (∑ j, MvPolynomial.eval θ₀ (kC j) *
            (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) Q
        = Polynomial.eval (shellSpectralAction hP k π θ₀)
            (Polynomial.map (MvPolynomial.eval θ₀) Q) := by
    intro π
    rw [Polynomial.eval_map]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hkC, MvPolynomial.eval_C]
  have hcritEq : ∀ i : Fin N,
      (∑ n ∈ Finset.range m, MvPolynomial.eval θ₀ (MvPolynomial.pderiv i (c n))
          * (shellSpectralAction hP k π₀ θ₀) ^ n)
        + (∑ n ∈ Finset.range m, (n : ℝ) * MvPolynomial.eval θ₀ (c n)
            * (shellSpectralAction hP k π₀ θ₀) ^ (n - 1))
          * (shellSpectralAction hP k π₀ θ₀ * θ₀ i) = 0 :=
    fun i => shell_criticality_relation c (shellSpectralAction hP k π₀) θ₀ i (hrel π₀) (hcrit i)
  have hzero := eval_map_criticalitySquareSum_eq_zero_of_forall m c θ₀
    (shellSpectralAction hP k π₀ θ₀) hcritEq
  rw [← hG θ₀, hprod]
  refine Finset.prod_eq_zero (Finset.mem_univ π₀) ?_
  rw [hfac π₀]
  exact hzero

end

end GaloisForLFunctions.HTGeometry
