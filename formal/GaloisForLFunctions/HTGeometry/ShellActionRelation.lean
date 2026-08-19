/-
# The spectral action of the shell satisfies a polynomial relation with polynomial coefficients

The symmetrised labelled action polynomial has symmetric coefficients, so each of them is a real
polynomial in the shell coordinates; and every labelled action value is one of its roots.  Hence
the spectral action of a Hermitian interaction family satisfies, at every coordinate vector, a
polynomial relation whose coefficients are polynomials in the coordinates.

This is exactly the hypothesis of the criticality criterion.

Main results:
* `exists_realShellCoeff_labeledActionPoly` — the coefficients as shell polynomials.
* `exists_shellRelation_labeledAction` — **the polynomial relation satisfied by the spectral
  action**.
* `exists_shell_criticality_polynomial` — **the criticality criterion for the spectral action**.
-/
import GaloisForLFunctions.HTGeometry.RealValuedComplexPolynomial
import GaloisForLFunctions.HTGeometry.LabeledActionSymmetricPolynomial
import GaloisForLFunctions.HTGeometry.ShellCriticalityCriterion

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- The spectral action of a coefficient vector at one labelling of the shell spectrum. -/
def shellSpectralAction {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (k : Fin D → ℝ) (π₀ : Equiv.Perm (Fin D)) (θ : Fin N → ℝ) : ℝ :=
  ∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues (π₀ j)

/-- The coefficients of the symmetrised labelled action polynomial are shell polynomials. -/
theorem exists_realShellCoeff_labeledActionPoly {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) :
    ∃ c : ℕ → MvPolynomial (Fin N) ℝ, ∀ (n : ℕ) (θ : Fin N → ℝ),
      MvPolynomial.eval
          (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i)
          ((labeledActionPoly k).coeff n)
        = MvPolynomial.eval θ (c n) := by
  choose c hc using fun n : ℕ => exists_realShellPoly_of_isSymmetric hP
    ((labeledActionPoly k).coeff n) (isSymmetric_coeff_labeledActionPoly k n)
  exact ⟨c, fun n θ => hc n θ⟩

/-- **The polynomial relation satisfied by the spectral action.**  For every labelling of the
spectrum, the corresponding spectral action is a root of a polynomial whose coefficients are
polynomials in the shell coordinates. -/
theorem exists_shellRelation_labeledAction {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) :
    ∃ (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ),
      ∀ (π₀ : Equiv.Perm (Fin D)) (θ : Fin N → ℝ),
        ∑ n ∈ Finset.range m, MvPolynomial.eval θ (c n)
          * (shellSpectralAction hP k π₀ θ) ^ n = 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_realShellCoeff_labeledActionPoly hP k
  refine ⟨(labeledActionPoly k).natDegree + 1, c, fun π₀ θ => ?_⟩
  set lam : Fin D → ℝ :=
    fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i with hlam
  have hroot := eval_map_labeledActionPoly k lam π₀
  have hact : shellSpectralAction hP k π₀ θ = ∑ j, k j * lam (π₀ j) := rfl
  rw [hact]
  have hdeg : (Polynomial.map (MvPolynomial.eval lam) (labeledActionPoly k)).natDegree
      < (labeledActionPoly k).natDegree + 1 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_map_le)
  rw [Polynomial.eval_eq_sum_range' hdeg] at hroot
  rw [← hroot]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Polynomial.coeff_map, hc n θ]

/-- **The criticality criterion for the spectral action.**  There is one polynomial family, common
to every labelling and every coordinate vector, whose vanishing expresses the vanishing of the
tangential gradient of the spectral action. -/
theorem exists_shell_criticality_polynomial {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) :
    ∃ (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ),
      ∀ (π₀ : Equiv.Perm (Fin D)) (θ₀ : Fin N → ℝ) (i : Fin N),
        HasDerivAt (fun t : ℝ =>
            shellSpectralAction hP k π₀ (fun j => θ₀ j + (if j = i then t else 0)))
          (shellSpectralAction hP k π₀ θ₀ * θ₀ i) 0 →
        (∑ n ∈ Finset.range m, MvPolynomial.eval θ₀ (MvPolynomial.pderiv i (c n))
              * (shellSpectralAction hP k π₀ θ₀) ^ n)
          + (∑ n ∈ Finset.range m, (n : ℝ) * MvPolynomial.eval θ₀ (c n)
              * (shellSpectralAction hP k π₀ θ₀) ^ (n - 1))
            * (shellSpectralAction hP k π₀ θ₀ * θ₀ i) = 0 := by
  obtain ⟨m, c, hrel⟩ := exists_shellRelation_labeledAction hP k
  refine ⟨m, c, fun π₀ θ₀ i hcrit => ?_⟩
  exact shell_criticality_relation c (shellSpectralAction hP k π₀) θ₀ i (hrel π₀) hcrit

end

end GaloisForLFunctions.HTGeometry
