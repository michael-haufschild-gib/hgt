/-
# One literal pair of Hamiltonians witnesses every spectral-action level

The nonconstancy theorem asks for a coefficient vector avoiding each prescribed quadratic
spectral-action level.  Since the spectrum has only finitely many labellings, those separately
chosen witnesses can be compressed into one pair of Hamiltonians.  Fix the first coefficient
vector to a coordinate basis vector.  Each labelling of its spectrum determines one forbidden
level.  The descended shell-obstruction polynomial for every such level is nonzero; their finite
product is therefore nonzero, and one evaluation of that product supplies a second coefficient
vector avoiding all labelled ratios simultaneously.

Main result:
* `exists_disjoint_actionRatio_pair_of_witness` -- the concrete two-Hamiltonian witness.
-/
import GaloisForLFunctions.HTGeometry.SpectralActionWitness
import GaloisForLFunctions.HTGeometry.PolynomialEvaluationLemma

open Filter Topology Set MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m N D : ℕ}

/-- **Positive-dimensional two-Hamiltonian compression.**  This is the dimension-agnostic form of
the witness-pair theorem: any nonempty finite coefficient space suffices. -/
theorem exists_disjoint_actionRatio_pair_of_witness_of_pos
    {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (k : Fin D → ℝ) (hN : 0 < N)
    (hwit : ∀ b : ℝ, ∃ θ₀ : Fin N → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ (2 : ℕ)
        ≠ b ^ (2 : ℕ) * (∑ a, (θ₀ a) ^ (2 : ℕ))) :
    ∃ θ₁ θ₂ : Fin N → ℝ, ∀ π₁ π₂ : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₁).eigenvalues (π₁ j)) ^ (2 : ℕ)
          * (∑ a, (θ₂ a) ^ (2 : ℕ))
        ≠ (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₂).eigenvalues (π₂ j)) ^ (2 : ℕ)
          * (∑ a, (θ₁ a) ^ (2 : ℕ)) := by
  classical
  let i₀ : Fin N := ⟨0, hN⟩
  let θ₁ : Fin N → ℝ := Pi.single i₀ 1
  let level : Equiv.Perm (Fin D) → ℝ := fun π =>
    ∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₁).eigenvalues (π j)
  choose G hG using fun π : Equiv.Perm (Fin D) =>
    exists_shellPoly_jointActionDefectProduct hP k (level π)
  have hGne : ∀ π : Equiv.Perm (Fin D), G π ≠ 0 := by
    intro π hzero
    obtain ⟨θ, hθ⟩ := hwit (level π)
    have heval : MvPolynomial.eval θ (G π) = 0 := by simp [hzero]
    rw [hG π θ, eval_jointActionDefectProduct] at heval
    obtain ⟨σ, -, hσ⟩ := Finset.prod_eq_zero_iff.mp heval
    exact hθ σ (sub_eq_zero.mp hσ)
  let Q : MvPolynomial (Fin N) ℝ := ∏ π : Equiv.Perm (Fin D), G π
  have hQne : Q ≠ 0 := by
    dsimp only [Q]
    exact Finset.prod_ne_zero_iff.mpr fun π _ => hGne π
  obtain ⟨θ₂, hθ₂⟩ := AffineJet.exists_eval_ne_zero hQne
  have hfactor : ∀ π : Equiv.Perm (Fin D), MvPolynomial.eval θ₂ (G π) ≠ 0 := by
    intro π hzero
    apply hθ₂
    dsimp only [Q]
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ π) hzero
  have hnorm₁ : ∑ a, (θ₁ a) ^ (2 : ℕ) = 1 := by
    simp [θ₁, Pi.single_apply]
  refine ⟨θ₁, θ₂, ?_⟩
  intro π₁ π₂ hcollision
  apply hfactor π₁
  rw [hG π₁ θ₂, eval_jointActionDefectProduct]
  refine Finset.prod_eq_zero (Finset.mem_univ π₂) ?_
  rw [hnorm₁, mul_one] at hcollision
  change
    (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₂).eigenvalues (π₂ j)) ^ (2 : ℕ)
      - level π₁ ^ (2 : ℕ) * (∑ a, (θ₂ a) ^ (2 : ℕ)) = 0
  dsimp only [level]
  linarith

/-- **One literal two-Hamiltonian witness.**  If every prescribed quadratic level is missed by
some member of a Hermitian linear ensemble, then two members of that ensemble have disjoint lists
of squared labelled spectral-action ratios.  The first member is the explicit coefficient-basis
vector `Pi.single 0 1`; the second is one real evaluation of the finite product of all forbidden
level polynomials. -/
theorem exists_disjoint_actionRatio_pair_of_witness
    {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (k : Fin D → ℝ)
    (hwit : ∀ b : ℝ, ∃ θ₀ : Fin (m + 1) → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ (2 : ℕ)
        ≠ b ^ (2 : ℕ) * (∑ a, (θ₀ a) ^ (2 : ℕ))) :
    ∃ θ₁ θ₂ : Fin (m + 1) → ℝ, ∀ π₁ π₂ : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₁).eigenvalues (π₁ j)) ^ (2 : ℕ)
          * (∑ a, (θ₂ a) ^ (2 : ℕ))
        ≠ (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₂).eigenvalues (π₂ j)) ^ (2 : ℕ)
      * (∑ a, (θ₁ a) ^ (2 : ℕ)) :=
  exists_disjoint_actionRatio_pair_of_witness_of_pos hP k (Nat.succ_pos m) hwit

end

end GaloisForLFunctions.HTGeometry
