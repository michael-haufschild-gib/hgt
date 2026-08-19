/-
# Two coefficient vectors with disjoint action ratios refute constancy at every level

The witness the nonconstancy criterion needs is quantified over the constant value: for each `b`
one coefficient vector at which no labelling reaches `b`.  A single pair of coefficient vectors
suffices, provided the squared action-to-energy ratios they realise are disjoint: a level reached
at both points would force one ratio from the first list to equal one from the second.

Main results:
* `exists_witness_of_disjoint_actionRatio` — **the two-point witness criterion**.
* `tendsto_integral_exp_sortedSpectralAction_zero_of_disjoint` — **angular dephasing from two
  coefficient vectors**.
-/
import GaloisForLFunctions.HTGeometry.SpectralActionNonconstancy

open Filter Topology Set MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- **The two-point witness criterion.**  If the squared action-to-energy ratios realised at two
coefficient vectors are disjoint, then for every level one of the two vectors misses it. -/
theorem exists_witness_of_disjoint_actionRatio {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) {θ₁ θ₂ : Fin N → ℝ}
    (hdisj : ∀ π₁ π₂ : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₁).eigenvalues (π₁ j)) ^ 2
          * (∑ a, (θ₂ a) ^ 2)
        ≠ (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₂).eigenvalues (π₂ j)) ^ 2
          * (∑ a, (θ₁ a) ^ 2)) (b : ℝ) :
    ∃ θ₀ : Fin N → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ 2
        ≠ b ^ 2 * (∑ a, (θ₀ a) ^ 2) := by
  classical
  by_contra hcon
  have h1 : ∃ π₁ : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₁).eigenvalues (π₁ j)) ^ 2
        = b ^ 2 * (∑ a, (θ₁ a) ^ 2) := by
    by_contra h
    exact hcon ⟨θ₁, fun π hπ => h ⟨π, hπ⟩⟩
  have h2 : ∃ π₂ : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₂).eigenvalues (π₂ j)) ^ 2
        = b ^ 2 * (∑ a, (θ₂ a) ^ 2) := by
    by_contra h
    exact hcon ⟨θ₂, fun π hπ => h ⟨π, hπ⟩⟩
  obtain ⟨π₁, hπ₁⟩ := h1
  obtain ⟨π₂, hπ₂⟩ := h2
  refine hdisj π₁ π₂ ?_
  rw [hπ₁, hπ₂]
  ring

section Dephasing

variable {m : ℕ}

/-- **Angular dephasing from two coefficient vectors.** -/
theorem tendsto_integral_exp_sortedSpectralAction_zero_of_disjoint
    {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (hDisc : spectralDiscriminantPoly P ≠ 0) (k : Fin D → ℝ) {θ₁ θ₂ : Fin (m + 1) → ℝ}
    (hdisj : ∀ π₁ π₂ : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₁).eigenvalues (π₁ j)) ^ 2
          * (∑ a, (θ₂ a) ^ 2)
        ≠ (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₂).eigenvalues (π₂ j)) ^ 2
          * (∑ a, (θ₁ a) ^ 2))
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℂ) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Filter.Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * sortedSpectralAction hP k
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (m + 1)))) : ℝ) : ℂ) * Complex.I)
        ∂(MeasureTheory.volume.toSphere))
      (Filter.cocompact ℝ) (nhds 0) :=
  tendsto_integral_exp_sortedSpectralAction_zero_of_witness hP hDisc k
    (exists_witness_of_disjoint_actionRatio hP k hdisj) g hg hC0 hC

end Dephasing

end

end GaloisForLFunctions.HTGeometry
