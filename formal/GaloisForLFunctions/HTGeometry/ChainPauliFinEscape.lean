/-
# The numbered nearest-neighbour Pauli family escapes every constant real relation

The spanning witness of the qubit chain produces, for every nonzero balanced spectral character,
one Hamiltonian of the nearest-neighbour Pauli span whose spectrum is a simple root packet on which
no relabelling of the character vanishes.  Since the family is Hermitian, that packet is real, and
the real span of the numbered generators is the range of the family map.  This is the escape
hypothesis that the Kleinbock--Margulis extremality of the spectral gap maps consumes.

Main results:
* `mem_range_spectralEnsembleMatrix_of_mem_span` — the range of a linear family is its real span.
* `chainPauliFin_spectrumEscapesRealRelations` — **the escape property of the chain family**.
-/
import GaloisForLFunctions.HTGeometry.PauliChainSpanWitness
import GaloisForLFunctions.HTGeometry.SpectrumRealRelationEscape
import GaloisForLFunctions.HTGeometry.HermitianLocalSpectralObserverLaw
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem mem_range_spectralEnsembleMatrix_of_mem_span {N D : ℕ}
    {P : Fin N → Matrix (Fin D) (Fin D) ℂ} {H : Matrix (Fin D) (Fin D) ℂ}
    (hH : H ∈ Submodule.span ℝ (Set.range P)) :
    H ∈ Set.range (spectralEnsembleMatrix P) := by
  obtain ⟨θ, hθ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hH
  refine ⟨θ, ?_⟩
  rw [spectralEnsembleMatrix, ← hθ]
  refine Finset.sum_congr rfl fun a _ => ?_
  ext x y
  simp [Matrix.smul_apply, Complex.real_smul]

/-- **The numbered nearest-neighbour Pauli family escapes every constant real relation.**  The
spanning witness of the chain provides, for every nonzero balanced spectral character, one chain
Hamiltonian whose simple real spectrum makes every relabelled relation nonzero. -/
theorem chainPauliFin_spectrumEscapesRealRelations (k : ℕ) :
    SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix (chainPauliFin (k + 3)))) := by
  intro c hbal hne
  obtain ⟨H₀, energy₀, hspan, hinj, hroot, hfail⟩ := exists_pauliChain_spanWitness k 0 c hbal hne
  have hmem : H₀ ∈ Set.range (spectralEnsembleMatrix (chainPauliFin (k + 3))) :=
    mem_range_spectralEnsembleMatrix_of_mem_span hspan
  obtain ⟨θ, hθ⟩ := hmem
  have hHerm : H₀.IsHermitian := by
    rw [← hθ]
    exact isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) θ
  have hreal : ∀ j, (((energy₀ j).re : ℝ) : ℂ) = energy₀ j := by
    intro j
    have him := matrixCharpolyRelation_im_eq_zero_of_isHermitian H₀ hHerm (energy₀ j) (hroot j)
    exact Complex.ext rfl (by simp [him])
  refine ⟨H₀, ⟨θ, hθ⟩, fun j => (energy₀ j).re, ?_, ?_, ?_⟩
  · intro a b hab
    simp only at hab
    exact hinj (by rw [← hreal a, ← hreal b, hab])
  · intro j
    rw [hreal j]
    exact hroot j
  · intro σ
    have hσ := hfail σ
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, ne_eq] at hσ
    intro hzero
    simp only at hzero
    refine hσ ?_
    have hcast : ((∑ i, c i * (energy₀ (σ i)).re : ℝ) : ℂ)
        = ∑ j, ((c (σ.symm j) : ℝ) : ℂ) * energy₀ j := by
      push_cast
      rw [← Equiv.sum_comp σ (fun j => ((c (σ.symm j) : ℝ) : ℂ) * energy₀ j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Equiv.symm_apply_apply, hreal]
    rw [← hcast, hzero]
    simp

end

end GaloisForLFunctions.HTGeometry
