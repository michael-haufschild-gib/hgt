import GaloisForLFunctions.HTGeometry.BohrProductRule

/-!
# The frequency module of a product

The spectral product rule says a frequency of `f · g` splits as a sum of a frequency of `f` and a
frequency of `g`.  Spanning, the frequency module of the product lies in the join of the two
frequency modules, with no hypothesis on the shape of either factor.
-/

open MeasureTheory

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- **The spectrum of a product is contained in the sum of the spectra.** -/
theorem bohrSpectrum_mul_subset {f g : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htbf : HasTotallyBoundedOrbit (fun x => f x)) (hg : UniformContinuous (fun x => g x))
    (htbg : HasTotallyBoundedOrbit (fun x => g x)) :
    bohrSpectrum (fun t => f t * g t)
      ⊆ {lam : ℝ | ∃ mu ∈ bohrSpectrum (fun x => f x), ∃ nu ∈ bohrSpectrum (fun x => g x),
        mu + nu = lam} := by
  intro lam hlam
  by_contra hnot
  refine hlam ?_
  refine bohrCoefficient_mul_eq_zero hf htbf hg htbg ?_
  intro mu nu hsum
  by_contra hne
  push Not at hne
  exact hnot ⟨mu, hne.1, nu, hne.2, hsum⟩

/-- **The product rule for frequency modules.**  The frequency module of a product of two
almost-periodic functions lies in the join of their frequency modules. -/
theorem bohrFrequencyModule_mul_le {f g : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htbf : HasTotallyBoundedOrbit (fun x => f x)) (hg : UniformContinuous (fun x => g x))
    (htbg : HasTotallyBoundedOrbit (fun x => g x)) :
    bohrFrequencyModule (fun t => f t * g t)
      ≤ bohrFrequencyModule (fun x => f x) ⊔ bohrFrequencyModule (fun x => g x) := by
  rw [bohrFrequencyModule]
  refine Submodule.span_le.mpr ?_
  intro lam hlam
  obtain ⟨mu, hmu, nu, hnu, rfl⟩ := bohrSpectrum_mul_subset hf htbf hg htbg hlam
  exact Submodule.add_mem_sup (Submodule.subset_span hmu) (Submodule.subset_span hnu)

end

end GaloisForLFunctions
