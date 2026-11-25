import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Conditioning.FirstWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Conditioning.GaussianMaximal

/-! # Quantitative conditional resolution of the physical first excursion -/

open MeasureTheory ProbabilityTheory Real Set
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
noncomputable section

/-- The average over revealed backgrounds controls all window radii together.
The same bound applies to the first crossing, elapsed wait, or absolute
first entry, with any prescribed subsets of the Gaussian couplings revealed. -/
theorem gaussian_first_wait_resolution_tail (n j s : ℕ) (S : Set (PrefixIndex n))
    (a b : ℝ) {T M : ℝ} (hT : 0<T) (hM : 0<M) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let d := Fintype.card (ChainLabel (n+2))
    let F := revealedPassage n j s S a b
    μ.real {x | ∃ h> (0:ℝ), (M/T)*h < μ.real {y | |F (x,y)-T|<h}} ≤
      16*(exp 1)^2*(2*(d:ℝ)+1)/M := by
  intro μ d F
  obtain ⟨hm,hs⟩ := revealedPassage_properties n j s S a b
  have h := gaussian_conditional_maximal _ hm hs hT hM
  change μ.real {x | (x,T)∈excessKernel μ F (M/T)} ≤ _
  apply h.trans_eq
  rw [Fintype.card_fin]
  dsimp only [d]
  ring

#print axioms gaussian_first_wait_resolution_tail
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
