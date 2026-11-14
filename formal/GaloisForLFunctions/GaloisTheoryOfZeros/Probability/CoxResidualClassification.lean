import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.FiniteGammaCoxLaw

/-!
# Transporting exact residual criteria to Gamma–Cox laws

A proved zero-set equivalence identifies the deterministic pattern recovered by
the finite probability law. This separates scalar encoding from probability.
-/

open Filter Topology
open scoped Classical
namespace GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
noncomputable section

/-- An exact zero criterion transfers simultaneous consistency to its stated predicate. -/
theorem tendsto_classification_error {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (P : ι → Prop) [DecidablePred P] (hP : ∀ i, g i = 0 ↔ P i) :
    Tendsto (fun K => (binaryLaw K g).real {b | b ≠ fun i => decide (P i)})
      atTop (𝓝 0) := by
  have hp : zeroPattern g = fun i => decide (P i) := by
    funext i
    by_cases h : P i <;> simp [zeroPattern, hP, h]
  simpa only [hp] using tendsto_binaryLaw_error g

end
end GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_classification_error
