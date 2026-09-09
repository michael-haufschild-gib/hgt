import GaloisForLFunctions.RHTower.FokasLenellsCausalPointSpectrum
import Mathlib.Analysis.Normed.Operator.Banach

/-! The actual spectral equation on the complete closed generator graph. This is the Banach-space
representation needed for open mapping; the original domain retains its weaker data norm. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual state/derivative graph pair of a maximal-domain vector. -/
def causalGeneratorDomainGraph : causalGeneratorDomain →ₗ[ℂ] causalGeneratorGraph where
  toFun u := ⟨(u.val, causalGenerator u),
    (causalGeneratorGraph_mem_iff _ _).2 (causalGenerator_hasRightDeriv u)⟩
  map_add' u v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_add causalGenerator u v
  map_smul' c u := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_smul causalGenerator c u

/-- The actual graph input, continuously valued in the maximal domain with its inherited data norm. -/
def causalGeneratorGraphDomain : causalGeneratorGraph →L[ℂ] causalGeneratorDomain :=
  causalGeneratorGraphInput.codRestrict causalGeneratorDomain (fun p => ⟨p, rfl⟩)

/-- Converting an actual domain vector to its graph pair preserves the vector exactly. -/
theorem causalGeneratorGraphDomain_domainGraph (u : causalGeneratorDomain) :
    causalGeneratorGraphDomain (causalGeneratorDomainGraph u) = u := rfl

/-- Every actual graph pair is recovered from its domain input and the actual generator. -/
theorem causalGeneratorDomainGraph_graphDomain (p : causalGeneratorGraph) :
    causalGeneratorDomainGraph (causalGeneratorGraphDomain p) = p := by
  apply causalGeneratorGraphInput_injective
  rfl

/-- The actual graph norm dominates the original data norm. -/
theorem causalGeneratorGraphInput_norm_le (p : causalGeneratorGraph) :
    ‖causalGeneratorGraphInput p‖ ≤ ‖p‖ := by
  change ‖p.val.1‖ ≤ max ‖p.val.1‖ ‖p.val.2‖
  exact le_max_left _ _

/-- The spectral equation as a bounded map on the actual complete closed graph. -/
def causalComplexGraphShift (z : ℂ) : causalGeneratorGraph →L[ℂ] hardyL2ᗮ :=
  z • causalGeneratorGraphInput - causalGeneratorGraphOutput

/-- The bounded graph shift agrees with the original unbounded-domain equation. -/
theorem causalComplexGraphShift_domainGraph (z : ℂ) (u : causalGeneratorDomain) :
    causalComplexGraphShift z (causalGeneratorDomainGraph u) = causalComplexGeneratorShift z u := rfl

/-- Reading the domain input of a graph pair preserves its actual spectral equation. -/
theorem causalComplexGraphShift_graphDomain (z : ℂ) (p : causalGeneratorGraph) :
    causalComplexGeneratorShift z (causalGeneratorGraphDomain p) = causalComplexGraphShift z p := by
  rw [← causalComplexGraphShift_domainGraph, causalGeneratorDomainGraph_graphDomain]

/-- Surjectivity is exactly the same for the complete graph and the original maximal-domain equation. -/
theorem causalComplexGraphShift_surjective_iff (z : ℂ) :
    Function.Surjective (causalComplexGraphShift z) ↔ Function.Surjective (causalComplexGeneratorShift z) := by
  constructor
  · intro h u
    obtain ⟨p, hp⟩ := h u
    exact ⟨causalGeneratorGraphDomain p, (causalComplexGraphShift_graphDomain z p).trans hp⟩
  · intro h u
    obtain ⟨v, hv⟩ := h u
    exact ⟨causalGeneratorDomainGraph v, (causalComplexGraphShift_domainGraph z v).trans hv⟩

/-- Every imaginary-axis graph shift is injective on the actual closed graph. -/
theorem causalComplexGraphShift_imaginary_injective (ω : ℝ) :
    Function.Injective (causalComplexGraphShift ((ω : ℂ)*I)) := by
  intro p q h
  have hd : causalGeneratorGraphDomain p = causalGeneratorGraphDomain q := by
    apply causalComplexGeneratorShift_imaginary_injective ω
    rw [causalComplexGraphShift_graphDomain, causalComplexGraphShift_graphDomain, h]
  apply causalGeneratorGraphInput_injective
  exact congrArg (fun u : causalGeneratorDomain => u.val) hd

end
end RHTower.FokasLenells
