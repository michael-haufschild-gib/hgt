import GaloisForLFunctions.RepresentationLifting.InnerProduct.ReflectionGramRealization
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeCauchyDephasing

/-!
# Minimal reflection realizations of dephased probe Grams

Every dephasing iterate preserves the two sector inequalities. Their exact
realizability criterion therefore constructs a finite unitary-reflection
model at every iterate, including singular Gram data. The active dimension
is the sum of the positive and negative sector ranks, and no realization
can use fewer dimensions.
-/

noncomputable section
open scoped ComplexOrder
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open GaloisForLFunctions.RepresentationLifting.ReflectionGrams
open HilbertMetric.CauchyDephasing
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) (r : Fin N → ℝ) (k : ℕ)

/-- Every dephased ordinary/Weil Gram pair has an exact finite reflection model of optimal active dimension. -/
theorem dephased_probe_reflection_realization :
    ∃ v : Fin N → PairSpace (Fin N),
      Matrix.gram ℂ v = (channelPower k r (hilbertProbeGram p)).transpose ∧
      mixedGram pairReflection v = (dephasedProbeGram k r p).transpose ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range (doubledFeature pairReflection v))) =
        (channelPower k r (hilbertProbeGram p) + dephasedProbeGram k r p).rank +
        (channelPower k r (hilbertProbeGram p) - dephasedProbeGram k r p).rank := by
  obtain ⟨hp, hm⟩ := dephasedProbeGram_hilbert_sandwich k r p
  have hp' : ((channelPower k r (hilbertProbeGram p)).transpose +
      (dephasedProbeGram k r p).transpose).PosSemidef := by
    rw [← Matrix.transpose_add]
    exact hp.transpose
  have hm' : ((channelPower k r (hilbertProbeGram p)).transpose -
      (dephasedProbeGram k r p).transpose).PosSemidef := by
    rw [← Matrix.transpose_sub]
    exact hm.transpose
  obtain ⟨v, hv, hK⟩ := exists_pair_realization (ι := Fin N) hp' hm'
  refine ⟨v, hv, hK, ?_⟩
  rw [active_dimension (pairReflection (ι := Fin N))
      (pairReflection_involutive (ι := Fin N)), hv, hK,
    ← Matrix.transpose_add, ← Matrix.transpose_sub, Matrix.rank_transpose, Matrix.rank_transpose]

/-- Every other finite realization obeys the same sharp sector-rank lower bound. -/
theorem dephased_probe_realization_dimension_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (R : E ≃ₗᵢ[ℂ] E) (hR : ∀ x, R (R x) = x) (v : Fin N → E)
    (hG : Matrix.gram ℂ v = (channelPower k r (hilbertProbeGram p)).transpose)
    (hK : mixedGram R v = (dephasedProbeGram k r p).transpose) :
    (channelPower k r (hilbertProbeGram p) + dephasedProbeGram k r p).rank +
      (channelPower k r (hilbertProbeGram p) - dephasedProbeGram k r p).rank ≤
        Module.finrank ℂ E := by
  have h := dimension_lower_bound R hR v
  rwa [hG, hK, ← Matrix.transpose_add, ← Matrix.transpose_sub,
    Matrix.rank_transpose, Matrix.rank_transpose] at h

#print axioms dephased_probe_reflection_realization
#print axioms dephased_probe_realization_dimension_lower_bound
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
