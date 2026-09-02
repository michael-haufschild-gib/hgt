import GaloisForLFunctions.RHTower.SchattenLogResidueTraceClassPerturbation
import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaTraceClassFeatureRobinTraceNoGo

namespace RHTower

open _root_.ContinuousLinearMap Filter Finset
open scoped Topology

noncomputable section

/-- The actual causal-depth Gamma feature is invisible to every additive measurable logarithmic
singular residue. -/
theorem hasSchattenLogResidue_one_add_suzukiCanonicalCausalDepthGammaFeature_iff
    (A : SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2)
    (hAcpt : IsCompactOperator A) (R : ℝ) :
    HasSchattenLogResidue 1
        (A + suzukiCanonicalCausalDepthGammaFeatureOperator) R ↔
      HasSchattenLogResidue 1 A R :=
  hasSchattenLogResidue_one_add_iff_of_memSchattenClass_one hAcpt
    suzukiCanonicalCausalDepthGammaFeatureOperator_memSchattenClass_one R

/-- A candidate additive singular-residue reporter is coefficient-faithful only if adding the
actual CCM--FU source changes its measurable logarithmic residue. -/
structure SuzukiCausalDepthGammaAdditiveSingularResidueCoefficientFaithful where
  background : SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2
  background_compact : IsCompactOperator background
  backgroundResidue : ℝ
  sourceResidue : ℝ
  background_weak : MemWeakSchattenClass 1 background
  background_residue : HasSchattenLogResidue 1 background backgroundResidue
  source_residue : HasSchattenLogResidue 1
    (background + suzukiCanonicalCausalDepthGammaFeatureOperator) sourceResidue
  detects_actual_source : sourceResidue ≠ backgroundResidue

/-- **Additive singular-residue CCM--FU no-go.** No measurable logarithmic singular residue can
retain a nonzero coefficient of the actual causal-depth Gamma feature when it is added to an
arbitrary compact weak-`S¹` background. -/
theorem no_suzukiCausalDepthGammaAdditiveSingularResidueCoefficientFaithful :
    ¬ Nonempty SuzukiCausalDepthGammaAdditiveSingularResidueCoefficientFaithful := by
  rintro ⟨P⟩
  have hsourceOnBackground :
      HasSchattenLogResidue 1 P.background P.sourceResidue :=
    (hasSchattenLogResidue_one_add_suzukiCanonicalCausalDepthGammaFeature_iff
      P.background P.background_compact P.sourceResidue).1 P.source_residue
  have heq : P.sourceResidue = P.backgroundResidue :=
    tendsto_nhds_unique hsourceOnBackground P.background_residue
  exact P.detects_actual_source heq

end

end RHTower
