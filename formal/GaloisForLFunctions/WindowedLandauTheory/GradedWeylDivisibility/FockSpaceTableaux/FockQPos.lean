import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.StatementB
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas



open MvPolynomial

noncomputable section

namespace WindowedLandauTheory.GradedWeylDivisibility

theorem fischerInnerRatPos : FockQPos :=
  fun _ f g => ⟨lfockq_symm f g, fun hf => lfockq_self_pos f hf⟩

end WindowedLandauTheory.GradedWeylDivisibility

