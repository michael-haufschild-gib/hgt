import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.StatementB
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas



open MvPolynomial

noncomputable section

namespace WindowedLandauTheory.GradedWeylDivisibility

theorem fischerInnerRatBilinear : FockQBilin := fun _ f f' g c =>
  ⟨lfockq_add_left f f' g, lfockq_smul_left c f g⟩

end WindowedLandauTheory.GradedWeylDivisibility

