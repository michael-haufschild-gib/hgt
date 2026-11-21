import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.StatementA
import GaloisForLFunctions.WindowedLandauTheory.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle



open MvPolynomial

noncomputable section

namespace WindowedLandauTheory.GradedWeylDivisibility

theorem fischerInnerConjSymm_holds : FockHerm := by
  intro σ f g
  exact WindowedLandauTheory.REAL.fischerInner_eq_star g f

end WindowedLandauTheory.GradedWeylDivisibility

