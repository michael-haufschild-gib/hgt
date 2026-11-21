import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.StatementB
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.DualWeylDominanceOf



open MvPolynomial

noncomputable section

namespace WindowedLandauTheory.GradedWeylDivisibility

theorem weylEqNablaQ_of (h : ClosedEqNabla) : WeylEqNablaQ := by
  intro r n hn ν hν
  refine h r n hn ν hν (weyl ℚ r n hn ν) (weylLeDual ℚ r n hn ν hν)
    (fun a b k f hf => weylRowDivStable ℚ r n hn ν a b k f hf) ?_

  exact Submodule.subset_span ⟨[], rfl⟩

end WindowedLandauTheory.GradedWeylDivisibility

