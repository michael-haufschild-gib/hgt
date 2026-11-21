import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.StatementA



open MvPolynomial

noncomputable section

namespace WindowedLandauTheory.GradedWeylDivisibility

theorem fischerInnerWeightOrthogonal_holds : FockWeightOrth := by
  intro σ M _ w μ μ' f g hne hf hg
  unfold WindowedLandauTheory.REAL.fockF
  refine Finset.sum_eq_zero fun m hm => ?_
  have hgm : g.coeff m = 0 := by
    by_contra h
    exact hne ((hf (mem_support_iff.mp hm)).symm.trans (hg h))
  rw [hgm, star_zero, mul_zero, zero_mul]

end WindowedLandauTheory.GradedWeylDivisibility

