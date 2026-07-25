import GaloisForLFunctions.RHTower.SoninCoupledPrimeArchGramTransfer

/-!
# Coupled Sonin moment-ratio normalization closure

The coupled all-prime source column is nonzero at every positive aperture.  Consequently its
zeroth trace moment is always strictly positive, and normalized moment-ratio coupling needs only
the convergence of its nonconstant ratios.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Convergence of the nonconstant coupled moment ratios.  Degree-zero positivity is omitted
because it follows from the prime-square residual channel at every positive aperture. -/
def SoninCoupledPrimeArchNonconstantMomentRatioCoupling
    (aperture : ℕ → ℕ → SoninPositiveAperture) : Prop :=
  ∀ N k, 0 < k → k < 2 * N - 1 →
    Tendsto (fun j : ℕ =>
        soninAllPrimeCoupledTraceMoment (aperture N j) k /
          soninAllPrimeCoupledTraceMoment (aperture N j) 0)
      atTop
      (nhds ((((normalizedPrimeArchMoment k : ℝ) : ℂ) /
        ((normalizedPrimeArchMoment 0 : ℝ) : ℂ))))

/-- The original moment-ratio coupling is exactly nonconstant ratio convergence: its
degree-zero positivity conjunct is automatic from source data. -/
theorem soninCoupledPrimeArchMomentRatioCoupling_iff_nonconstant
    {aperture : ℕ → ℕ → SoninPositiveAperture} :
    SoninCoupledPrimeArchMomentRatioCoupling aperture ↔
      SoninCoupledPrimeArchNonconstantMomentRatioCoupling aperture := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro N j
    exact
      (soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero
        (aperture N j)).2
        (soninAllPrimeColumnCoordinateOperator_ne_zero
          (aperture N j).1 (aperture N j).2)

/-- Nonconstant coupled moment-ratio convergence alone implies RH; no normalization sign or
nondegeneracy hypothesis remains. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchNonconstantMomentRatioCoupling
    {aperture : ℕ → ℕ → SoninPositiveAperture}
    (h : SoninCoupledPrimeArchNonconstantMomentRatioCoupling aperture) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchMomentRatioCoupling
    (soninCoupledPrimeArchMomentRatioCoupling_iff_nonconstant.2 h)

end

end RHTower
