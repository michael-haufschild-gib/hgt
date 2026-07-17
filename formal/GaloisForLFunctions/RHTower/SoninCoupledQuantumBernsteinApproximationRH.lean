import GaloisForLFunctions.RHTower.SoninCoupledQuantumHausdorff
import GaloisForLFunctions.RHTower.PrimeArchBernsteinPurityDivergence
import GaloisForLFunctions.RHTower.PrimeArchBernsteinNegativeMassAbscissa

/-!
# Quantum discharge for coupled-Sonin Bernstein approximation routes

Complete Hausdorff positivity of density-replica moments makes every coupled Sonin source an
admissible positive comparator for the existing Bernstein approximation criteria.  Its zeroth
replica value lies in `[0,1]`, so the bounded-mass Hilbert criterion also receives the universal
mass-square ceiling `1`.

The resulting statements remove all positivity and mass hypotheses from the coupled-source
routes.  Only the source/target Bernstein discrepancy estimates remain.
-/

namespace RHTower

noncomputable section

open Filter Topology

/-- The zeroth density-replica value of every coupled Sonin channel has mass square at most one,
including the degenerate zero-channel case. -/
theorem soninAllPrimeCoupledRenyiReplicaMoment_zero_sq_le_one
    (a : SoninPositiveAperture) :
    soninAllPrimeCoupledRenyiReplicaMoment a 0 ^ 2 ≤ 1 := by
  have h := soninAllPrimeCoupledRenyiReplicaMoment_mem_Icc a 0
  simpa only [pow_two, one_mul] using mul_self_le_mul_self h.1 h.2

/-- **Hypothesis-free coupled Hilbert comparator criterion.**  A uniform squared Bernstein
distance bound from coupled Sonin density-replica packets along cofinal degrees proves RH.
Quantum positivity and the comparator mass ceiling are automatic. -/
theorem riemannHypothesis_of_cofinal_soninCoupledRenyi_bernsteinSquareDiscrepancy_bounded
    (d : ℕ → ℕ) (a : ℕ → SoninPositiveAperture) (E : ℝ)
    (hd : Tendsto d atTop atTop)
    (herr : ∀ j,
      bernsteinCoefficientSquareDiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment)
        (soninAllPrimeCoupledRenyiReplicaMoment (a j)) (d j) ≤ E) :
    RiemannHypothesis :=
  riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_squareDiscrepancy_bounded
    d (fun j => soninAllPrimeCoupledRenyiReplicaMoment (a j)) 1 E hd
    (fun j => soninAllPrimeCoupledRenyiReplicaMoment_hausdorffBernsteinNonnegative (a j))
    (fun j => soninAllPrimeCoupledRenyiReplicaMoment_zero_sq_le_one (a j)) herr

/-- Under failure of RH, the degree-matched Bernstein Hilbert distance from every coupled Sonin
density-replica family diverges.  Positivity and bounded mass need not be assumed. -/
theorem tendsto_soninCoupledRenyi_bernsteinSquareDiscrepancy_atTop_of_not_rh
    (hRH : ¬ RiemannHypothesis) (a : ℕ → SoninPositiveAperture) :
    Tendsto
      (fun N => bernsteinCoefficientSquareDiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment)
        (soninAllPrimeCoupledRenyiReplicaMoment (a N)) N)
      atTop atTop :=
  tendsto_bernsteinSquareDiscrepancy_from_boundedMass_positiveComparators_atTop_of_not_rh
    hRH (fun N => soninAllPrimeCoupledRenyiReplicaMoment (a N)) 1
    (fun N => soninAllPrimeCoupledRenyiReplicaMoment_hausdorffBernsteinNonnegative (a N))
    (fun N => soninAllPrimeCoupledRenyiReplicaMoment_zero_sq_le_one (a N))

/-- **Hypothesis-free coupled `L¹` comparator criterion.**  A uniform aggregate Bernstein
packet discrepancy from coupled Sonin density-replica moments along cofinal degrees proves RH. -/
theorem riemannHypothesis_of_cofinal_soninCoupledRenyi_bernsteinL1Discrepancy_bounded
    (d : ℕ → ℕ) (a : ℕ → SoninPositiveAperture) (C : ℝ)
    (hd : Tendsto d atTop atTop)
    (herr : ∀ j,
      bernsteinCoefficientL1DiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment)
        (soninAllPrimeCoupledRenyiReplicaMoment (a j)) (d j) ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_l1Discrepancy_bounded
    d (fun j => soninAllPrimeCoupledRenyiReplicaMoment (a j)) C hd
    (fun j => soninAllPrimeCoupledRenyiReplicaMoment_hausdorffBernsteinNonnegative (a j)) herr

/-- **Hypothesis-free coupled quadratic packet criterion.**  At the natural inverse-dimension
scale, one squared coupled-Sonin Bernstein packet estimate along cofinal degrees proves RH. -/
theorem riemannHypothesis_of_cofinal_soninCoupledRenyi_bernsteinSquareDiscrepancy
    (d : ℕ → ℕ) (a : ℕ → SoninPositiveAperture) (C : ℝ)
    (hC : 0 ≤ C) (hd : Tendsto d atTop atTop)
    (henergy : ∀ j, (d j + 2 : ℝ) *
      bernsteinCoefficientSquareDiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment)
        (soninAllPrimeCoupledRenyiReplicaMoment (a j)) (d j) ≤ C ^ 2) :
    RiemannHypothesis :=
  riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_squareDiscrepancy
    d (fun j => soninAllPrimeCoupledRenyiReplicaMoment (a j)) C hC hd
    (fun j => soninAllPrimeCoupledRenyiReplicaMoment_hausdorffBernsteinNonnegative (a j))
    henergy

end

end RHTower
