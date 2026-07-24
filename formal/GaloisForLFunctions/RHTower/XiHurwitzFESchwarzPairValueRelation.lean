import GaloisForLFunctions.RHTower.XiHurwitzFEAnchorCircuitCollision
import GaloisForLFunctions.RHTower.XiHurwitzAnchorPrimeTwoOrientationEnergy

/-!
# FE--Schwarz Hurwitz pair circuits are exactly the common first-prime seam

The rank-two continued-Hurwitz circuit joining functional-equation reflection `1 - rho` to
Schwarz reflection `conj rho` is not an independent RH input.  In the open critical strip it is
equivalent to vanishing of the common first-prime seam charge, and equivalently to convergence of
the normalized Hurwitz anchor seam to zero.

Over the Xi divisor this identifies the global pair circuit with both vanishing of all first-prime
charges and zero scalar Xi--Hurwitz orientation energy.  Thus any source theorem producing this
pair dependence must close the already isolated source-core sign gap; the differential circuit
does not create a second arithmetic obligation.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- In the open strip, the FE--Schwarz continued-Hurwitz pair is dependent exactly when the common
first-prime seam charge vanishes. -/
theorem continuedHurwitzFESchwarzPairDependent_iff_firstPrimeSeamCharge_eq_zero
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ContinuedHurwitzPairDifferentiallyDependent
        (1 - rho) ((starRingEnd ℂ) rho) ↔
      orbitwiseFirstPrimeSeamCharge rho = 0 := by
  rw [continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half hstrip,
    orbitwiseFirstPrimeSeamCharge_eq_zero_iff]

/-- The same pair circuit is exactly convergence of the normalized Hurwitz anchor seam to zero. -/
theorem continuedHurwitzFESchwarzPairDependent_iff_anchorPrimeTwoSeam_tendsto_zero
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ContinuedHurwitzPairDifferentiallyDependent
        (1 - rho) ((starRingEnd ℂ) rho) ↔
      Tendsto (xiHurwitzAnchorPrimeTwoSeam rho) atTop (nhds 0) := by
  rw [continuedHurwitzFESchwarzPairDependent_iff_firstPrimeSeamCharge_eq_zero hstrip]
  constructor
  · intro hzero
    simpa only [hzero] using tendsto_xiHurwitzAnchorPrimeTwoSeam hstrip
  · intro hlimit
    exact tendsto_nhds_unique (tendsto_xiHurwitzAnchorPrimeTwoSeam hstrip) hlimit

/-- Over the complete Xi divisor, the rank-two circuit is exactly vanishing of all common
first-prime seam charges. -/
theorem xiHurwitzFESchwarzPairCircuit_iff_firstPrimeSeamChargesVanish :
    XiHurwitzFESchwarzPairCircuit ↔ XiFirstPrimeSeamChargesVanish := by
  constructor
  · intro h rho
    exact
      (continuedHurwitzFESchwarzPairDependent_iff_firstPrimeSeamCharge_eq_zero
        (xi_divisor_support_re_mem_open_unit rho)).mp (h rho)
  · intro h rho
    exact
      (continuedHurwitzFESchwarzPairDependent_iff_firstPrimeSeamCharge_eq_zero
        (xi_divisor_support_re_mem_open_unit rho)).mpr (h rho)

/-- **Value-relation collapse.**  The global FE--Schwarz pair circuit is exactly zero scalar
Xi--Hurwitz orientation energy. -/
theorem xiHurwitzFESchwarzPairCircuit_iff_orientationEnergy_zero :
    XiHurwitzFESchwarzPairCircuit ↔ xiHurwitzOrientationEnergy = 0 :=
  xiHurwitzFESchwarzPairCircuit_iff_firstPrimeSeamChargesVanish.trans
    xiFirstPrimeSeamChargesVanish_iff_orientationEnergy_zero

/-- Vanishing of every first-prime seam charge is exactly RH. -/
theorem xiFirstPrimeSeamChargesVanish_iff_riemannHypothesis :
    XiFirstPrimeSeamChargesVanish ↔ RiemannHypothesis :=
  xiHurwitzFESchwarzPairCircuit_iff_firstPrimeSeamChargesVanish.symm.trans
    xiHurwitzFESchwarzPairCircuit_iff_riemannHypothesis

/-- Vanishing of every normalized prime-two Hurwitz anchor seam is exactly RH. -/
theorem xiHurwitzAnchorPrimeTwoSeamsVanish_iff_riemannHypothesis :
    XiHurwitzAnchorPrimeTwoSeamsVanish ↔ RiemannHypothesis :=
  xiHurwitzAnchorPrimeTwoSeamsVanish_iff_firstPrimeSeamChargesVanish.trans
    xiFirstPrimeSeamChargesVanish_iff_riemannHypothesis

end

end RHTower
