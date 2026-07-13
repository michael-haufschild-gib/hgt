import GaloisForLFunctions.RHTower.XiHurwitzAnchorPrimeTwoSeam
import GaloisForLFunctions.RHTower.XiHurwitzOrientationSourceSequenceGate

/-!
# The common first-prime seam is exactly the Xi--Hurwitz orientation zero locus

The normalized Hurwitz anchor tail and the translated von Mangoldt source have the same
first-prime seam charge.  This module identifies the apparent extra assertion that this common
charge vanishes with the already formalized scalar Xi--Hurwitz orientation energy.

Pointwise, the first-prime charge is odd under functional-equation/Schwarz reflection and vanishes
exactly when the Hurwitz orientation defect vanishes.  Globally, the following three statements
are equivalent:

* every Xi-indexed common first-prime charge vanishes;
* every normalized Hurwitz anchor seam tends to zero;
* the canonical scalar orientation energy is zero.

Consequently the existing algebraic regular-Cauchy source-core positivity interface discharges the
common-charge assertion.  This does not prove that positivity: it proves that common-charge
vanishing is not an additional gap beyond the already isolated source sign.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- The first-prime seam is odd under the functional-equation/Schwarz reflection. -/
theorem orbitwiseFirstPrimeSeamCharge_lineReflect (rho : ℂ) :
    orbitwiseFirstPrimeSeamCharge (1 - (starRingEnd ℂ) rho) =
      -orbitwiseFirstPrimeSeamCharge rho := by
  simp only [orbitwiseFirstPrimeSeamCharge, map_sub, map_one, Complex.conj_conj]
  ring

/-- Pointwise common-charge vanishing is exactly the Hurwitz orientation zero locus. -/
theorem orbitwiseFirstPrimeSeamCharge_eq_zero_iff_orientationDefect_zero
    (rho : XiDivisorSupport) :
    orbitwiseFirstPrimeSeamCharge (rho : ℂ) = 0 ↔
      xiHurwitzOrientationDefect rho = 0 :=
  (orbitwiseFirstPrimeSeamCharge_eq_zero_iff (rho : ℂ)).trans
    (xiHurwitzOrientationDefect_eq_zero_iff_re_eq_half rho).symm

/-- Vanishing of every Xi-indexed common first-prime seam charge. -/
def XiFirstPrimeSeamChargesVanish : Prop :=
  ∀ rho : XiDivisorSupport,
    orbitwiseFirstPrimeSeamCharge (rho : ℂ) = 0

/-- The complete family of first-prime charges vanishes exactly at zero scalar orientation
energy.  Thus the common-charge assertion is not independent of the existing energy gate. -/
theorem xiFirstPrimeSeamChargesVanish_iff_orientationEnergy_zero :
    XiFirstPrimeSeamChargesVanish ↔ xiHurwitzOrientationEnergy = 0 := by
  constructor
  · intro h
    apply xiHurwitzOrientationEnergy_eq_zero_iff_terms.mpr
    intro rho
    apply (xiHurwitzOrientationEnergyTerm_eq_zero_iff rho).mpr
    exact (orbitwiseFirstPrimeSeamCharge_eq_zero_iff_orientationDefect_zero rho).mp
      (h rho)
  · intro h rho
    apply (orbitwiseFirstPrimeSeamCharge_eq_zero_iff_orientationDefect_zero rho).mpr
    apply (xiHurwitzOrientationEnergyTerm_eq_zero_iff rho).mp
    exact xiHurwitzOrientationEnergy_eq_zero_iff_terms.mp h rho

/-- Convergence of every normalized Hurwitz anchor seam to zero is exactly vanishing of its common
first-prime limit. -/
theorem xiHurwitzAnchorPrimeTwoSeamsVanish_iff_firstPrimeSeamChargesVanish :
    XiHurwitzAnchorPrimeTwoSeamsVanish ↔ XiFirstPrimeSeamChargesVanish := by
  constructor
  · intro h rho
    have hcharge := tendsto_xiHurwitzAnchorPrimeTwoSeam
      (xi_divisor_support_re_mem_open_unit rho)
    exact tendsto_nhds_unique hcharge (h rho)
  · intro h rho
    have hcharge := tendsto_xiHurwitzAnchorPrimeTwoSeam
      (xi_divisor_support_re_mem_open_unit rho)
    simpa only [h rho] using hcharge

/-- **Gap identification.**  The apparent extra common-seam assertion is exactly zero scalar
Xi--Hurwitz orientation energy. -/
theorem xiHurwitzAnchorPrimeTwoSeamsVanish_iff_orientationEnergy_zero :
    XiHurwitzAnchorPrimeTwoSeamsVanish ↔
      xiHurwitzOrientationEnergy = 0 :=
  xiHurwitzAnchorPrimeTwoSeamsVanish_iff_firstPrimeSeamChargesVanish.trans
    xiFirstPrimeSeamChargesVanish_iff_orientationEnergy_zero

/-- Existing source-core positivity discharges the common-charge assertion.  The source-core sign
itself remains the open mathematical input. -/
theorem xiHurwitzAnchorPrimeTwoSeamsVanish_of_cauchyCore_nonnegative
    (hpos : ∀ v ∈ xiWeilCauchyAlgebraicSubspace,
      0 ≤ xiWeilHilbertQuadratic v) :
    XiHurwitzAnchorPrimeTwoSeamsVanish := by
  apply xiHurwitzAnchorPrimeTwoSeamsVanish_iff_orientationEnergy_zero.mpr
  apply riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mp
  exact riemannHypothesis_of_cauchyCore_nonnegative hpos

end

end RHTower
