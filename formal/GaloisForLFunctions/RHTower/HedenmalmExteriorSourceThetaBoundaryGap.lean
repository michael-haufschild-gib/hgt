import GaloisForLFunctions.RHTower.HedenmalmCoefficientFaithfulExteriorSourceContour
import GaloisForLFunctions.RHTower.HedenmalmThetaGreenReflectionPairNoGo
import GaloisForLFunctions.RHTower.HedenmalmFixedCenterExteriorReflectionEnergy

/-!
# Exterior source contours detect the theta Green boundary current

The coefficient-faithful four-contour construction and the Hedenmalm theta Green-square operator
are not independent Route P mechanisms.  A nonneutral rank-two theta boundary current on any
height-local divisor fibre forces the two-orientation prime--Gamma contour landing above the same
indivisible Ward--Green quantum.

Consequently a strict subquantum source bound is exactly a same-fibre boundary-neutralization
mechanism.  Polynomial interpolation growth is only a presentation issue: the remaining producer
must kill the oriented rank-two current before reflection pairing or positive squaring.  No source
bound or RH conclusion is asserted here.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive real landing of the two adjacent fixed-center source-contour orientations. -/
def xiPrimeWardExteriorTwoOrientationLandingEnergy
    (S : Finset XiDivisorSupport) (t : ℝ) : ℝ :=
  xiExteriorCayleyAbelFixedPacketEnergy S 1 t +
    xiExteriorCayleyAbelFixedPacketEnergy S 1 (t - 1)

/-- Analytic multiplicity can only increase one exterior norm square. -/
theorem normSq_le_multiplicity_normSq
    (rho : XiDivisorSupport) (z : ℂ) :
    Complex.normSq z ≤
      Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) * z) := by
  rw [Complex.normSq_mul]
  have hm : (1 : ℝ) ≤ xiSupportMultiplicity rho := by
    exact_mod_cast xiSupportMultiplicity_pos rho
  have hmSq : (1 : ℝ) ≤
      Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ)) := by
    norm_num [Complex.normSq_apply]
    have hprod : 0 ≤ ((xiSupportMultiplicity rho : ℝ) - 1) *
        ((xiSupportMultiplicity rho : ℝ) + 1) :=
      mul_nonneg (sub_nonneg.mpr hm) (by positivity)
    nlinarith
  calc
    Complex.normSq z = 1 * Complex.normSq z := by ring
    _ ≤ Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ)) *
        Complex.normSq z :=
      mul_le_mul_of_nonneg_right hmSq (Complex.normSq_nonneg z)

/-- The full multiplicity-square packet landing dominates every retained local fixed-center
energy. -/
theorem xiFixedCenterExteriorEnergy_le_twoOrientationLandingEnergy_of_mem
    (S : Finset XiDivisorSupport) (t : ℝ) (rho : XiDivisorSupport)
    (hrho : rho ∈ S) :
    xiFixedCenterExteriorEnergy t rho ≤
      xiPrimeWardExteriorTwoOrientationLandingEnergy S t := by
  rw [xiFixedCenterExteriorEnergy,
    xiPrimeWardExteriorTwoOrientationLandingEnergy,
    xiExteriorCayleyAbelFixedPacketEnergy,
    xiExteriorCayleyAbelFixedPacketEnergy]
  have hplus : Complex.normSq (xiFixedAdjacentCayleyAbelCoefficient 1 t rho) ≤
      ∑ sigma ∈ S, Complex.normSq
        (((xiSupportMultiplicity sigma : ℕ) : ℂ) *
          xiExteriorCayleyAbelFixedCoefficient 1 t sigma) := by
    calc
      Complex.normSq (xiFixedAdjacentCayleyAbelCoefficient 1 t rho) =
          Complex.normSq (xiExteriorCayleyAbelFixedCoefficient 1 t rho) := by rfl
      _ ≤ Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
          xiExteriorCayleyAbelFixedCoefficient 1 t rho) :=
        normSq_le_multiplicity_normSq rho _
      _ ≤ _ := Finset.single_le_sum (s := S)
        (f := fun sigma => Complex.normSq
          (((xiSupportMultiplicity sigma : ℕ) : ℂ) *
            xiExteriorCayleyAbelFixedCoefficient 1 t sigma))
        (fun sigma _ => Complex.normSq_nonneg _) hrho
  have hminus : Complex.normSq (xiFixedAdjacentCayleyAbelCoefficient 1 (t - 1) rho) ≤
      ∑ sigma ∈ S, Complex.normSq
        (((xiSupportMultiplicity sigma : ℕ) : ℂ) *
          xiExteriorCayleyAbelFixedCoefficient 1 (t - 1) sigma) := by
    calc
      Complex.normSq (xiFixedAdjacentCayleyAbelCoefficient 1 (t - 1) rho) =
          Complex.normSq (xiExteriorCayleyAbelFixedCoefficient 1 (t - 1) rho) := by rfl
      _ ≤ Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
          xiExteriorCayleyAbelFixedCoefficient 1 (t - 1) rho) :=
        normSq_le_multiplicity_normSq rho _
      _ ≤ _ := Finset.single_le_sum (s := S)
        (f := fun sigma => Complex.normSq
          (((xiSupportMultiplicity sigma : ℕ) : ℂ) *
            xiExteriorCayleyAbelFixedCoefficient 1 (t - 1) sigma))
        (fun sigma _ => Complex.normSq_nonneg _) hrho
  linarith

/-- A nonneutral theta Green-boundary fibre forces the two-orientation exterior landing above
the indivisible Ward--Green quantum. -/
theorem four_mul_transverseQuantum_le_twoOrientationLandingEnergy_of_boundaryFlux_ne_zero
    (S : Finset XiDivisorSupport) (t : ℝ) (q : XiZeroCopy)
    (hq : q.1 ∈ S)
    (ht : |(xiSpectralPoint q).re - t| ≤ 1 / 2)
    (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    4 * (96 / 145 : ℝ) ^ (2 : ℕ) ≤
      xiPrimeWardExteriorTwoOrientationLandingEnergy S t := by
  have him : (xiSpectralPoint q).im ≠ 0 := by
    intro him
    apply hflux
    exact
      (thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero q).2 him
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by
    intro hline
    apply him
    rw [xiSpectralPoint_eq_support]
    exact (xiSpectralPointSupport_im_eq_zero_iff q.1).2 hline
  have hlocal := four_mul_transverseQuantum_le_xiFixedCenterExteriorEnergy
    t q.1 (by simpa only [xiSpectralPoint_eq_support] using ht) hoff
  exact hlocal.trans
    (xiFixedCenterExteriorEnergy_le_twoOrientationLandingEnergy_of_mem S t q.1 hq)

/-- Any strict subquantum bound for a packet containing a height-local fibre neutralizes that
fibre's actual theta Green rank-two boundary current. -/
theorem thetaXiRankTwoBoundaryFlux_eq_zero_of_twoOrientationLandingEnergy_lt_quantum
    (S : Finset XiDivisorSupport) (t : ℝ) (q : XiZeroCopy)
    (hq : q.1 ∈ S)
    (ht : |(xiSpectralPoint q).re - t| ≤ 1 / 2)
    (hsub : xiPrimeWardExteriorTwoOrientationLandingEnergy S t <
      4 * (96 / 145 : ℝ) ^ (2 : ℕ)) :
    thetaXiRankTwoBoundaryFlux q = 0 := by
  by_contra hflux
  exact (not_lt_of_ge
    (four_mul_transverseQuantum_le_twoOrientationLandingEnergy_of_boundaryFlux_ne_zero
      S t q hq ht hflux)) hsub

/-- The coefficient-faithful four-contour Cesaro sequence detects the same pointwise obstruction
as the theta Green rank-two boundary current, with a uniform quantitative gap. -/
theorem tendsto_coefficientFaithfulTwoOrientationSourceCesaro_and_quantum_of_boundaryFlux_ne_zero
    (p : Nat.Primes) {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (hclosed : ∀ rho ∈ xiDivisorSupportClosedRectangle z₁ z₂,
      xiZeroLineConjEquiv rho ∈ xiDivisorSupportClosedRectangle z₁ z₂)
    (t : ℝ) (q : XiZeroCopy)
    (hq : q.1 ∈ xiDivisorSupportClosedRectangle z₁ z₂)
    (ht : |(xiSpectralPoint q).re - t| ≤ 1 / 2)
    (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    Tendsto
        (xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro
          p z₁ z₂ t)
        atTop
        (nhds ((xiPrimeWardExteriorTwoOrientationLandingEnergy
          (xiDivisorSupportClosedRectangle z₁ z₂) t : ℝ) : ℂ)) ∧
      4 * (96 / 145 : ℝ) ^ (2 : ℕ) ≤
        xiPrimeWardExteriorTwoOrientationLandingEnergy
          (xiDivisorSupportClosedRectangle z₁ z₂) t := by
  constructor
  · simpa only [xiPrimeWardExteriorTwoOrientationLandingEnergy] using
      tendsto_xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro
        p hre him hbot htop hright hleft hclosed t
  · exact
      four_mul_transverseQuantum_le_twoOrientationLandingEnergy_of_boundaryFlux_ne_zero
        _ t q hq ht hflux

end

end RHTower
