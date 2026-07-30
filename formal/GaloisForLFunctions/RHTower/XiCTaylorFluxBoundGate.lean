import GaloisForLFunctions.RHTower.PrimeArchSourceUpperBoundGate
import GaloisForLFunctions.RHTower.PrimeEnergyZeroTransfer
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Finite Xi-Taylor logarithmic-derivative bounds imply RH

The canonical Taylor polynomials of `XiC` converge locally uniformly on the plane.  Since every
approximant is entire, complex locally-uniform convergence differentiates; at each pole-free point,
their logarithmic derivatives therefore converge to `logDeriv XiC`, hence to the fixed continued
prime--archimedean source.

This discharges the finite-to-limit interface in the source upper-bound route.  It is enough to
bound, by one common real constant, the imaginary parts of the logarithmic derivatives of the
finite Xi Taylor polynomials eventually at each Gaussian-rational point of the original left
half-strip.  The resulting finite-polynomial condition is equivalent to RH.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Derivatives of the canonical Xi Taylor approximants converge locally uniformly. -/
theorem xiCTaylorApprox_deriv_tendstoLocallyUniformly :
    TendstoLocallyUniformly (deriv ∘ xiCTaylorApprox) (deriv XiC) atTop := by
  rw [← tendstoLocallyUniformlyOn_univ]
  apply xiCTaylorApprox_tendstoLocallyUniformly.tendstoLocallyUniformlyOn.deriv
  · exact Eventually.of_forall fun n =>
      (xiCTaylorApprox_differentiable n).differentiableOn
  · exact isOpen_univ

/-- At a pole-free point, logarithmic derivatives of the finite Xi Taylor polynomials converge to
the Xi logarithmic derivative. -/
theorem xiCTaylorApprox_logDeriv_tendsto {z : ℂ} (hz : XiC z ≠ 0) :
    Tendsto (fun n => logDeriv (xiCTaylorApprox n) z) atTop
      (nhds (logDeriv XiC z)) := by
  have hv := xiCTaylorApprox_tendstoLocallyUniformly.tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ z)
  have hd :=
    xiCTaylorApprox_deriv_tendstoLocallyUniformly.tendstoLocallyUniformlyOn.tendsto_at
      (Set.mem_univ z)
  simpa only [Function.comp_apply, logDeriv_apply] using! hd.div hv hz

/-- Original-strip to centered Xi coordinate. -/
def xiCTaylorCenteredPoint (s : ℂ) : ℂ := (s - 1 / 2) * (-I)

/-- Finite-polynomial source condition: one common upper bound eventually controls the imaginary
logarithmic derivatives of the Xi Taylor approximants at every pole-free Gaussian-rational point
of the left half-strip.  The eventual index may depend on the rational point; the bound may not. -/
def XiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove : Prop :=
  ∃ C : ℝ, ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 →
    riemannZeta (gaussianRatPoint q) ≠ 0 →
      ∀ᶠ n in atTop,
        (logDeriv (xiCTaylorApprox n)
          (xiCTaylorCenteredPoint (gaussianRatPoint q))).im ≤ C

/-- The finite Taylor bound transfers to the countable completed prime--Gamma flux lower bound. -/
theorem completedPrimeGammaGaussianRatLeftHalfBoundedBelow_of_xiCTaylor
    (htaylor : XiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove) :
    CompletedPrimeGammaGaussianRatLeftHalfBoundedBelow := by
  obtain ⟨C, hC⟩ := htaylor
  refine ⟨-C, ?_⟩
  intro q hqpos hqhalf hqzeta
  let s : ℂ := gaussianRatPoint q
  let z : ℂ := xiCTaylorCenteredPoint s
  have hcoord : 1 / 2 + z * I = s := by
    dsimp only [z, xiCTaylorCenteredPoint]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re] at hre
    dsimp only [s] at hre
    linarith
  have hXi : XiC z ≠ 0 := by
    change xi (1 / 2 + z * I) ≠ 0
    rw [hcoord]
    exact (xi_eq_zero_iff (by dsimp only [s]; exact hqpos) hs1).not.mpr hqzeta
  have htend := xiCTaylorApprox_logDeriv_tendsto hXi
  have himTend : Tendsto
      (fun n => (logDeriv (xiCTaylorApprox n) z).im) atTop
      (nhds (logDeriv XiC z).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp htend
  have hlim : (logDeriv XiC z).im ≤ C :=
    le_of_tendsto himTend (hC q hqpos hqhalf hqzeta)
  have hsource : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      (by rw [hcoord]; dsimp only [s]; exact hqpos)
      (by rw [hcoord]; exact hs1)
      (by rw [hcoord]; exact hqzeta)]
    symm
    exact logDeriv_XiC_eq_relativeResolventTrace hXi
  rw [← hsource, continuedPrimeArchSourceRelativeTrace, hcoord] at hlim
  change (-I * (infinitePrimeFlux s - logDeriv archFactor s)).im ≤ C at hlim
  simp only [mul_im, I_re, zero_mul, neg_im, I_im, neg_mul, one_mul] at hlim
  change -C ≤ (infinitePrimeFlux s - logDeriv archFactor s).re
  linarith

/-- Finite Xi-Taylor logarithmic-derivative boundedness proves RH. -/
theorem riemannHypothesis_of_xiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove
    (htaylor : XiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove) :
    RiemannHypothesis :=
  riemannHypothesis_of_completedPrimeGammaGaussianRatLeftHalfBoundedBelow
    (completedPrimeGammaGaussianRatLeftHalfBoundedBelow_of_xiCTaylor htaylor)

/-- RH supplies the uniform finite bound `1` eventually at every rational point. -/
theorem xiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove := by
  let hanti : ContinuedPrimeArchUpperAntiHerglotz :=
    continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz.mp
      (continuedPrimeArchUpperCauchyDiagonalNonnegative_of_riemannHypothesis hRH)
  refine ⟨1, ?_⟩
  intro q hqpos hqhalf hqzeta
  let s : ℂ := gaussianRatPoint q
  let z : ℂ := xiCTaylorCenteredPoint s
  have hcoord : 1 / 2 + z * I = s := by
    dsimp only [z, xiCTaylorCenteredPoint]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hzim : z.im = 1 / 2 - s.re := by
    simp [z, xiCTaylorCenteredPoint]
  have hzpos : 0 < z.im := by rw [hzim]; dsimp only [s]; linarith
  have hzhalf : z.im < 1 / 2 := by rw [hzim]; dsimp only [s]; linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re] at hre
    dsimp only [s] at hre
    linarith
  have hXi : XiC z ≠ 0 := by
    change xi (1 / 2 + z * I) ≠ 0
    rw [hcoord]
    exact (xi_eq_zero_iff (by dsimp only [s]; exact hqpos) hs1).not.mpr hqzeta
  have htend := xiCTaylorApprox_logDeriv_tendsto hXi
  have himTend : Tendsto
      (fun n => (logDeriv (xiCTaylorApprox n) z).im) atTop
      (nhds (logDeriv XiC z).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp htend
  have hsource : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      (by rw [hcoord]; dsimp only [s]; exact hqpos)
      (by rw [hcoord]; exact hs1)
      (by rw [hcoord]; exact hqzeta)]
    symm
    exact logDeriv_XiC_eq_relativeResolventTrace hXi
  have hlim : (logDeriv XiC z).im ≤ 0 := by
    rw [← hsource]
    exact hanti z hzpos hzhalf (by rw [hcoord]; exact hqzeta)
  have hev : ∀ᶠ n in atTop, (logDeriv (xiCTaylorApprox n) z).im < 1 :=
    himTend.eventually (eventually_lt_nhds (lt_of_le_of_lt hlim zero_lt_one))
  exact hev.mono fun _ hn => hn.le

/-- Exact finite Xi-Taylor logarithmic-derivative criterion for RH. -/
theorem xiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove_iff_riemannHypothesis :
    XiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove,
    xiCTaylorGaussianRatLeftHalfImEventuallyBoundedAbove_of_riemannHypothesis⟩

end

end RHTower
