import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedHorizonSturmOpticalForm

/-!
# Integrated mixed-horizon Birmingham--Mokhtari optical form

The exact mixed BM radial operator already has a real Sturm--Liouville form on `0 < z < 1`.
This module upgrades its jet-level optical identity to a global identity on every compact radial
interval `0 < a ≤ b < 1`.

For a twice differentiable forced solution `y`, define radial optical current

`J(z) = p(z) Im(conj(y(z)) y'(z))`.

Then

`J(b) - J(a) = integral_a^b w(z) Im(conj(y(z)) forcing(z)) dz`.

This is the exact finite-radius Green identity needed before horizon and AdS-boundary limits.  It
does not assert those endpoint limits, identify the forcing with the complete nonlinear augmented
Einstein source, or impose any Xi-divisor condition.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
-/

open Complex Real
open scoped Interval

namespace RHTower

noncomputable section

/-- Mixed BM radial optical current `p Im(conj(y) y')`, written in real coordinates. -/
def d4BMMixedHorizonOpticalCurrent
    (n k : ℕ) (y dy : ℝ → ℂ) (z : ℝ) : ℝ :=
  d4BMMixedHorizonSturmP n k z *
    ((y z).re * (dy z).im - (y z).im * (dy z).re)

/-- Derivative of the exact mixed BM optical current from first and second solution jets. -/
theorem hasDerivAt_d4BMMixedHorizonOpticalCurrent
    (n k : ℕ) (y dy : ℝ → ℂ) (z : ℝ) (ddy : ℂ)
    (hz0 : 0 < z) (hz1 : z < 1)
    (hy : HasDerivAt y (dy z) z)
    (hdy : HasDerivAt dy ddy z) :
    HasDerivAt (d4BMMixedHorizonOpticalCurrent n k y dy)
      (d4BMMixedHorizonOpticalCurrentDerivativeJet
        n k z (y z) (dy z) ddy) z := by
  have hyre : HasDerivAt (fun x : ℝ => (y x).re) (dy z).re z :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt z hy
  have hyim : HasDerivAt (fun x : ℝ => (y x).im) (dy z).im z :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt z hy
  have hdyre : HasDerivAt (fun x : ℝ => (dy x).re) ddy.re z :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt z hdy
  have hdyim : HasDerivAt (fun x : ℝ => (dy x).im) ddy.im z :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt z hdy
  have hpair : HasDerivAt
      (fun x : ℝ => (y x).re * (dy x).im - (y x).im * (dy x).re)
      ((dy z).re * (dy z).im + (y z).re * ddy.im -
        ((dy z).im * (dy z).re + (y z).im * ddy.re)) z :=
    (hyre.mul hdyim).sub (hyim.mul hdyre)
  have hp := hasDerivAt_d4BMMixedHorizonSturmP n k hz0 hz1
  have hprod : HasDerivAt
      (fun x : ℝ => d4BMMixedHorizonSturmP n k x *
        ((y x).re * (dy x).im - (y x).im * (dy x).re))
      ((d4BMMixedHorizonSturmWeight n k z *
          d4BMMixedHorizonSturmDrift n k z) *
          ((y z).re * (dy z).im - (y z).im * (dy z).re) +
        d4BMMixedHorizonSturmP n k z *
          ((dy z).re * (dy z).im + (y z).re * ddy.im -
            ((dy z).im * (dy z).re + (y z).im * ddy.re))) z := by
    simpa only [Pi.mul_apply] using! hp.mul hpair
  apply hprod.congr_deriv
  simp [d4BMMixedHorizonOpticalCurrentDerivativeJet, Complex.mul_im]
  ring

/-- **Integrated mixed BM optical theorem.** Source modal work equals outer-minus-inner radial
optical current on every compact interval inside the physical radial domain. -/
theorem d4BMMixedHorizonIntegratedOpticalIdentity
    (n k : ℕ) (chi : ℝ) (a b : ℝ)
    (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b < 1)
    (y dy ddy forcing : ℝ → ℂ)
    (hy : ∀ z ∈ Set.uIcc a b, HasDerivAt y (dy z) z)
    (hdy : ∀ z ∈ Set.uIcc a b, HasDerivAt dy (ddy z) z)
    (hforcing : ∀ z ∈ Set.uIcc a b,
      d4BMMixedHorizonHypergeometricJet
        n k chi z (y z) (dy z) (ddy z) = forcing z)
    (hint : IntervalIntegrable
      (fun z : ℝ => d4BMMixedHorizonSturmWeight n k z *
        (((starRingEnd ℂ) (y z)) * forcing z).im)
      MeasureTheory.volume a b) :
    (∫ z in a..b, d4BMMixedHorizonSturmWeight n k z *
        (((starRingEnd ℂ) (y z)) * forcing z).im) =
      d4BMMixedHorizonOpticalCurrent n k y dy b -
        d4BMMixedHorizonOpticalCurrent n k y dy a := by
  have hz0 : ∀ z ∈ Set.uIcc a b, 0 < z := by
    intro z hz
    rw [Set.uIcc_of_le hab] at hz
    exact lt_of_lt_of_le ha0 hz.1
  have hz1 : ∀ z ∈ Set.uIcc a b, z < 1 := by
    intro z hz
    rw [Set.uIcc_of_le hab] at hz
    exact lt_of_le_of_lt hz.2 hb1
  have hcurrent : ∀ z ∈ Set.uIcc a b,
      HasDerivAt (d4BMMixedHorizonOpticalCurrent n k y dy)
        (d4BMMixedHorizonSturmWeight n k z *
          (((starRingEnd ℂ) (y z)) * forcing z).im) z := by
    intro z hz
    have hlocal := d4BMMixedHorizonOpticalCurrentDerivativeJet_eq_source
      n k chi (hz0 z hz) (hz1 z hz) (y z) (dy z) (ddy z) (forcing z)
      (hforcing z hz)
    simpa [hlocal] using
      hasDerivAt_d4BMMixedHorizonOpticalCurrent n k y dy z (ddy z)
        (hz0 z hz) (hz1 z hz) (hy z hz) (hdy z hz)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hcurrent hint

end

end RHTower
