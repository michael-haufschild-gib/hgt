import GaloisForLFunctions.RHTower.ProlateBandEigenMass
import GaloisForLFunctions.RHTower.ProlateCanonicalRadialFamily
import GaloisForLFunctions.RHTower.ProlateSignedLeakageOrdering

/-!
# Exact leakage mass identity for the canonical radial family

The endpoint-normalized radial profile is a scalar multiple of the global band eigenfunction.
Consequently its exterior-to-interior mass ratio is exactly the signed spectral leakage divided by
the squared signed eigenvalue.  This is the normalization-independent bridge used by tunneling
estimates.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- Exact exterior mass of the canonical endpoint-normalized radial profile at every live
aperture. -/
theorem integral_outside_sq_signedModeRadialData_eq_leakage_ratio
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    (∫ x in (Icc (-1 : ℝ) 1)ᶜ, (signedModeRadialData a n).R x ^ 2) =
      (∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).R x ^ 2) *
        evenProlateSignedLeakage a n / evenProlateSignedValue a n ^ 2 := by
  let D := signedModeRadialData a n
  have hD := signedModeRadialData_isExact ha n hvalue
  rcases hD with ⟨hPhi, _hPhi0, _hPhiEven, _hPhi1, hRdef, hR, _hREven, _hR1,
    hband, _hprolate, _hs, _hs0, _hend, _hode⟩
  have hc : 0 < signedModeRadialBandwidth a := by
    simp only [signedModeRadialBandwidth]
    positivity
  have hRband : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) D.R x =
        evenProlateSignedValue a n ^ 2 * D.R x := by
    rw [hRdef]
    exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hband
  have hmass :=
    GaloisForLFunctions.RHTower.integral_outside_sq_global_band_eigen_eq_integral_mul_ratio
      hc (pow_ne_zero 2 hvalue) hR.continuous hRband
  simpa only [D, evenProlateSignedLeakage] using hmass

end RHTower

end
