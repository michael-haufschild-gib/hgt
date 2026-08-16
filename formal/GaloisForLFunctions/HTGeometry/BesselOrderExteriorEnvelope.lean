import GaloisForLFunctions.HTGeometry.BesselExteriorEnvelope
import GaloisForLFunctions.HTGeometry.BesselOrderRecurrence

/-!
# The order-one Schlaefli integral and its exterior envelope

The real order-one Schlaefli integral `∫₀^∞ e^{-s cosh t} cosh t dt` is the real restriction of the
complex Bessel carrier `besselK1C`.  Transporting the complex envelope across this identification
gives the two elementary bounds used for exterior mass decay:

`K₁(s) ≤ e^{-s} · e^{1/(2s)} · √(2π/s)`,

which supplies both the plain exponential envelope and the square-root gain in the argument.
-/

open MeasureTheory Set

namespace HTGeometry

/-- The real order-one Schlaefli integrand is the real restriction of the complex Bessel
integrand. -/
theorem ofReal_realBesselOrderKernel_one (s t : ℝ) :
    ((GaloisForLFunctions.HTGeometry.realBesselOrderKernel s 1 t : ℝ) : ℂ)
      = Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ) := by
  rw [GaloisForLFunctions.HTGeometry.realBesselOrderKernel, one_mul, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_cosh]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_cosh]

/-- The real order-one Schlaefli integral is the real restriction of `besselK1C`. -/
theorem ofReal_realModifiedBesselKOrder_one {s : ℝ} (hs : 0 < s) :
    ((GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder s 1 : ℝ) : ℂ)
      = besselK1C (s : ℂ) := by
  have hint := GaloisForLFunctions.HTGeometry.integrableOn_realBesselOrderKernel hs 1
  have hmap := Complex.ofRealCLM.integral_comp_comm hint
  rw [GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder, besselK1C]
  rw [← (by simpa only [Complex.ofRealCLM_apply] using hmap :
    (∫ t : ℝ in Ioi 0, ((GaloisForLFunctions.HTGeometry.realBesselOrderKernel s 1 t : ℝ) : ℂ))
      = ((∫ t : ℝ in Ioi 0,
          GaloisForLFunctions.HTGeometry.realBesselOrderKernel s 1 t : ℝ) : ℂ))]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
    ofReal_realBesselOrderKernel_one s t)

/-- **The order-one exterior envelope.**  The Schlaefli integral decays like `e^{-s}` with an extra
square-root gain in the argument. -/
theorem realModifiedBesselKOrder_one_le {s : ℝ} (hs : 0 < s) :
    GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder s 1
      ≤ Real.exp (-s) * Real.exp (1 / (2 * s)) * Real.sqrt (2 * Real.pi / s) := by
  have hpos := GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder_pos hs 1
  have hre : ((s : ℂ)).re = s := Complex.ofReal_re s
  have hb := norm_besselK1C_le (z := (s : ℂ)) (by rw [hre]; exact hs)
  rw [← ofReal_realModifiedBesselKOrder_one hs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos, hre] at hb
  exact hb

end HTGeometry
