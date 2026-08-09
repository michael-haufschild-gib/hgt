import GaloisForLFunctions.RHTower.HedenmalmIntervalAnomaly

/-!
# Continuous-aperture endpoint doublet of the Hedenmalm source window

The centered integer-shift anomaly belongs to a canonical continuous family, indexed by its
logarithmic aperture `L`.  Differentiation in the center gives the odd endpoint difference, while
the covariant aperture derivative `2 (d/dL + 1/2)` gives the even endpoint sum.  Thus both marked
endpoint channels are derived from the original positive source; the even channel is not an
independently adjoined observable.

At `L = log n` this family is exactly the already formalized centered integer window.  These
identities are unconditional source geometry.  They do not assert the open all-prime closed-domain
landing required by Route N.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmContinuousAperture

open HedenmalmIntervalAnomaly

variable (S : PositiveDensitySource)

/-- Continuous centered source window of logarithmic aperture `L`. -/
def centeredApertureWindow (L x : ℝ) : ℝ :=
  Real.exp (-L / 2) *
    (S.mass * (S.cdfFun (x + L / 2) - S.cdfFun (x - L / 2)))

/-- Odd marked endpoint channel, obtained by differentiating the center. -/
def centeredApertureOddEndpoint (L x : ℝ) : ℝ :=
  Real.exp (-L / 2) * (S.k (x + L / 2) - S.k (x - L / 2))

/-- Even marked endpoint channel, obtained by the covariant aperture derivative. -/
def centeredApertureEvenEndpoint (L x : ℝ) : ℝ :=
  Real.exp (-L / 2) * (S.k (x + L / 2) + S.k (x - L / 2))

/-- For nonnegative aperture, the CDF definition is the literal centered interval mass. -/
theorem centeredApertureWindow_eq_intervalMass {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    centeredApertureWindow S L x =
      Real.exp (-L / 2) * intervalMass S (x - L / 2) (x + L / 2) := by
  have hle : x - L / 2 ≤ x + L / 2 := by linarith
  rw [centeredApertureWindow, mass_mul_cdfFun_sub S hle]

/-- Raw center derivative in normalized-density coordinates. -/
theorem hasDerivAt_centeredApertureWindow_center_normalized (L x : ℝ) :
    HasDerivAt (fun y => centeredApertureWindow S L y)
      (Real.exp (-L / 2) * S.mass *
        (S.normalized (x + L / 2) - S.normalized (x - L / 2))) x := by
  have hu : HasDerivAt (fun y : ℝ => S.cdfFun (y + L / 2))
      (S.normalized (x + L / 2)) x :=
    by
      simpa only [Function.comp_def, id_eq, mul_one] using
        (S.hasDerivAt_cdfFun (x + L / 2)).comp x
          ((hasDerivAt_id x).add_const (L / 2))
  have hl : HasDerivAt (fun y : ℝ => S.cdfFun (y - L / 2))
      (S.normalized (x - L / 2)) x :=
    by
      simpa only [Function.comp_def, id_eq, mul_one] using
        (S.hasDerivAt_cdfFun (x - L / 2)).comp x
          ((hasDerivAt_id x).sub_const (L / 2))
  simpa only [centeredApertureWindow, Pi.sub_apply, mul_assoc] using
    (hu.sub hl).const_mul (Real.exp (-L / 2) * S.mass)

/-- **Center derivative law.** The center derivative is exactly the odd endpoint difference. -/
theorem hasDerivAt_centeredApertureWindow_center (L x : ℝ) :
    HasDerivAt (fun y => centeredApertureWindow S L y)
      (centeredApertureOddEndpoint S L x) x := by
  convert hasDerivAt_centeredApertureWindow_center_normalized S L x using 1
  simp only [centeredApertureOddEndpoint, PositiveDensitySource.normalized]
  field_simp [S.mass_ne_zero]

/-- Raw aperture derivative before cancelling the source mass. -/
theorem hasDerivAt_centeredApertureWindow_aperture_normalized (L x : ℝ) :
    HasDerivAt (fun M => centeredApertureWindow S M x)
      (Real.exp (-L / 2) * (-1 / 2) *
          (S.mass * (S.cdfFun (x + L / 2) - S.cdfFun (x - L / 2))) +
        Real.exp (-L / 2) *
          (S.mass *
            (S.normalized (x + L / 2) * (1 / 2) -
              S.normalized (x - L / 2) * (-1 / 2)))) L := by
  have hneg : HasDerivAt (fun M : ℝ => -M / 2) (-1 / 2) L := by
    simpa using (hasDerivAt_id L).neg.div_const 2
  have hexp : HasDerivAt (fun M : ℝ => Real.exp (-M / 2))
      (Real.exp (-L / 2) * (-1 / 2)) L :=
    by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_exp (-L / 2)).comp L hneg
  have huArg : HasDerivAt (fun M : ℝ => x + M / 2) (1 / 2) L := by
    simpa using ((hasDerivAt_id L).div_const 2).const_add x
  have hlArg : HasDerivAt (fun M : ℝ => x - M / 2) (-1 / 2) L := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      (hasDerivAt_const (x := L) x).sub ((hasDerivAt_id L).div_const 2)
  have hu : HasDerivAt (fun M : ℝ => S.cdfFun (x + M / 2))
      (S.normalized (x + L / 2) * (1 / 2)) L :=
    by
      simpa only [Function.comp_def] using
        (S.hasDerivAt_cdfFun (x + L / 2)).comp L huArg
  have hl : HasDerivAt (fun M : ℝ => S.cdfFun (x - M / 2))
      (S.normalized (x - L / 2) * (-1 / 2)) L :=
    by
      simpa only [Function.comp_def] using
        (S.hasDerivAt_cdfFun (x - L / 2)).comp L hlArg
  have hmass := (hu.sub hl).const_mul S.mass
  convert hexp.mul hmass using 1
  · funext M
    simp only [centeredApertureWindow, Pi.mul_apply, Pi.sub_apply]
  · simp only [Pi.sub_apply]

/-- **Aperture derivative law.** The covariant derivative separates half-density decay from the
even endpoint sum. -/
theorem hasDerivAt_centeredApertureWindow_aperture (L x : ℝ) :
    HasDerivAt (fun M => centeredApertureWindow S M x)
      ((-1 / 2) * centeredApertureWindow S L x +
        (1 / 2) * centeredApertureEvenEndpoint S L x) L := by
  convert hasDerivAt_centeredApertureWindow_aperture_normalized S L x using 1
  simp only [centeredApertureWindow, centeredApertureEvenEndpoint,
    PositiveDensitySource.normalized]
  field_simp [S.mass_ne_zero]
  ring

/-- Exact covariant-width recovery of the even endpoint channel. -/
theorem two_mul_deriv_centeredApertureWindow_add_half (L x : ℝ) :
    2 * (deriv (fun M => centeredApertureWindow S M x) L +
        (1 / 2) * centeredApertureWindow S L x) =
      centeredApertureEvenEndpoint S L x := by
  rw [(hasDerivAt_centeredApertureWindow_aperture S L x).deriv]
  ring

/-- At integer logarithmic apertures, the continuous family is the original centered anomaly
window. -/
theorem centeredApertureWindow_log_nat_eq_centeredWindow {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    centeredApertureWindow S (Real.log n) x = centeredWindow S n x := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hrpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) = Real.exp (-Real.log n / 2) := by
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  rw [centeredApertureWindow_eq_intervalMass S hlog, centeredWindow, hrpow]

end HedenmalmContinuousAperture

end

end RHTower
