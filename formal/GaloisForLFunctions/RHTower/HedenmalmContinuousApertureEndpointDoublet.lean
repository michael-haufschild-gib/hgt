import GaloisForLFunctions.RHTower.HedenmalmThetaIntervalTransform
import GaloisForLFunctions.RHTower.HedenmalmPrimeNormalSolderingCurvature

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

open HedenmalmIntervalAnomaly HedenmalmQuantile HedenmalmThetaSource

variable (S : PositiveDensitySource)

/-- Scalar derivative predicate using the canonical normed-algebra module structure on `ℝ`. -/
abbrev SourceHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ _ (NormedAlgebra.toNormedSpace ℝ).toModule _ _ f f' x

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
    SourceHasDerivAt (fun y => centeredApertureWindow S L y)
      (Real.exp (-L / 2) * S.mass *
        (S.normalized (x + L / 2) - S.normalized (x - L / 2))) x := by
  have hu : SourceHasDerivAt (fun y : ℝ => S.cdfFun (y + L / 2))
      (S.normalized (x + L / 2)) x :=
    by
      simpa only [Function.comp_def, id_eq, mul_one] using
        (S.hasDerivAt_cdfFun (x + L / 2)).comp x
          ((hasDerivAt_id x).add_const (L / 2))
  have hl : SourceHasDerivAt (fun y : ℝ => S.cdfFun (y - L / 2))
      (S.normalized (x - L / 2)) x :=
    by
      simpa only [Function.comp_def, id_eq, mul_one] using
        (S.hasDerivAt_cdfFun (x - L / 2)).comp x
          ((hasDerivAt_id x).sub_const (L / 2))
  simpa only [centeredApertureWindow, Pi.sub_apply, mul_assoc] using
    (hu.sub hl).const_mul (Real.exp (-L / 2) * S.mass)

/-- **Center derivative law.** The center derivative is exactly the odd endpoint difference. -/
theorem hasDerivAt_centeredApertureWindow_center (L x : ℝ) :
    SourceHasDerivAt (fun y => centeredApertureWindow S L y)
      (centeredApertureOddEndpoint S L x) x := by
  convert hasDerivAt_centeredApertureWindow_center_normalized S L x using 1
  simp only [centeredApertureOddEndpoint, PositiveDensitySource.normalized]
  field_simp [S.mass_ne_zero]

/-- Raw aperture derivative before cancelling the source mass. -/
theorem hasDerivAt_centeredApertureWindow_aperture_normalized (L x : ℝ) :
    SourceHasDerivAt (fun M => centeredApertureWindow S M x)
      (Real.exp (-L / 2) * (-1 / 2) *
          (S.mass * (S.cdfFun (x + L / 2) - S.cdfFun (x - L / 2))) +
        Real.exp (-L / 2) *
          (S.mass *
            (S.normalized (x + L / 2) * (1 / 2) -
              S.normalized (x - L / 2) * (-1 / 2)))) L := by
  have hneg : SourceHasDerivAt (fun M : ℝ => -M / 2) (-1 / 2) L := by
    simpa using (hasDerivAt_id L).neg.div_const 2
  have hexp : SourceHasDerivAt (fun M : ℝ => Real.exp (-M / 2))
      (Real.exp (-L / 2) * (-1 / 2)) L :=
    by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_exp (-L / 2)).comp L hneg
  have huArg : SourceHasDerivAt (fun M : ℝ => x + M / 2) (1 / 2) L := by
    simpa using ((hasDerivAt_id L).div_const 2).const_add x
  have hlArg : SourceHasDerivAt (fun M : ℝ => x - M / 2) (-1 / 2) L := by
    have h := (hasDerivAt_const (x := L) x).sub ((hasDerivAt_id L).div_const 2)
    refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with M
    rfl
  have hu : SourceHasDerivAt (fun M : ℝ => S.cdfFun (x + M / 2))
      (S.normalized (x + L / 2) * (1 / 2)) L :=
    by
      simpa only [Function.comp_def] using
        (S.hasDerivAt_cdfFun (x + L / 2)).comp L huArg
  have hl : SourceHasDerivAt (fun M : ℝ => S.cdfFun (x - M / 2))
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
    SourceHasDerivAt (fun M => centeredApertureWindow S M x)
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

/-! ### Theta-source endpoint transforms -/

/-- Marked half-character at continuous aperture `L`.  Its two coordinates are the translated
source factors of the two centered endpoints. -/
def centeredApertureMarkedCharacter (L : ℝ) (z : ℂ) : ℂ × ℂ :=
  let c : ℂ := (Real.exp (-L / 2) : ℝ)
  let a : ℂ := ((L / 2 : ℝ) : ℂ)
  (c * Complex.exp (Complex.I * z * a),
    c * Complex.exp (-(Complex.I * z * a)))

theorem integrable_shifted_thetaSource_sourceChar {a : ℝ} {z : ℂ} (hz : |z.im| < 1) :
    Integrable
      (fun x : ℝ => (thetaSource.k (x + a) : ℂ) * sourceChar z x)
      (volume : Measure ℝ) := by
  have hk : Integrable (fun x : ℝ => (thetaSource.k x : ℂ) * sourceChar z x)
      (volume : Measure ℝ) :=
    integrable_k_sourceChar thetaSource (hasShiftedTail_thetaSource hz)
  have hcomp : Integrable
      (fun x : ℝ => (thetaSource.k (x + a) : ℂ) * sourceChar z (x + a))
      (volume : Measure ℝ) := hk.comp_add_right a
  have hpt : ∀ x : ℝ, (thetaSource.k (x + a) : ℂ) * sourceChar z x =
      Complex.exp (-(Complex.I * z * (a : ℂ))) *
        ((thetaSource.k (x + a) : ℂ) * sourceChar z (x + a)) := by
    intro x
    exact shifted_char_factor (thetaSource.k (x + a) : ℂ) a z x
  exact (hcomp.const_mul _).congr
    (Filter.Eventually.of_forall fun x => (hpt x).symm)

/-- **Even endpoint divisor factorization.** The aperture-covariant even endpoint carries exactly
the same completed theta divisor as the original odd interval anomaly. -/
theorem integral_centeredApertureEvenEndpoint_sourceChar {L : ℝ} {z : ℂ}
    (hz : |z.im| < 1) :
    (∫ x : ℝ,
        ((centeredApertureEvenEndpoint thetaSource L x : ℝ) : ℂ) * sourceChar z x) =
      hedenmalmPrimeEvenSolder (centeredApertureMarkedCharacter L z) * XiC z := by
  have hu := integrable_shifted_thetaSource_sourceChar (a := L / 2) hz
  have hl := integrable_shifted_thetaSource_sourceChar (a := -(L / 2)) hz
  have hpt : ∀ x : ℝ,
      ((centeredApertureEvenEndpoint thetaSource L x : ℝ) : ℂ) * sourceChar z x =
        ((Real.exp (-L / 2) : ℝ) : ℂ) *
          (((thetaSource.k (x + L / 2) : ℂ) * sourceChar z x) +
            ((thetaSource.k (x + (-(L / 2))) : ℂ) * sourceChar z x)) := by
    intro x
    simp only [centeredApertureEvenEndpoint]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_add hu hl,
    integral_shifted_k_sourceChar hz, integral_shifted_k_sourceChar hz]
  have hphase :
      Complex.exp (-(Complex.I * z * ((-(L / 2) : ℝ) : ℂ))) =
        Complex.exp (Complex.I * z * ((L / 2 : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  simp only [centeredApertureMarkedCharacter, hedenmalmPrimeEvenSolder]
  rw [hphase]
  ring

/-- **Odd endpoint divisor factorization.** Center differentiation gives the marked odd soldering,
up to the fixed unitary phase `-i`, with the same completed theta divisor. -/
theorem integral_centeredApertureOddEndpoint_sourceChar {L : ℝ} {z : ℂ}
    (hz : |z.im| < 1) :
    (∫ x : ℝ,
        ((centeredApertureOddEndpoint thetaSource L x : ℝ) : ℂ) * sourceChar z x) =
      -Complex.I * hedenmalmPrimeOddSolder (centeredApertureMarkedCharacter L z) * XiC z := by
  have hu := integrable_shifted_thetaSource_sourceChar (a := L / 2) hz
  have hl := integrable_shifted_thetaSource_sourceChar (a := -(L / 2)) hz
  have hpt : ∀ x : ℝ,
      ((centeredApertureOddEndpoint thetaSource L x : ℝ) : ℂ) * sourceChar z x =
        ((Real.exp (-L / 2) : ℝ) : ℂ) *
          (((thetaSource.k (x + L / 2) : ℂ) * sourceChar z x) -
            ((thetaSource.k (x + (-(L / 2))) : ℂ) * sourceChar z x)) := by
    intro x
    simp only [centeredApertureOddEndpoint]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_sub hu hl,
    integral_shifted_k_sourceChar hz, integral_shifted_k_sourceChar hz]
  have hphase :
      Complex.exp (-(Complex.I * z * ((-(L / 2) : ℝ) : ℂ))) =
        Complex.exp (Complex.I * z * ((L / 2 : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  simp only [centeredApertureMarkedCharacter, hedenmalmPrimeOddSolder]
  rw [hphase]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- At prime logarithmic aperture, the continuous source marker is the prime-normal marked
half-character. -/
theorem centeredApertureMarkedCharacter_log_prime_eq (p : Nat.Primes) (z : ℂ) :
    centeredApertureMarkedCharacter (Real.log (p.1 : ℕ)) z =
      hedenmalmMarkedPrimeHalfCharacter p.1 z := by
  have hp0 : (0 : ℝ) < (p.1 : ℕ) := by exact_mod_cast p.2.pos
  have hc : Real.exp (-Real.log (p.1 : ℕ) / 2) = hedenmalmPrimeHalfDensity p.1 := by
    rw [hedenmalmPrimeHalfDensity, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0,
      ← Real.exp_neg]
    congr 1
    ring
  ext <;>
    simp only [centeredApertureMarkedCharacter, hedenmalmMarkedPrimeHalfCharacter, hc] <;>
    congr 1 <;> ring

/-- Prime even endpoint transform in the exact marked carrier. -/
theorem integral_primeEvenEndpoint_sourceChar {p : Nat.Primes} {z : ℂ}
    (hz : |z.im| < 1) :
    (∫ x : ℝ,
        ((centeredApertureEvenEndpoint thetaSource (Real.log (p.1 : ℕ)) x : ℝ) : ℂ) *
          sourceChar z x) =
      hedenmalmPrimeEvenSolder (hedenmalmMarkedPrimeHalfCharacter p.1 z) * XiC z := by
  rw [integral_centeredApertureEvenEndpoint_sourceChar hz,
    centeredApertureMarkedCharacter_log_prime_eq]

/-- Prime odd endpoint transform in the exact marked carrier. -/
theorem integral_primeOddEndpoint_sourceChar {p : Nat.Primes} {z : ℂ}
    (hz : |z.im| < 1) :
    (∫ x : ℝ,
        ((centeredApertureOddEndpoint thetaSource (Real.log (p.1 : ℕ)) x : ℝ) : ℂ) *
          sourceChar z x) =
      -Complex.I * hedenmalmPrimeOddSolder
          (hedenmalmMarkedPrimeHalfCharacter p.1 z) * XiC z := by
  rw [integral_centeredApertureOddEndpoint_sourceChar hz,
    centeredApertureMarkedCharacter_log_prime_eq]

/-- **Source-derived radial endpoint energy.** After removing the common `XiC` divisor, the
prime endpoint doublet has exact energy `4/p cosh(Im z log p)`, with no dependence on `Re z`. -/
theorem prime_endpointSymbol_energy_eq_cosh (p : Nat.Primes) (z : ℂ) :
    ‖hedenmalmPrimeEvenSolder (centeredApertureMarkedCharacter (Real.log (p.1 : ℕ)) z)‖ ^ 2 +
        ‖-Complex.I * hedenmalmPrimeOddSolder
          (centeredApertureMarkedCharacter (Real.log (p.1 : ℕ)) z)‖ ^ 2 =
      4 / (p.1 : ℕ) * Real.cosh (z.im * Real.log (p.1 : ℕ)) := by
  rw [centeredApertureMarkedCharacter_log_prime_eq]
  simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using
    hedenmalmPrime_evenOdd_character_energy_eq_cosh p z

end HedenmalmContinuousAperture

end

end RHTower
