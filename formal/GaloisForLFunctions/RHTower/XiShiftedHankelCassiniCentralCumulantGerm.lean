import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoalescingXiSourceRate
import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniThetaCumulantContact
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureBalance

/-!
# The central cumulant germ of the Route-U Euler contact

The degree-one Route-U contact numerator has a sixth-order central germ.  This file identifies
that germ exactly: it is the negative of the old prime--archimedean first Hankel minor, hence the
negative of one universal sixth-versus-fourth cumulant discriminant.

If `κ₂`, `κ₄`, and `κ₆` are the centered cumulants of the normalized completed theta source, put

`Δ₆₄ = 3 κ₂ κ₆ - 10 κ₄²`.

Then

`N(t) / t⁶ -> -Δ₆₄ / 45`

as `t -> 0+`.  Thus the center obstruction previously isolated in the prime--archimedean Hankel
lane is literally the infinitesimal boundary orientation of the Route-U Cassini flow.  This is an
actual source/divisor limit, not a formal Taylor placeholder.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Variance of the normalized completed theta source at the central tilt. -/
def thetaCuspCentralCumulantTwo : ℝ :=
  thetaCuspNormalizedEvenMoment 1

/-- Fourth centered cumulant of the normalized completed theta source. -/
def thetaCuspCentralCumulantFour : ℝ :=
  thetaCuspNormalizedEvenMoment 2 -
    3 * thetaCuspNormalizedEvenMoment 1 ^ (2 : ℕ)

/-- Sixth centered cumulant of the normalized completed theta source. -/
def thetaCuspCentralCumulantSix : ℝ :=
  thetaCuspNormalizedEvenMoment 3 -
    15 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 2 +
    30 * thetaCuspNormalizedEvenMoment 1 ^ (3 : ℕ)

/-- Universal sixth-versus-fourth cumulant discriminant governing the central Route-U germ. -/
def thetaCuspCentralCumulantDiscriminant : ℝ :=
  3 * thetaCuspCentralCumulantTwo * thetaCuspCentralCumulantSix -
    10 * thetaCuspCentralCumulantFour ^ (2 : ℕ)

/-- The cumulant discriminant is exactly the normalized theta sixth-moment cubic. -/
theorem thetaCuspCentralCumulantDiscriminant_eq_moments :
    thetaCuspCentralCumulantDiscriminant =
      3 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 +
        15 * thetaCuspNormalizedEvenMoment 1 ^ (2 : ℕ) *
          thetaCuspNormalizedEvenMoment 2 -
        10 * thetaCuspNormalizedEvenMoment 2 ^ (2 : ℕ) := by
  unfold thetaCuspCentralCumulantDiscriminant
    thetaCuspCentralCumulantTwo thetaCuspCentralCumulantFour
    thetaCuspCentralCumulantSix
  ring

/-- The central Route-U discriminant is the zero-aperture Gaussian ratio curvature, multiplied
by the positive normalization `m₁ m₂ / m₀²`.  Thus the Route-U central germ and the old Gaussian
aperture boundary problem are not two gates: they are the same source scalar. -/
theorem thetaCuspCentralCumulantDiscriminant_eq_apertureBalance_zero :
    thetaCuspCentralCumulantDiscriminant =
      thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 2 /
          thetaCuspRawEvenMoment 0 ^ (2 : ℕ) *
        thetaCuspGaussianApertureBalance 0 := by
  rw [thetaCuspCentralCumulantDiscriminant_eq_moments,
    thetaCuspGaussianApertureBalance_zero]
  simp only [thetaCuspNormalizedEvenMoment]
  have h0 := (thetaCuspRawEvenMoment_pos 0).ne'
  have h1 := (thetaCuspRawEvenMoment_pos 1).ne'
  have h2 := (thetaCuspRawEvenMoment_pos 2).ne'
  field_simp [h0, h1, h2]

/-- Strict positivity of the central Route-U discriminant is exactly strict positivity of the
zero-aperture Gaussian balance. -/
theorem thetaCuspCentralCumulantDiscriminant_pos_iff_apertureBalance_zero_pos :
    0 < thetaCuspCentralCumulantDiscriminant ↔
      0 < thetaCuspGaussianApertureBalance 0 := by
  rw [thetaCuspCentralCumulantDiscriminant_eq_apertureBalance_zero]
  have hfactor :
      0 < thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 2 /
        thetaCuspRawEvenMoment 0 ^ (2 : ℕ) := by
    exact div_pos
      (mul_pos (thetaCuspRawEvenMoment_pos 1)
        (thetaCuspRawEvenMoment_pos 2))
      (sq_pos_of_pos (thetaCuspRawEvenMoment_pos 0))
  exact mul_pos_iff_of_pos_left hfactor

/-- Nonnegativity has the same exact boundary identification. -/
theorem thetaCuspCentralCumulantDiscriminant_nonneg_iff_apertureBalance_zero_nonneg :
    0 ≤ thetaCuspCentralCumulantDiscriminant ↔
      0 ≤ thetaCuspGaussianApertureBalance 0 := by
  rw [thetaCuspCentralCumulantDiscriminant_eq_apertureBalance_zero]
  have hfactor :
      0 < thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 2 /
        thetaCuspRawEvenMoment 0 ^ (2 : ℕ) := by
    exact div_pos
      (mul_pos (thetaCuspRawEvenMoment_pos 1)
        (thetaCuspRawEvenMoment_pos 2))
      (sq_pos_of_pos (thetaCuspRawEvenMoment_pos 0))
  exact mul_nonneg_iff_of_pos_left hfactor

/-- The central prime--archimedean first minor is one `360`th of the cumulant discriminant. -/
theorem normalizedPrimeArch_firstHankelMinor_scaled_eq_centralCumulantDiscriminant :
    360 * (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 1 ^ (2 : ℕ)) =
      thetaCuspCentralCumulantDiscriminant := by
  rw [thetaCuspCentralCumulantDiscriminant_eq_moments]
  exact normalizedPrimeArch_firstHankelMinor_scaled_eq_thetaCuspMoments

/-- The moving degree-one shifted minor reaches the old central first minor from the right. -/
theorem tendsto_xiShiftedDegreeOneHankelMinor_nhdsGE_zero :
    Tendsto xiShiftedDegreeOneHankelMinor (𝓝[≥] (0 : ℝ))
      (𝓝 (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 1 ^ (2 : ℕ))) := by
  have hreal (m : ℕ) :
      Tendsto (fun y : ℝ => (xiShiftedReciprocalMoment y m).re)
        (𝓝[≥] (0 : ℝ)) (𝓝 (normalizedPrimeArchMoment m)) := by
    have h := (Complex.continuous_re.tendsto
      (normalizedPrimeArchMoment m : ℂ)).comp
        (tendsto_xiShiftedReciprocalMoment_nhdsGE_zero m)
    simpa [Function.comp_def] using h
  have h0 := hreal 0
  have h1 := hreal 1
  have h2 := hreal 2
  have hminor := (h0.mul h2).sub (h1.pow 2)
  change Tendsto
    (fun y : ℝ =>
      (xiShiftedReciprocalMoment y 0).re *
          (xiShiftedReciprocalMoment y 2).re -
        (xiShiftedReciprocalMoment y 1).re ^ (2 : ℕ))
    (𝓝[≥] (0 : ℝ))
    (𝓝 (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
      normalizedPrimeArchMoment 1 ^ (2 : ℕ)))
  exact hminor

/-- Exact central asymptotic of the actual Route-U theta contact numerator. -/
theorem tendsto_thetaCuspCassiniEulerContactNumerator_div_pow_six :
    Tendsto
      (fun t : ℝ => thetaCuspCassiniEulerContactNumerator t / t ^ (6 : ℕ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-8 * (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 1 ^ (2 : ℕ)))) := by
  have ht2 : Tendsto (fun t : ℝ => t ^ (2 : ℕ))
      (𝓝[>] (0 : ℝ)) (𝓝[≥] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : ContinuousAt (fun t : ℝ => t ^ (2 : ℕ)) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · exact Eventually.of_forall fun t => sq_nonneg t
  have hminor := tendsto_xiShiftedDegreeOneHankelMinor_nhdsGE_zero.comp ht2
  have hscaled :
      Tendsto (fun t : ℝ => -8 * xiShiftedDegreeOneHankelMinor (t ^ (2 : ℕ)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (-8 * (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ (2 : ℕ)))) :=
    tendsto_const_nhds.mul hminor
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht0 ht1
  change 0 < t at ht0
  change t < 1 at ht1
  rw [thetaCuspCassiniEulerContactNumerator_eq_neg_eight_mul_minor ht0 ht1]
  field_simp [ht0.ne']

/-- **Central-germ bridge.**  Route-U radial orientation is governed infinitesimally by the
same `3 κ₂ κ₆ - 10 κ₄²` discriminant as the old first prime--archimedean Hankel face. -/
theorem tendsto_thetaCuspCassiniEulerContactNumerator_div_pow_six_eq_cumulants :
    Tendsto
      (fun t : ℝ => thetaCuspCassiniEulerContactNumerator t / t ^ (6 : ℕ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-thetaCuspCentralCumulantDiscriminant / 45)) := by
  have hlimit :
    -8 * (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 1 ^ (2 : ℕ)) =
        -(360 * (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ (2 : ℕ))) / 45 := by ring
  have hlimit' :
      -8 * (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ (2 : ℕ)) =
        -thetaCuspCentralCumulantDiscriminant / 45 := by
    calc
      _ = -(360 * (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ (2 : ℕ))) / 45 := hlimit
      _ = -thetaCuspCentralCumulantDiscriminant / 45 := by
        rw [normalizedPrimeArch_firstHankelMinor_scaled_eq_centralCumulantDiscriminant]
  simpa only [hlimit'] using
    tendsto_thetaCuspCassiniEulerContactNumerator_div_pow_six

/-- Positive central cumulant discriminant excludes all sufficiently small positive degree-one
Route-U contacts by forcing the actual contact numerator strictly negative. -/
theorem eventually_thetaCuspCassiniEulerContactNumerator_neg_of_centralDiscriminant_pos
    (hdisc : 0 < thetaCuspCentralCumulantDiscriminant) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      thetaCuspCassiniEulerContactNumerator t < 0 := by
  have hnormalized :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        thetaCuspCassiniEulerContactNumerator t / t ^ (6 : ℕ) < 0 :=
    tendsto_thetaCuspCassiniEulerContactNumerator_div_pow_six_eq_cumulants
      |>.eventually_lt_const
        (div_neg_of_neg_of_pos (neg_lt_zero.mpr hdisc) (by norm_num))
  filter_upwards [hnormalized, self_mem_nhdsWithin] with t hquot ht
  change 0 < t at ht
  have hpow : 0 < t ^ (6 : ℕ) := pow_pos ht 6
  rcases div_neg_iff.mp hquot with hbad | hgood
  · exact (not_lt_of_ge hpow.le hbad.2).elim
  · exact hgood.1

end

end RHTower
