import GaloisForLFunctions.RHTower.GammaSewnMobiusValuationContraction
import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric

/-!
# Gamma-sewn cubic-defect Szegő-angle universality

The cubic defect between the Gamma-sewn Möbius valuation feature and its source is only a
positive radial rescaling of the source ray.  Its completed valuation Gram therefore changes
radial masses but preserves every normalized Möbius--Szegő aperture angle and the corresponding
real-disk pseudohyperbolic distance.
-/

namespace RHTower

noncomputable section

/-- Positive radial loss multiplying the unsewn source ray in the Gamma-sewing defect. -/
def gammaSewnMobiusCubicDefectRadialGain
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  1 - gammaSewnMobiusValuationContractionMultiplier x p

/-- Difference between the Gamma-sewn valuation feature and its unsewn Möbius--Schur source. -/
def gammaSewnMobiusContinuousApertureCubicDefect
    (x : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  gammaSewnMobiusContinuousApertureFeature x p e -
    xiMobiusPrimeSchurContinuousForwardDifference x p e

/-- Completed valuation Gram of two cubic Gamma-sewing defect rays. -/
def gammaSewnMobiusContinuousApertureCubicDefectMetric
    (a b : ℝ) (p : Nat.Primes) : ℝ :=
  ∑' e : ℕ,
    gammaSewnMobiusContinuousApertureCubicDefect a p e *
      gammaSewnMobiusContinuousApertureCubicDefect b p e

/-- The defect radial gain is exactly the quadratic Gamma tangency factor. -/
theorem gammaSewnMobiusCubicDefectRadialGain_eq_sq_mul_gain
    (x : ℝ) (p : Nat.Primes) :
    gammaSewnMobiusCubicDefectRadialGain x p =
      (1 - xiMobiusContinuousApertureDiskNode x p) ^ (2 : ℕ) *
        gammaSewnMobiusValuationQuadraticDefectGain x p := by
  exact one_sub_gammaSewnMobiusValuationContractionMultiplier_eq_sq_mul_gain x p

/-- Positive aperture makes the cubic-defect radial gain strictly positive. -/
theorem gammaSewnMobiusCubicDefectRadialGain_pos
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    0 < gammaSewnMobiusCubicDefectRadialGain x p := by
  exact sub_pos.mpr (gammaSewnMobiusValuationContractionMultiplier_lt_one hx p)

/-- The complete cubic defect ray is the negative radial gain times the source ray. -/
theorem gammaSewnMobiusContinuousApertureCubicDefect_eq
    (x : ℝ) (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusContinuousApertureCubicDefect x p e =
      -gammaSewnMobiusCubicDefectRadialGain x p *
        xiMobiusPrimeSchurContinuousForwardDifference x p e := by
  rw [gammaSewnMobiusContinuousApertureCubicDefect,
    gammaSewnMobiusContinuousApertureFeature,
    gammaSewnMobiusCubicDefectRadialGain]
  ring

/-- The cubic-defect Gram is a positive radial rescaling of the Möbius--Szegő aperture metric. -/
theorem gammaSewnMobiusContinuousApertureCubicDefectMetric_eq_radial_mul_szego
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    gammaSewnMobiusContinuousApertureCubicDefectMetric a b p =
      gammaSewnMobiusCubicDefectRadialGain a p *
        gammaSewnMobiusCubicDefectRadialGain b p *
          xiMobiusPrimeContinuousApertureSzegoMetric a b p := by
  let ρa := gammaSewnMobiusCubicDefectRadialGain a p
  let ρb := gammaSewnMobiusCubicDefectRadialGain b p
  calc
    gammaSewnMobiusContinuousApertureCubicDefectMetric a b p =
        ∑' e : ℕ,
          (ρa * ρb) *
            (xiMobiusPrimeSchurContinuousForwardDifference a p e *
              xiMobiusPrimeSchurContinuousForwardDifference b p e) := by
      rw [gammaSewnMobiusContinuousApertureCubicDefectMetric]
      apply tsum_congr
      intro e
      rw [gammaSewnMobiusContinuousApertureCubicDefect_eq,
        gammaSewnMobiusContinuousApertureCubicDefect_eq]
      change (-ρa * xiMobiusPrimeSchurContinuousForwardDifference a p e) *
          (-ρb * xiMobiusPrimeSchurContinuousForwardDifference b p e) = _
      ring
    _ = (ρa * ρb) *
        ∑' e : ℕ,
          xiMobiusPrimeSchurContinuousForwardDifference a p e *
            xiMobiusPrimeSchurContinuousForwardDifference b p e := tsum_mul_left
    _ = gammaSewnMobiusCubicDefectRadialGain a p *
        gammaSewnMobiusCubicDefectRadialGain b p *
          xiMobiusPrimeContinuousApertureSzegoMetric a b p := by
      rw [tsum_xiMobiusPrimeSchurContinuousForwardDifference_mul_eq_metric ha hb p]

/-- Every positive-aperture cubic-defect ray has strictly positive completed mass. -/
theorem gammaSewnMobiusContinuousApertureCubicDefectMetric_self_pos
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    0 < gammaSewnMobiusContinuousApertureCubicDefectMetric a a p := by
  rw [gammaSewnMobiusContinuousApertureCubicDefectMetric_eq_radial_mul_szego ha ha]
  exact mul_pos
    (mul_pos
      (gammaSewnMobiusCubicDefectRadialGain_pos ha p)
      (gammaSewnMobiusCubicDefectRadialGain_pos ha p))
    (xiMobiusPrimeContinuousApertureSzegoMetric_self_pos_iff a p |>.2 ha)

/-- **Gamma-sewn cubic-defect Szegő-angle universality.**  Cubic Gamma attenuation changes only
radial masses: every normalized aperture correlation is exactly preserved. -/
theorem gammaSewnMobiusContinuousApertureCubicDefect_metricRatio_eq_correlation
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    gammaSewnMobiusContinuousApertureCubicDefectMetric a b p ^ (2 : ℕ) /
        (gammaSewnMobiusContinuousApertureCubicDefectMetric a a p *
          gammaSewnMobiusContinuousApertureCubicDefectMetric b b p) =
      xiMobiusPrimeContinuousApertureNormalizedCorrelationSq a b p := by
  rw [gammaSewnMobiusContinuousApertureCubicDefectMetric_eq_radial_mul_szego ha hb,
    gammaSewnMobiusContinuousApertureCubicDefectMetric_eq_radial_mul_szego ha ha,
    gammaSewnMobiusContinuousApertureCubicDefectMetric_eq_radial_mul_szego hb hb,
    xiMobiusPrimeContinuousApertureNormalizedCorrelationSq_eq_metricRatio ha hb p]
  have hρa := gammaSewnMobiusCubicDefectRadialGain_pos ha p
  have hρb := gammaSewnMobiusCubicDefectRadialGain_pos hb p
  have hKa := xiMobiusPrimeContinuousApertureSzegoMetric_self_pos_iff a p |>.2 ha
  have hKb := xiMobiusPrimeContinuousApertureSzegoMetric_self_pos_iff b p |>.2 hb
  field_simp [hρa.ne', hρb.ne', hKa.ne', hKb.ne']

/-- The normalized cubic-defect angular loss is the exact real-disk pseudohyperbolic distance
squared. -/
theorem one_sub_gammaSewnMobiusContinuousApertureCubicDefect_metricRatio
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    1 -
        gammaSewnMobiusContinuousApertureCubicDefectMetric a b p ^ (2 : ℕ) /
          (gammaSewnMobiusContinuousApertureCubicDefectMetric a a p *
            gammaSewnMobiusContinuousApertureCubicDefectMetric b b p) =
      ((xiMobiusContinuousApertureDiskNode a p -
          xiMobiusContinuousApertureDiskNode b p) /
        (1 - xiMobiusContinuousApertureDiskNode a p *
          xiMobiusContinuousApertureDiskNode b p)) ^ (2 : ℕ) := by
  rw [gammaSewnMobiusContinuousApertureCubicDefect_metricRatio_eq_correlation ha hb,
    one_sub_xiMobiusPrimeContinuousApertureNormalizedCorrelationSq ha hb]

end

end RHTower
