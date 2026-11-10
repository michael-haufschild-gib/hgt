import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherMomentTypeIPole

/-!
# Complete correlations of critical Gaussian moment cofactors

The long-variable height phase cancels in a pair. Its continuous Gram
entry is an integer power of a complex Gaussian covariance. Rotation
then suppresses separated cofactors geometrically in the moment order;
the complete lattice retains an explicit Bernoulli remainder.
-/

open Complex MeasureTheory Filter Topology
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The critical Mellin exponent of the normalized moment. -/
def gaussianCriticalMomentExponent (r : ℕ) (t : ℝ) : ℂ :=
  ((2 * r : ℕ) : ℂ) - (((1 / 2 : ℝ) : ℂ) + t * I)

/-- The part of a cofactor column independent of its long variable. -/
def gaussianCofactorAmplitude (r : ℕ) (t : ℝ) (ε : ℂ) (m : ℝ) : ℂ :=
  (ε / (t : ℂ)) ^ r * (m : ℂ) ^ gaussianCriticalMomentExponent r t

/-- Complex damping after pairing two dilated Gaussian columns. -/
def gaussianCofactorPairDamping (ε : ℂ) (m k : ℝ) : ℂ :=
  ε * (m : ℂ) ^ 2 + (starRingEnd ℂ) ε * (k : ℂ) ^ 2

/-- The exact continuous pair correlation. -/
def gaussianCofactorCorrelationMain (r : ℕ) (t : ℝ) (ε : ℂ) (m k : ℝ) : ℂ :=
  gaussianCofactorAmplitude r t ε m * (starRingEnd ℂ) (gaussianCofactorAmplitude r t ε k) *
    ((1 / 2 : ℂ) * Complex.Gamma ((2 * r : ℕ) : ℂ)) /
      gaussianCofactorPairDamping ε m k ^ (2 * r)

/-- The positive geometric scale of the two diagonal continuum entries. -/
def gaussianCofactorCorrelationScale (r : ℕ) (t : ℝ) (ε : ℂ) (m k : ℝ) : ℝ :=
  ‖gaussianCofactorAmplitude r t ε m‖ * ‖gaussianCofactorAmplitude r t ε k‖ *
    ‖(1 / 2 : ℂ) * Complex.Gamma ((2 * r : ℕ) : ℂ)‖ /
      (2 * ε.re * m * k) ^ (2 * r)

/-- The dimensionless overlap of the two continuum columns. -/
def gaussianCofactorOverlap (r : ℕ) (ε : ℂ) (m k : ℝ) : ℝ :=
  ((2 * ε.re * m * k) ^ 2 / ‖gaussianCofactorPairDamping ε m k‖ ^ 2) ^ r

theorem gaussianCofactorPairDamping_re (ε : ℂ) (m k : ℝ) :
    (gaussianCofactorPairDamping ε m k).re = ε.re * (m ^ 2 + k ^ 2) := by
  simp only [gaussianCofactorPairDamping, Complex.add_re, Complex.mul_re,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, mul_zero, sub_zero]
  ring

theorem gaussianCofactorPairDamping_im (ε : ℂ) (m k : ℝ) :
    (gaussianCofactorPairDamping ε m k).im = ε.im * (m ^ 2 - k ^ 2) := by
  simp only [gaussianCofactorPairDamping, Complex.add_im, Complex.mul_im,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, mul_zero, zero_add]
  ring

theorem gaussianCofactorPairDamping_re_pos {ε : ℂ} (hε : 0 < ε.re)
    {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    0 < (gaussianCofactorPairDamping ε m k).re := by
  rw [gaussianCofactorPairDamping_re]
  positivity

private theorem pairDamping_ne_zero {ε : ℂ} (hε : 0 < ε.re)
    {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    gaussianCofactorPairDamping ε m k ≠ 0 := by
  intro h
  have hh := gaussianCofactorPairDamping_re_pos hε hm hk
  rw [h, Complex.zero_re] at hh
  exact lt_irrefl _ hh

end GaloisForLFunctions.ExceptionalLayerTheory
