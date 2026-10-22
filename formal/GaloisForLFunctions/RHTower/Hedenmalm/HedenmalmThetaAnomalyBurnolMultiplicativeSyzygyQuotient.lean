import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAnomalyBurnolPrimeOrientationLine

/-!
# Multiplicative Burnol syzygy and horizontal quotient

The completed centered co-Poisson cells at 2, 3, and 6 satisfy an exact entire sine-addition
syzygy induced by 6 = 2 * 3.  Consequently every three-cell synthesis has two unique affine
coordinates: the P-G114 horizontal determinant-line gauge and an independent arithmetic syzygy
gauge.

Eliminating or changing the multiplicative syzygy coordinate leaves the horizontal gauge exactly
unchanged.  Thus adding the first composite Burnol cell cannot cancel P-G115's Gaussian source
class.  Multiplicative redundancy must be quotiented before testing the RH-bearing orientation.
-/

open Complex Real

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Multiplicative sine-addition coefficient carrying the prime-two cell into the six-cell. -/
def burnolTwoToSixCoefficient (z : ℂ) : ℂ :=
  thetaIntegerShiftScale 6 / thetaIntegerShiftScale 2 *
    Complex.cos (z * ((Real.log 3 / 2 : ℝ) : ℂ))

/-- Multiplicative sine-addition coefficient carrying the prime-three cell into the six-cell. -/
def burnolThreeToSixCoefficient (z : ℂ) : ℂ :=
  thetaIntegerShiftScale 6 / thetaIntegerShiftScale 3 *
    Complex.cos (z * ((Real.log 2 / 2 : ℝ) : ℂ))

theorem burnolCompletedCenteredMultiplier_eq_scale_sin_div
    (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    burnolCompletedCenteredMultiplier n z =
      2 * thetaIntegerShiftScale n *
        Complex.sin (z * ((Real.log n / 2 : ℝ) : ℂ)) / z := by
  rw [burnolCompletedCenteredMultiplier_eq_centeredMultiplierE,
    centeredMultiplierE_eq n hz, centeredMultiplier_eq_sin n hz,
    thetaIntegerShiftScale]

/-- Exact completed co-Poisson multiplicative syzygy for `6=2*3`. -/
theorem burnolCompletedCenteredMultiplier_six_eq_two_three (z : ℂ) :
    burnolCompletedCenteredMultiplier 6 z =
      burnolTwoToSixCoefficient z * burnolCompletedCenteredMultiplier 2 z +
        burnolThreeToSixCoefficient z * burnolCompletedCenteredMultiplier 3 z := by
  have hs2 : thetaIntegerShiftScale 2 ≠ 0 :=
    thetaIntegerShiftScale_ne_zero (by norm_num)
  have hs3 : thetaIntegerShiftScale 3 ≠ 0 :=
    thetaIntegerShiftScale_ne_zero (by norm_num)
  have hlog : Real.log (6 : ℕ) = Real.log (2 : ℕ) + Real.log (3 : ℕ) := by
    norm_num only [Nat.cast_ofNat]
    calc
      Real.log 6 = Real.log (2 * 3) := by norm_num
      _ = Real.log 2 + Real.log 3 :=
        Real.log_mul (by norm_num) (by norm_num)
  rcases eq_or_ne z 0 with rfl | hz
  · rw [burnolCompletedCenteredMultiplier_zero,
      burnolCompletedCenteredMultiplier_zero,
      burnolCompletedCenteredMultiplier_zero,
      burnolTwoToSixCoefficient, burnolThreeToSixCoefficient]
    simp only [zero_mul, Complex.cos_zero, mul_one]
    rw [hlog]
    push_cast
    field_simp [hs2, hs3]
  · rw [burnolCompletedCenteredMultiplier_eq_scale_sin_div 6 hz,
      burnolCompletedCenteredMultiplier_eq_scale_sin_div 2 hz,
      burnolCompletedCenteredMultiplier_eq_scale_sin_div 3 hz,
      burnolTwoToSixCoefficient, burnolThreeToSixCoefficient]
    have hphase :
        z * ((Real.log (6 : ℕ) / 2 : ℝ) : ℂ) =
          z * ((Real.log (2 : ℕ) / 2 : ℝ) : ℂ) +
            z * ((Real.log (3 : ℕ) / 2 : ℝ) : ℂ) := by
      rw [hlog]
      push_cast
      ring
    rw [hphase, Complex.sin_add]
    field_simp [hs2, hs3, hz]
    ring

/-- Three-cell synthesis obtained from the two-prime affine row plus the exact arithmetic
syzygy coordinate. -/
def burnolTwoThreeSixSynthesisFrame (c d z : ℂ) : ℂ × ℂ × ℂ :=
  ((burnolAffineSynthesisFrame c z).1 - burnolTwoToSixCoefficient z * d,
    (burnolAffineSynthesisFrame c z).2 - burnolThreeToSixCoefficient z * d,
    d)

theorem burnolTwoThreeSixSynthesis_identity (c d z : ℂ) :
    (burnolTwoThreeSixSynthesisFrame c d z).1 *
        burnolCompletedCenteredMultiplier 2 z +
      (burnolTwoThreeSixSynthesisFrame c d z).2.1 *
        burnolCompletedCenteredMultiplier 3 z +
      (burnolTwoThreeSixSynthesisFrame c d z).2.2 *
        burnolCompletedCenteredMultiplier 6 z = 1 := by
  rw [burnolTwoThreeSixSynthesisFrame]
  dsimp only [Prod.fst, Prod.snd]
  rw [burnolCompletedCenteredMultiplier_six_eq_two_three]
  rw [← burnolAffineSynthesis_identity c z]
  ring

/-- Eliminate the arithmetic six-cell along its exact multiplicative syzygy. -/
def burnolTwoThreeSixEffectivePair (b₂ b₃ b₆ z : ℂ) : ℂ × ℂ :=
  (b₂ + burnolTwoToSixCoefficient z * b₆,
    b₃ + burnolThreeToSixCoefficient z * b₆)

theorem burnolTwoThreeSixEffectivePair_synthesis
    (z b₂ b₃ b₆ : ℂ)
    (hbez : b₂ * burnolCompletedCenteredMultiplier 2 z +
        b₃ * burnolCompletedCenteredMultiplier 3 z +
        b₆ * burnolCompletedCenteredMultiplier 6 z = 1) :
    (burnolTwoThreeSixEffectivePair b₂ b₃ b₆ z).1 *
        burnolCompletedCenteredMultiplier 2 z +
      (burnolTwoThreeSixEffectivePair b₂ b₃ b₆ z).2 *
        burnolCompletedCenteredMultiplier 3 z = 1 := by
  rw [burnolTwoThreeSixEffectivePair]
  dsimp only [Prod.fst, Prod.snd]
  rw [burnolCompletedCenteredMultiplier_six_eq_two_three] at hbez
  linear_combination hbez

/-- Horizontal determinant-line gauge after quotienting the exact multiplicative syzygy. -/
def burnolTwoThreeSixHorizontalGauge (z b₂ b₃ b₆ : ℂ) : ℂ :=
  burnolSynthesisGauge z
    (burnolTwoThreeSixEffectivePair b₂ b₃ b₆ z).1
    (burnolTwoThreeSixEffectivePair b₂ b₃ b₆ z).2

theorem burnolTwoThreeSixSynthesisFrame_effectivePair (c d z : ℂ) :
    burnolTwoThreeSixEffectivePair
        (burnolTwoThreeSixSynthesisFrame c d z).1
        (burnolTwoThreeSixSynthesisFrame c d z).2.1
        (burnolTwoThreeSixSynthesisFrame c d z).2.2 z =
      burnolAffineSynthesisFrame c z := by
  rw [burnolTwoThreeSixEffectivePair, burnolTwoThreeSixSynthesisFrame]
  apply Prod.ext <;> dsimp <;> ring

/-- Arithmetic syzygy motion cannot alter horizontal gauge. -/
theorem burnolTwoThreeSixSynthesisFrame_horizontalGauge (c d z : ℂ) :
    burnolTwoThreeSixHorizontalGauge z
        (burnolTwoThreeSixSynthesisFrame c d z).1
        (burnolTwoThreeSixSynthesisFrame c d z).2.1
        (burnolTwoThreeSixSynthesisFrame c d z).2.2 = c := by
  rw [burnolTwoThreeSixHorizontalGauge,
    burnolTwoThreeSixSynthesisFrame_effectivePair,
    burnolAffineSynthesis_gauge]

/-- Complete two-gauge classification of every synthesis by the three multiplicatively related
Burnol cells. -/
theorem burnolTwoThreeSixSynthesis_classification
    (z b₂ b₃ b₆ : ℂ)
    (hbez : b₂ * burnolCompletedCenteredMultiplier 2 z +
        b₃ * burnolCompletedCenteredMultiplier 3 z +
        b₆ * burnolCompletedCenteredMultiplier 6 z = 1) :
    (b₂, b₃, b₆) =
      burnolTwoThreeSixSynthesisFrame
        (burnolTwoThreeSixHorizontalGauge z b₂ b₃ b₆) b₆ z := by
  have heff := burnolTwoThreeSixEffectivePair_synthesis z b₂ b₃ b₆ hbez
  have hclass := burnolSynthesis_affine_classification z
    (burnolTwoThreeSixEffectivePair b₂ b₃ b₆ z).1
    (burnolTwoThreeSixEffectivePair b₂ b₃ b₆ z).2 heff
  rw [burnolTwoThreeSixHorizontalGauge]
  rw [burnolTwoThreeSixSynthesisFrame]
  rw [burnolTwoThreeSixEffectivePair]
  apply Prod.ext
  · have h2 := congrArg Prod.fst hclass
    rw [burnolTwoThreeSixEffectivePair] at h2
    dsimp only [Prod.fst, Prod.snd] at h2 ⊢
    linear_combination h2
  · apply Prod.ext
    · have h3 := congrArg Prod.snd hclass
      rw [burnolTwoThreeSixEffectivePair] at h3
      dsimp only [Prod.fst, Prod.snd] at h3 ⊢
      linear_combination h3
    · rfl

/-- Gaussian/source horizontal coordinate inserted into the full multiplicative three-cell torsor. -/
def thetaXiBurnolGaussianTwoThreeSixSynthesisFrame
    (d : ℂ) (q : XiZeroCopy) : ℂ × ℂ × ℂ :=
  burnolTwoThreeSixSynthesisFrame
    (thetaXiBurnolGaussianHorizontalGauge q) d (xiSpectralPoint q)

theorem thetaXiBurnolGaussianTwoThreeSixSynthesis_reconstructs_one
    (d : ℂ) (q : XiZeroCopy) :
    (thetaXiBurnolGaussianTwoThreeSixSynthesisFrame d q).1 *
        burnolCompletedCenteredMultiplier 2 (xiSpectralPoint q) +
      (thetaXiBurnolGaussianTwoThreeSixSynthesisFrame d q).2.1 *
        burnolCompletedCenteredMultiplier 3 (xiSpectralPoint q) +
      (thetaXiBurnolGaussianTwoThreeSixSynthesisFrame d q).2.2 *
        burnolCompletedCenteredMultiplier 6 (xiSpectralPoint q) = 1 := by
  exact burnolTwoThreeSixSynthesis_identity _ _ _

/-- No multiplicative-syzygy coordinate changes the source horizontal class. -/
theorem thetaXiBurnolGaussianTwoThreeSix_horizontalGauge
    (d : ℂ) (q : XiZeroCopy) :
    burnolTwoThreeSixHorizontalGauge (xiSpectralPoint q)
        (thetaXiBurnolGaussianTwoThreeSixSynthesisFrame d q).1
        (thetaXiBurnolGaussianTwoThreeSixSynthesisFrame d q).2.1
        (thetaXiBurnolGaussianTwoThreeSixSynthesisFrame d q).2.2 =
      thetaXiBurnolGaussianHorizontalGauge q := by
  exact burnolTwoThreeSixSynthesisFrame_horizontalGauge _ _ _

/-- Even existence of an arbitrary arithmetic syzygy correction killing horizontal gauge is
equivalent to critical-line placement. -/
theorem exists_thetaXiBurnolGaussianTwoThreeSix_horizontalGauge_zero_iff
    (q : XiZeroCopy) :
    (∃ d : ℂ,
      burnolTwoThreeSixHorizontalGauge (xiSpectralPoint q)
        (thetaXiBurnolGaussianTwoThreeSixSynthesisFrame d q).1
        (thetaXiBurnolGaussianTwoThreeSixSynthesisFrame d q).2.1
        (thetaXiBurnolGaussianTwoThreeSixSynthesisFrame d q).2.2 = 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [← thetaXiBurnolGaussianHorizontalGauge_eq_zero_iff]
  constructor
  · rintro ⟨d, hd⟩
    rwa [thetaXiBurnolGaussianTwoThreeSix_horizontalGauge] at hd
  · intro h
    exact ⟨0, by rw [thetaXiBurnolGaussianTwoThreeSix_horizontalGauge, h]⟩

end

end RHTower.HedenmalmThetaSource
