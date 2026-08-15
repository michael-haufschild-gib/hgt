import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielDualPower

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Truncated center moment appearing in fixed Gabriel interpolation. -/
def inghamFixedGabrielCenterMoment (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  ∫ t in Icc (-T) T, ‖f ((inghamFixedGabrielSigma : ℂ) + t * I)‖ ^
    (364 / 237 : ℝ)

/-- Actual scalar analytic family obtained by pairing the shifted field with its fixed center dual
datum. -/
def inghamFixedGabrielScalarFamily (f : ℂ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Icc (-T) T,
    f (z + t * I) *
      inghamFixedGabrielDualPower
        (inghamFixedGabrielDualSeed
          (f ((inghamFixedGabrielSigma : ℂ) + t * I))) z

/-- The scalar family represents the center moment exactly. -/
theorem inghamFixedGabrielScalarFamily_center (f : ℂ → ℂ) (T : ℝ) :
    inghamFixedGabrielScalarFamily f T (inghamFixedGabrielSigma : ℂ) =
      (inghamFixedGabrielCenterMoment f T : ℂ) := by
  rw [inghamFixedGabrielScalarFamily, inghamFixedGabrielCenterMoment]
  calc
    (∫ t in Icc (-T) T,
      f ((inghamFixedGabrielSigma : ℂ) + t * I) *
        inghamFixedGabrielDualPower
          (inghamFixedGabrielDualSeed
            (f ((inghamFixedGabrielSigma : ℂ) + t * I)))
          (inghamFixedGabrielSigma : ℂ)) =
        ∫ t in Icc (-T) T,
          (↑(‖f ((inghamFixedGabrielSigma : ℂ) + t * I)‖ ^
            (364 / 237 : ℝ)) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [inghamFixedGabrielDualPower_center, mul_inghamFixedGabrielDualSeed]
    _ = (↑(∫ t in Icc (-T) T,
        ‖f ((inghamFixedGabrielSigma : ℂ) + t * I)‖ ^
          (364 / 237 : ℝ)) : ℂ) := integral_ofReal

/-- The truncated center moment is nonnegative when the interval has its natural orientation. -/
theorem inghamFixedGabrielCenterMoment_nonneg (f : ℂ → ℂ) (T : ℝ) :
    0 ≤ inghamFixedGabrielCenterMoment f T := by
  exact integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _

/-- Consequently the center norm of the scalar family is exactly the center moment. -/
theorem norm_inghamFixedGabrielScalarFamily_center
    (f : ℂ → ℂ) (T : ℝ) :
    ‖inghamFixedGabrielScalarFamily f T (inghamFixedGabrielSigma : ℂ)‖ =
      inghamFixedGabrielCenterMoment f T := by
  rw [inghamFixedGabrielScalarFamily_center, Complex.norm_real,
    Real.norm_of_nonneg (inghamFixedGabrielCenterMoment_nonneg f T)]

end

end RHTower.Sieve

