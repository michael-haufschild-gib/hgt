import GaloisForLFunctions.RHTower.SuzukiTaV2ActualSecondDefectBound

/-!
# Literal completed-covariance cancellation in Suzuki's second defect

The uniformly bounded endpoint torque is expanded here before scalarization.  Its source is exactly
the zero extension of the scaled completed prime--polar--Gamma covariance response `Cₐ exp(x)`;
both endpoint Fourier values and both signed first moments remain coupled in one quotient.
-/

open Complex MeasureTheory

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

/-- Whole-line literal completed covariance source underlying Suzuki's plus deficiency. -/
def suzukiTaV2CompletedCovarianceSource (a : SuzukiPositiveAperture) : SoninL2 :=
  suzukiApertureZeroExtendL2
    ((‖suzukiTaRawDeficiency a 1‖ : ℂ) •
      suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a 1))

theorem suzukiTaV2CompletedCovarianceSource_eq_plusDeficiency
    (a : SuzukiPositiveAperture) :
    suzukiTaV2CompletedCovarianceSource a =
      suzukiApertureZeroExtendL2
        (suzukiTaPhysicalEmbedding a (suzukiTaPlusDeficiency a)) := by
  rw [suzukiTaV2CompletedCovarianceSource, suzukiTaPlusDeficiency, map_smul,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance,
    norm_suzukiTaRawDeficiency_neg_eq a 1]

/-- Fourier readout of the literal completed covariance source. -/
def suzukiTaV2CompletedCovarianceFourier
    (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  suzukiCompactL2Fourier a.1 (suzukiTaV2CompletedCovarianceSource a) z

/-- Signed first Fourier moment of the literal completed covariance source. -/
def suzukiTaV2CompletedCovarianceFirstMoment
    (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  ∫ x : ℝ,
    (suzukiCutoff a.1 (suzukiTaV2CompletedCovarianceSource a) : ℝ → ℂ) x *
      (I * (x : ℂ)) * Complex.exp (I * z * (x : ℂ))

theorem suzukiTaPhysicalFourier_plus_eq_completedCovarianceFourier
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a) z =
      suzukiTaV2CompletedCovarianceFourier a z := by
  rw [suzukiTaPhysicalFourier, suzukiTaV2CompletedCovarianceFourier,
    suzukiTaV2CompletedCovarianceSource_eq_plusDeficiency]

theorem deriv_suzukiTaPhysicalFourier_plus_eq_completedCovarianceFirstMoment
    (a : SuzukiPositiveAperture) (z : ℂ) :
    deriv (suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a)) z =
      suzukiTaV2CompletedCovarianceFirstMoment a z := by
  have hF : suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a) =
      suzukiTaV2CompletedCovarianceFourier a := by
    funext w
    exact suzukiTaPhysicalFourier_plus_eq_completedCovarianceFourier a w
  rw [hF]
  change deriv
      (suzukiCompactL2Fourier a.1 (suzukiTaV2CompletedCovarianceSource a)) z =
    suzukiTaV2CompletedCovarianceFirstMoment a z
  rw [(hasDerivAt_suzukiCompactL2Fourier a.2.le
    (suzukiTaV2CompletedCovarianceSource a) z).deriv]
  rfl

/-- Exact pre-scalar signed cancellation coordinate of Suzuki's actual completed covariance. -/
theorem suzukiTaV2EndpointSecondTorque_eq_completedCovarianceIntegral
    (a : SuzukiPositiveAperture) :
    suzukiTaV2EndpointSecondTorque a =
      4 * I *
        (suzukiTaV2CompletedCovarianceFirstMoment a I *
            suzukiTaV2CompletedCovarianceFourier a (-I) +
          suzukiTaV2CompletedCovarianceFourier a I *
            suzukiTaV2CompletedCovarianceFirstMoment a (-I)) /
        suzukiTaV2CompletedCovarianceFourier a (-I) ^ 2 := by
  rw [suzukiTaV2EndpointSecondTorque]
  simp only
    [deriv_suzukiTaPhysicalFourier_plus_eq_completedCovarianceFirstMoment,
      suzukiTaPhysicalFourier_plus_eq_completedCovarianceFourier]

/-- Uniform literal cancellation bound for scaled `Cₐ exp(x)`, valid at every aperture. -/
theorem norm_suzukiTaV2_completedCovarianceIntegral_le_two
    (a : SuzukiPositiveAperture) :
    ‖4 * I *
        (suzukiTaV2CompletedCovarianceFirstMoment a I *
            suzukiTaV2CompletedCovarianceFourier a (-I) +
          suzukiTaV2CompletedCovarianceFourier a I *
            suzukiTaV2CompletedCovarianceFirstMoment a (-I)) /
        suzukiTaV2CompletedCovarianceFourier a (-I) ^ 2‖ ≤ 2 := by
  rw [← suzukiTaV2EndpointSecondTorque_eq_completedCovarianceIntegral]
  exact norm_suzukiTaV2EndpointSecondTorque_le_two a

end RHTower
end
