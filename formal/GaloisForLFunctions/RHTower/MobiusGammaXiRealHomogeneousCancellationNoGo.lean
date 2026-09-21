import GaloisForLFunctions.RHTower.MobiusGammaXiRealReflectionCancellationNoGo

/-!
# Homogeneous nonlinear G-CE cancellation is physical-ray erasure

The coupled-error singular coefficient is a real physical Ward charge. This
file extends linear and anti-linear cancellation dichotomies to arbitrary
nonlinear controllers homogeneous under real source-amplitude scaling.
-/

open Complex

noncomputable section

namespace RHTower

/-- A possibly nonlinear controller compatible with real source-amplitude scaling. -/
def mobiusGammaXiRealHomogeneousDebtController (F : ℂ → ℂ) : Prop :=
  ∀ (r : ℝ) (z : ℂ), F ((r : ℂ) * z) = (r : ℂ) * F z

/-- Visible residual after a homogeneous nonlinear controller. -/
def mobiusGammaXiRealHomogeneousControlledCriticalResidual (F : ℂ → ℂ) : ℂ :=
  mobiusGammaXiCoupledErrorCriticalCoefficient +
    F mobiusGammaXiCoupledErrorCriticalCoefficient

/-- A controller erases the full real Ward ray when it is opposite on every real amplitude. -/
def mobiusGammaXiRealHomogeneousDebtControllerErasesPhysicalRay
    (F : ℂ → ℂ) : Prop :=
  ∀ r : ℝ, F (r : ℂ) = -(r : ℂ)

private theorem real_smul_critical_coefficient_eq
    (d : ℂ) (hdim : d.im = 0) (hdne : d ≠ 0) (r : ℝ) :
    (r / d.re : ℝ) • d = (r : ℂ) := by
  have hdre : d.re ≠ 0 := by
    intro hre
    apply hdne
    apply Complex.ext <;> simp [hre, hdim]
  rw [Algebra.smul_def]
  have hd : d = (d.re : ℂ) := by
    apply Complex.ext <;> simp [hdim]
  rw [hd]
  simp only [Complex.ofReal_re]
  change ((r / d.re : ℝ) : ℂ) * (d.re : ℂ) = (r : ℂ)
  rw [← Complex.ofReal_mul]
  exact_mod_cast div_mul_cancel₀ r hdre

/-- Real-amplitude homogeneity does not evade scalar source erasure. -/
theorem mobiusGammaXiRealHomogeneousDebtController_cancellation_iff_rh_or_physicalRayErasure
    (F : ℂ → ℂ) (hF : mobiusGammaXiRealHomogeneousDebtController F) :
    mobiusGammaXiRealHomogeneousControlledCriticalResidual F = 0 ↔
      RiemannHypothesis ∨
        mobiusGammaXiRealHomogeneousDebtControllerErasesPhysicalRay F := by
  let d := mobiusGammaXiCoupledErrorCriticalCoefficient
  constructor
  · intro hcancel
    by_cases hd : d = 0
    · left
      exact continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mp
        (by simpa [d, mobiusGammaXiCoupledErrorCriticalCoefficient] using hd)
    · right
      intro r
      have hFd : F d = -d := by
        dsimp only [mobiusGammaXiRealHomogeneousControlledCriticalResidual, d] at hcancel
        linear_combination hcancel
      have hrd : (r / d.re : ℝ) • d = (r : ℂ) :=
        real_smul_critical_coefficient_eq d
          (by simpa [d] using mobiusGammaXiCoupledErrorCriticalCoefficient_im_eq_zero)
          hd r
      rw [← hrd]
      change F (((r / d.re : ℝ) : ℂ) * d) =
        -(((r / d.re : ℝ) : ℂ) * d)
      rw [hF, hFd]
      ring
  · rintro (hRH | herase)
    · have hd : mobiusGammaXiCoupledErrorCriticalCoefficient = 0 := by
        exact continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mpr hRH
      have hFzero : F 0 = 0 := by
        simpa using hF 0 0
      simp [mobiusGammaXiRealHomogeneousControlledCriticalResidual, hd, hFzero]
    · rw [mobiusGammaXiRealHomogeneousControlledCriticalResidual]
      have hd : mobiusGammaXiCoupledErrorCriticalCoefficient =
          (mobiusGammaXiCoupledErrorCriticalCoefficient.re : ℂ) := by
        apply Complex.ext <;>
          simp [mobiusGammaXiCoupledErrorCriticalCoefficient_im_eq_zero]
      rw [hd, herase]
      ring

/-- Exact controller and hidden-port energy forced by visible cancellation. -/
theorem mobiusGammaXiRealHomogeneousDebtController_energy_transfer
    (F : ℂ → ℂ)
    (hcancel : mobiusGammaXiRealHomogeneousControlledCriticalResidual F = 0) :
    Complex.normSq (F mobiusGammaXiCoupledErrorCriticalCoefficient) =
        mobiusGammaXiCoupledErrorSingularGraphDebt ∧
      (1 / 2 : ℝ) * Complex.normSq
          (mobiusGammaXiCoupledErrorCriticalCoefficient -
            F mobiusGammaXiCoupledErrorCriticalCoefficient) =
        2 * mobiusGammaXiCoupledErrorSingularGraphDebt := by
  have hFd : F mobiusGammaXiCoupledErrorCriticalCoefficient =
      -mobiusGammaXiCoupledErrorCriticalCoefficient := by
    dsimp only [mobiusGammaXiRealHomogeneousControlledCriticalResidual] at hcancel
    linear_combination hcancel
  constructor
  · rw [hFd, Complex.normSq_neg]
    rfl
  · rw [hFd]
    have htwice : mobiusGammaXiCoupledErrorCriticalCoefficient -
        -mobiusGammaXiCoupledErrorCriticalCoefficient =
        (2 : ℂ) * mobiusGammaXiCoupledErrorCriticalCoefficient := by
      ring
    rw [htwice, Complex.normSq_mul, Complex.normSq_ofNat]
    simp only [mobiusGammaXiCoupledErrorSingularGraphDebt]
    ring

/-- After excluding physical-ray erasure, homogeneous nonlinear cancellation is exactly RH. -/
theorem mobiusGammaXiRealHomogeneousDebtController_nonerasingCancellation_iff
    (F : ℂ → ℂ) (hF : mobiusGammaXiRealHomogeneousDebtController F) :
    (¬ mobiusGammaXiRealHomogeneousDebtControllerErasesPhysicalRay F ∧
        mobiusGammaXiRealHomogeneousControlledCriticalResidual F = 0) ↔
      (¬ mobiusGammaXiRealHomogeneousDebtControllerErasesPhysicalRay F ∧
        RiemannHypothesis) := by
  rw [mobiusGammaXiRealHomogeneousDebtController_cancellation_iff_rh_or_physicalRayErasure F hF]
  tauto

end RHTower
