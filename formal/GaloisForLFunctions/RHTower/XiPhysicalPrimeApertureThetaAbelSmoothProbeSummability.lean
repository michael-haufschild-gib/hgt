import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelPhaseFiberRigidity
import GaloisForLFunctions.RHTower.CCMSmoothProfileDecay
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap

open Complex Filter Topology MeasureTheory MeromorphicOn
open scoped BigOperators ENNReal NNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace RHTower

noncomputable section

/-!
# Smooth-probe summability for physical theta--Abel Xi packets

Squaring a fixed smooth compact-aperture Laplace amplitude supplies inverse-square spectral decay.
Combined with multiplicity-exact Xi inverse-square summability, the Xi height gap, and uniform
physical-aperture bounds, this makes the complete right-Xi theta--Abel packet norm-summable in
`L²`. Thus norm nonsummability is not an escape after smooth probing: only failure of a finite
strictly isolated rightmost layer remains.
-/

/-- Actual Xi-divisor support strictly right of the critical line. -/
abbrev XiRightDivisorSupport :=
  {rho : XiDivisorSupport // 1 / 2 < (rho : ℂ).re}

/-- Centered right-Xi coordinate `rho - 1/2`. -/
def xiRightSupportCenteredZero (rho : XiRightDivisorSupport) : ℂ :=
  (rho.1 : ℂ) - 1 / 2

/-- Theta--Abel exponent `rho - 1`. -/
def xiRightSupportThetaAbelExponent (rho : XiRightDivisorSupport) : ℂ :=
  (rho.1 : ℂ) - 1

/-- Canonical first multiplicity copy of a right-support point. -/
def xiRightSupportFirstCopy (rho : XiRightDivisorSupport) : XiRightZeroCopy := by
  have hpos := xi_divisor_pos_on_support rho.1
  have hn : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (rho.1 : ℂ)) := by
    omega
  exact ⟨⟨rho.1, ⟨0, hn⟩⟩, by
    rw [I_mul_xiSpectralPoint]
    dsimp
    norm_num
    exact rho.2⟩

@[simp] theorem xiRightCenteredZero_firstCopy
    (rho : XiRightDivisorSupport) :
    xiRightCenteredZero (xiRightSupportFirstCopy rho) =
      xiRightSupportCenteredZero rho := by
  rw [xiRightCenteredZero, I_mul_xiSpectralPoint]
  rfl

theorem xiRightSupportCenteredZero_re_pos (rho : XiRightDivisorSupport) :
    0 < (xiRightSupportCenteredZero rho).re := by
  simpa [xiRightSupportCenteredZero, Complex.sub_re] using rho.2

theorem xiRightSupportCenteredZero_re_lt_half (rho : XiRightDivisorSupport) :
    (xiRightSupportCenteredZero rho).re < 1 / 2 := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho.1
  unfold xiRightSupportCenteredZero
  rw [Complex.sub_re]
  norm_num
  linarith

theorem xiRightSupportThetaAbelExponent_re_neg (rho : XiRightDivisorSupport) :
    (xiRightSupportThetaAbelExponent rho).re < 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho.1
  simpa [xiRightSupportThetaAbelExponent, Complex.sub_re] using hstrip.2

theorem xiRightSupportThetaAbelExponent_re_gt_neg_half (rho : XiRightDivisorSupport) :
    -(1 / 2 : ℝ) < (xiRightSupportThetaAbelExponent rho).re := by
  have := rho.2
  change -(1 / 2 : ℝ) < (rho.1 : ℂ).re - 1
  linarith

theorem xiRightSupportThetaAbelExponent_injective :
    Function.Injective xiRightSupportThetaAbelExponent := by
  intro rho tau h
  apply Subtype.ext
  apply Subtype.ext
  exact sub_left_injective h

theorem xiRightSupportThetaAbelExponent_ne_neg_one
    (rho : XiRightDivisorSupport) :
    xiRightSupportThetaAbelExponent rho ≠ -1 := by
  intro h
  have hre := congrArg Complex.re h
  have hrhopos := (xi_divisor_support_re_mem_open_unit rho.1).1
  simp [xiRightSupportThetaAbelExponent, Complex.sub_re] at hre
  linarith

/-- Multiplicity-weighted squared smooth Laplace aperture coefficient. -/
def xiRightSupportSmoothProbeCoefficient
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L)
    (rho : XiRightDivisorSupport) : ℂ :=
  (((MeromorphicOn.divisor xi Set.univ) (rho.1 : ℂ) : ℝ) : ℂ) *
    smoothProfileLaplaceAmplitude f (xiRightSupportCenteredZero rho) ^ 2

theorem xiRightSupportSmoothProbeCoefficient_summable
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) :
    Summable (xiRightSupportSmoothProbeCoefficient f) := by
  let C : ℝ := (Real.exp (L / 2) * smoothProfileDerivativeMass f) ^ 2
  have hbase : Summable (fun rho : XiRightDivisorSupport =>
      ((MeromorphicOn.divisor xi Set.univ) (rho.1 : ℂ) : ℝ) /
        ‖(rho.1 : ℂ) - 1 / 2‖ ^ 2) :=
    xi_zero_multiplicity_centered_inv_sq_summable.subtype _
  apply Summable.of_norm_bounded (hbase.mul_left C)
  intro rho
  have hdR : 0 ≤ ((MeromorphicOn.divisor xi Set.univ) (rho.1 : ℂ) : ℝ) := by
    exact_mod_cast (xi_divisor_pos_on_support rho.1).le
  have hdecay := norm_smoothProfileLaplaceAmplitude_sq_xiRight_le
    heta hwindow f (xiRightSupportFirstCopy rho)
  rw [xiRightCenteredZero_firstCopy] at hdecay
  rw [xiRightSupportSmoothProbeCoefficient, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  · calc
      ((MeromorphicOn.divisor xi Set.univ) (rho.1 : ℂ) : ℝ) *
          ‖smoothProfileLaplaceAmplitude f (xiRightSupportCenteredZero rho) ^ 2‖
          ≤ ((MeromorphicOn.divisor xi Set.univ) (rho.1 : ℂ) : ℝ) *
              (C / ‖xiSpectralPoint (xiRightSupportFirstCopy rho).1‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left hdecay hdR
      _ = C * (((MeromorphicOn.divisor xi Set.univ) (rho.1 : ℂ) : ℝ) /
          ‖(rho.1 : ℂ) - 1 / 2‖ ^ 2) := by
            rw [norm_xiSpectralPoint]
            change ((MeromorphicOn.divisor xi Set.univ) (rho.1 : ℂ) : ℝ) *
                (C / ‖(rho.1 : ℂ) - 1 / 2‖ ^ 2) = _
            ring
  · exact hdR

theorem xiRightSupportSmoothProbeCoefficient_ne_zero
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L)
    (hf : f ∈ xiSmoothProfileGenericSet eta L)
    (rho : XiRightDivisorSupport) :
    xiRightSupportSmoothProbeCoefficient f rho ≠ 0 := by
  have hmult :
      (((MeromorphicOn.divisor xi Set.univ) (rho.1 : ℂ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (xi_divisor_pos_on_support rho.1).ne'
  have hamp : smoothProfileLaplaceAmplitude f
      (xiRightSupportCenteredZero rho) ≠ 0 := by
    have h := hf (xiRightSupportFirstCopy rho)
    simpa only [xiRightCenteredZero_firstCopy] using h
  exact mul_ne_zero hmult (pow_ne_zero 2 hamp)

/-- In the open theta--Abel strip a positive physical window multiplier has norm at most two. -/
theorem norm_xiPhysicalLogWindowModeMultiplier_le_two_of_re_neg
    {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z.re < 0) :
    ‖xiPhysicalLogWindowModeMultiplier c z‖ ≤ 2 := by
  rw [xiPhysicalLogWindowModeMultiplier]
  calc
    ‖Complex.exp ((c : ℂ) * z) - 1‖ ≤
        ‖Complex.exp ((c : ℂ) * z)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = Real.exp (((c : ℂ) * z).re) + 1 := by rw [Complex.norm_exp]; norm_num
    _ ≤ 1 + 1 := by
      gcongr
      rw [Real.exp_le_one_iff]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hc.le hz.le
    _ = 2 := by norm_num

/-- Xi height gap uniformly controls the restored theta--Abel factor. -/
theorem norm_xiRightSupportThetaAbel_restoredFactor_le_two
    (rho : XiRightDivisorSupport) :
    ‖(xiRightSupportThetaAbelExponent rho + 1) /
        xiRightSupportThetaAbelExponent rho‖ ≤ 2 := by
  let z := xiRightSupportThetaAbelExponent rho
  have him : z.im = (rho.1 : ℂ).im := by
    simp [z, xiRightSupportThetaAbelExponent]
  have hheight : 1 < |z.im| := by
    rw [him]
    exact xiDivisorSupport_one_lt_abs_im rho.1
  have hnorm : 1 < ‖z‖ := hheight.trans_le (Complex.abs_im_le_norm z)
  have hnorm0 : 0 < ‖z‖ := zero_lt_one.trans hnorm
  rw [norm_div]
  calc
    ‖z + 1‖ / ‖z‖ ≤ (‖z‖ + 1) / ‖z‖ := by
      gcongr
      simpa using norm_add_le z (1 : ℂ)
    _ ≤ 2 := by
      rw [div_le_iff₀ hnorm0]
      linarith

/-- Uniform `L²` bound for every actual right-Xi theta--Abel aperture profile. -/
theorem norm_xiRightSupportThetaAbelModeApertureL2_le
    {A : ℝ} (_hA : 0 < A) (rho : XiRightDivisorSupport) :
    ‖xiPhysicalThetaAbelModeApertureL2 A
        (xiRightSupportThetaAbelExponent rho)‖ ≤
      ‖(ContinuousMap.toLp 2 (volume : Measure (ClosedInterval 0 A)) ℂ :
          C(ClosedInterval 0 A, ℂ) →L[ℂ]
            Lp ℂ 2 (volume : Measure (ClosedInterval 0 A)))‖ *
        Real.exp (A / 2) := by
  let z := xiRightSupportThetaAbelExponent rho
  have hprofile :
      ‖xiPhysicalThetaAbelModeApertureContinuous A z‖ ≤ Real.exp (A / 2) := by
    rw [ContinuousMap.norm_le _ (Real.exp_pos _).le]
    intro u
    change ‖Complex.exp (-z * (u.1 : ℂ))‖ ≤ Real.exp (A / 2)
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hu0 : 0 ≤ (u.1 : ℝ) := u.2.1
    have huA : (u.1 : ℝ) ≤ A := u.2.2
    have hzlower : -z.re < 1 / 2 := by
      have := xiRightSupportThetaAbelExponent_re_gt_neg_half rho
      linarith
    have hmul : -z.re * (u.1 : ℝ) ≤ (1 / 2 : ℝ) * u.1 :=
      mul_le_mul_of_nonneg_right hzlower.le hu0
    have hupper : (1 / 2 : ℝ) * u.1 ≤ A / 2 := by linarith
    have hre : (-z * (u.1 : ℂ)).re = -z.re * u.1 := by
      simp [Complex.mul_re]
    rw [hre]
    exact hmul.trans hupper
  exact (ContinuousLinearMap.le_opNorm
    (ContinuousMap.toLp 2 (volume : Measure (ClosedInterval 0 A)) ℂ)
    (xiPhysicalThetaAbelModeApertureContinuous A
      (xiRightSupportThetaAbelExponent rho))).trans
        (mul_le_mul_of_nonneg_left hprofile (norm_nonneg _))

/-- Squared smooth aperture probing makes the complete multiplicity-weighted right-Xi
theta--Abel packet norm-summable in physical aperture `L²`. -/
theorem xiRightSupportSmoothProbeThetaAbelModeVector_norm_summable
    {eta L A c : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (hA : 0 < A) (hc : 0 < c) (f : SmoothBoundaryProfile eta L) :
    Summable (fun rho : XiRightDivisorSupport =>
      ‖xiPhysicalThetaAbelCountableModeVector A c
        xiRightSupportThetaAbelExponent
        (xiRightSupportSmoothProbeCoefficient f) rho‖) := by
  let K : ℝ :=
    ‖(ContinuousMap.toLp 2 (volume : Measure (ClosedInterval 0 A)) ℂ :
        C(ClosedInterval 0 A, ℂ) →L[ℂ]
          Lp ℂ 2 (volume : Measure (ClosedInterval 0 A)))‖ * Real.exp (A / 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hcoeff := (xiRightSupportSmoothProbeCoefficient_summable
    heta hwindow f).norm
  have hmajor : Summable (fun rho : XiRightDivisorSupport =>
      (4 * K) * ‖xiRightSupportSmoothProbeCoefficient f rho‖) :=
    hcoeff.mul_left (4 * K)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun rho => ?_) hmajor
  rw [xiPhysicalThetaAbelCountableModeVector, norm_smul, norm_mul, norm_mul]
  have hwindowBound := norm_xiPhysicalLogWindowModeMultiplier_le_two_of_re_neg
    hc (xiRightSupportThetaAbelExponent_re_neg rho)
  have hfactorBound := norm_xiRightSupportThetaAbel_restoredFactor_le_two rho
  have hprofileBound := norm_xiRightSupportThetaAbelModeApertureL2_le hA rho
  change _ ≤ (4 * K) * ‖xiRightSupportSmoothProbeCoefficient f rho‖
  calc
    ‖xiRightSupportSmoothProbeCoefficient f rho‖ *
          ‖xiPhysicalLogWindowModeMultiplier c
            (xiRightSupportThetaAbelExponent rho)‖ *
          ‖(xiRightSupportThetaAbelExponent rho + 1) /
            xiRightSupportThetaAbelExponent rho‖ *
          ‖xiPhysicalThetaAbelModeApertureL2 A
            (xiRightSupportThetaAbelExponent rho)‖
        ≤ ‖xiRightSupportSmoothProbeCoefficient f rho‖ * 2 * 2 * K := by
          gcongr
    _ = (4 * K) * ‖xiRightSupportSmoothProbeCoefficient f rho‖ := by ring

/-- Smooth probing closes the countable-summability escape. A nonempty finite isolated rightmost
layer of actual right-Xi support forces physical half-density nondecay. -/
theorem not_tendsto_xiRightSupportSmoothProbeThetaAbelPhysicalScale_zero
    {eta L A c beta : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (hA : 0 < A) (hc : 0 < c)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L)
    (D : Finset XiRightDivisorSupport) (hD : D.Nonempty)
    (hdom : ∀ rho ∈ D, (xiRightSupportThetaAbelExponent rho).re = beta)
    (hsub : ∀ rho ∉ D, (xiRightSupportThetaAbelExponent rho).re < beta) :
    ¬ Tendsto
      (fun n : ℕ =>
        Complex.exp ((beta + 1 / 2 : ℝ) : ℂ) ^ n •
          xiPhysicalThetaAbelCountableNormalizedL2Response A c beta
            xiRightSupportThetaAbelExponent
            (xiRightSupportSmoothProbeCoefficient f) n)
      atTop (nhds 0) := by
  obtain ⟨rho, hrho⟩ := hD
  have hbeta0 : beta < 0 := by
    rw [← hdom rho hrho]
    exact xiRightSupportThetaAbelExponent_re_neg rho
  have hwall : -(1 / 2 : ℝ) < beta := by
    rw [← hdom rho hrho]
    exact xiRightSupportThetaAbelExponent_re_gt_neg_half rho
  exact not_tendsto_xiPhysicalThetaAbelCountableL2PhysicalScale_zero_of_distinctModes
    A c beta xiRightSupportThetaAbelExponent
      (xiRightSupportSmoothProbeCoefficient f)
    hA hc
    (xiRightSupportSmoothProbeThetaAbelModeVector_norm_summable
      heta hwindow hA hc f)
    D hdom hsub xiRightSupportThetaAbelExponent_injective.injOn
    rho hrho (xiRightSupportSmoothProbeCoefficient_ne_zero f hf rho)
    (xiRightSupportThetaAbelExponent_ne_neg_one rho) hbeta0 hwall

/-- A suitable fixed smooth probe exists outright for every proposed finite isolated rightmost
right-Xi layer. No profile-genericity premise remains in the conclusion. -/
theorem exists_smoothProbe_not_tendsto_xiRightSupportThetaAbelPhysicalScale_zero
    {eta L A c beta : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (hA : 0 < A) (hc : 0 < c)
    (D : Finset XiRightDivisorSupport) (hD : D.Nonempty)
    (hdom : ∀ rho ∈ D, (xiRightSupportThetaAbelExponent rho).re = beta)
    (hsub : ∀ rho ∉ D, (xiRightSupportThetaAbelExponent rho).re < beta) :
    ∃ f : SmoothBoundaryProfile eta L,
      ¬ Tendsto
        (fun n : ℕ =>
          Complex.exp ((beta + 1 / 2 : ℝ) : ℂ) ^ n •
            xiPhysicalThetaAbelCountableNormalizedL2Response A c beta
              xiRightSupportThetaAbelExponent
              (xiRightSupportSmoothProbeCoefficient f) n)
        atTop (nhds 0) := by
  obtain ⟨f, hf⟩ : (xiSmoothProfileGenericSet eta L).Nonempty :=
    (xiSmoothProfileGenericSet_dense_residual hwindow).1.nonempty
  exact ⟨f, not_tendsto_xiRightSupportSmoothProbeThetaAbelPhysicalScale_zero
    heta hwindow hA hc f hf D hD hdom hsub⟩

end

end RHTower
