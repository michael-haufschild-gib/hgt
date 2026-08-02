import GaloisForLFunctions.RHTower.SuzukiParitySpectralPairTransport
import GaloisForLFunctions.RHTower.SuzukiSecondDefectParityCommutator
import GaloisForLFunctions.RHTower.CompleteResolutionLabelBlindObserverRigidity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Suzuki interior excursions force a spectral credit/debt reversal

A Suzuki first-defect path whose two endpoints lie below a target but whose interior rises above
it cannot be governed by a one-sign parity hazard. It has a rising point, an interior maximum,
and a falling point. The parity-angle velocity is a strictly positive multiple of

`E' / E - O' / O`.

For literal even/odd source spectral measures, the measure-level cross-pair law therefore turns
those three velocity signs into the exact sequence

`inversion debt < lower-pair credit`,
`inversion debt = lower-pair credit`,
`lower-pair credit < inversion debt`.

Thus every interior Suzuki excursion must cross the spectral credit/debt wall. This rules out
every attempted proof based on a globally one-signed hazard while retaining arbitrary local
even/odd spectral reversals. No Riemann-hypothesis assumption or numerical computation occurs.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-! ## Abstract turning-point law -/

/-- A strict excursion above a target between two sub-target endpoints has a positive-velocity
rise, a zero-velocity interior maximum, and a negative-velocity fall. -/
theorem exists_rise_peak_fall_of_strict_interior_excursion
    (f velocity : ℝ → ℝ)
    {left middle right target : ℝ}
    (hleftMiddle : left < middle)
    (hmiddleRight : middle < right)
    (hcont : ContinuousOn f (Icc left right))
    (hderiv : ∀ x ∈ Ioo left right, HasDerivAt f (velocity x) x)
    (hleft : f left < target)
    (hmiddle : target < f middle)
    (hright : f right < target) :
    ∃ rise peak fall : ℝ,
      rise ∈ Ioo left peak ∧
      peak ∈ Ioo left right ∧
      fall ∈ Ioo peak right ∧
      0 < velocity rise ∧
      velocity peak = 0 ∧
      velocity fall < 0 ∧
      target < f peak ∧
      IsLocalMax f peak := by
  have hleftRight : left < right := hleftMiddle.trans hmiddleRight
  obtain ⟨peak, hpeak, hpeakMax⟩ :=
    isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hleftRight.le) hcont
  have hmiddleMem : middle ∈ Icc left right :=
    ⟨hleftMiddle.le, hmiddleRight.le⟩
  have hpeakAbove : target < f peak :=
    hmiddle.trans_le (hpeakMax hmiddleMem)
  have hpeakLeft : left < peak := by
    by_contra h
    have hpeakLe : peak ≤ left := le_of_not_gt h
    have hpeakEq : peak = left := le_antisymm hpeakLe hpeak.1
    rw [hpeakEq] at hpeakAbove
    exact (not_lt_of_ge hleft.le) hpeakAbove
  have hpeakRight : peak < right := by
    by_contra h
    have hrightLe : right ≤ peak := le_of_not_gt h
    have hpeakEq : peak = right := le_antisymm hpeak.2 hrightLe
    rw [hpeakEq] at hpeakAbove
    exact (not_lt_of_ge hright.le) hpeakAbove
  have hpeakLocalMax : IsLocalMax f peak :=
    hpeakMax.isLocalMax (Icc_mem_nhds hpeakLeft hpeakRight)
  have hpeakVelocity : velocity peak = 0 :=
    hpeakLocalMax.hasDerivAt_eq_zero
      (hderiv peak ⟨hpeakLeft, hpeakRight⟩)
  have hcontLeftPeak : ContinuousOn f (Icc left peak) :=
    hcont.mono (by
      intro x hx
      exact ⟨hx.1, hx.2.trans hpeakRight.le⟩)
  have hderivLeftPeak :
      ∀ x ∈ Ioo left peak, HasDerivAt f (velocity x) x := by
    intro x hx
    exact hderiv x ⟨hx.1, hx.2.trans hpeakRight⟩
  obtain ⟨rise, hrise, hriseSlope⟩ :=
    exists_hasDerivAt_eq_slope
      f velocity hpeakLeft hcontLeftPeak hderivLeftPeak
  have hrisePos : 0 < velocity rise := by
    rw [hriseSlope]
    exact div_pos (sub_pos.mpr (hleft.trans hpeakAbove))
      (sub_pos.mpr hpeakLeft)
  have hcontPeakRight : ContinuousOn f (Icc peak right) :=
    hcont.mono (by
      intro x hx
      exact ⟨hpeakLeft.le.trans hx.1, hx.2⟩)
  have hderivPeakRight :
      ∀ x ∈ Ioo peak right, HasDerivAt f (velocity x) x := by
    intro x hx
    exact hderiv x ⟨hpeakLeft.trans hx.1, hx.2⟩
  obtain ⟨fall, hfall, hfallSlope⟩ :=
    exists_hasDerivAt_eq_slope
      f velocity hpeakRight hcontPeakRight hderivPeakRight
  have hfallNeg : velocity fall < 0 := by
    rw [hfallSlope]
    exact div_neg_of_neg_of_pos (sub_neg.mpr (hright.trans hpeakAbove))
      (sub_pos.mpr hpeakRight)
  exact ⟨rise, peak, fall, hrise, ⟨hpeakLeft, hpeakRight⟩, hfall,
    hrisePos, hpeakVelocity, hfallNeg, hpeakAbove, hpeakLocalMax⟩

/-- A twice differentiable real path has nonpositive second derivative at a local maximum.
This converse half of the second-derivative test is not supplied directly by mathlib's
`DerivativeTest`: a hypothetical positive second derivative would also make the point a local
minimum, forcing local constancy and hence zero second derivative. -/
theorem suzukiSecondDeriv_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x)
    (hcont : ContinuousAt f x) :
    deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hsecondPos : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hfirstZero : deriv f x = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin f x :=
    isLocalMin_of_deriv_deriv_pos hsecondPos hfirstZero hcont
  have heq : f =ᶠ[nhds x] fun _ => f x := by
    filter_upwards [hmax, hmin] with y hyMax hyMin
    exact le_antisymm hyMax hyMin
  have hderivEq : deriv f =ᶠ[nhds x] deriv (fun _ => f x) := heq.deriv
  have hsecondZero :
      deriv (deriv f) x = deriv (deriv (fun _ => f x)) x :=
    hderivEq.deriv_eq
  have hsecondZero' : deriv (deriv f) x = 0 := by
    simpa using hsecondZero
  linarith

/-! ## Parity angle versus normalized spectral hazard -/

/-- Exact factorization of parity-angle velocity by the normalized even-minus-odd hazard. -/
theorem suzukiDefectAngleTiltVelocity_eq_hazardFactor
    {evenEnergy oddEnergy evenVelocity oddVelocity : ℝ}
    (heven : evenEnergy ≠ 0) (hodd : oddEnergy ≠ 0) :
    suzukiDefectAngleTiltVelocity
        evenEnergy oddEnergy evenVelocity oddVelocity =
      (2 * evenEnergy * oddEnergy / (evenEnergy + oddEnergy) ^ 2) *
        (evenVelocity / evenEnergy - oddVelocity / oddEnergy) := by
  rw [suzukiDefectAngleTiltVelocity]
  field_simp [heven, hodd]

/-- For positive parity energies, angle velocity and normalized hazard have the same positive
sign. -/
theorem suzukiDefectAngleTiltVelocity_pos_iff_hazardGap_pos
    {evenEnergy oddEnergy evenVelocity oddVelocity : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy) :
    0 < suzukiDefectAngleTiltVelocity
        evenEnergy oddEnergy evenVelocity oddVelocity ↔
      0 < evenVelocity / evenEnergy - oddVelocity / oddEnergy := by
  rw [suzukiDefectAngleTiltVelocity_eq_hazardFactor heven.ne' hodd.ne']
  have hfactor :
      0 < 2 * evenEnergy * oddEnergy / (evenEnergy + oddEnergy) ^ 2 := by
    exact div_pos (mul_pos (mul_pos (by norm_num) heven) hodd)
      (sq_pos_of_pos (add_pos heven hodd))
  exact mul_pos_iff_of_pos_left hfactor

/-- For positive parity energies, a stationary angle is exact hazard balance. -/
theorem suzukiDefectAngleTiltVelocity_eq_zero_iff_hazardGap_eq_zero
    {evenEnergy oddEnergy evenVelocity oddVelocity : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy) :
    suzukiDefectAngleTiltVelocity
        evenEnergy oddEnergy evenVelocity oddVelocity = 0 ↔
      evenVelocity / evenEnergy - oddVelocity / oddEnergy = 0 := by
  rw [suzukiDefectAngleTiltVelocity_eq_hazardFactor heven.ne' hodd.ne']
  have hfactor :
      0 < 2 * evenEnergy * oddEnergy / (evenEnergy + oddEnergy) ^ 2 := by
    exact div_pos (mul_pos (mul_pos (by norm_num) heven) hodd)
      (sq_pos_of_pos (add_pos heven hodd))
  simp only [mul_eq_zero, hfactor.ne', false_or]

/-- For positive parity energies, angle velocity and normalized hazard have the same negative
sign. -/
theorem suzukiDefectAngleTiltVelocity_neg_iff_hazardGap_neg
    {evenEnergy oddEnergy evenVelocity oddVelocity : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy) :
    suzukiDefectAngleTiltVelocity
          evenEnergy oddEnergy evenVelocity oddVelocity < 0 ↔
      evenVelocity / evenEnergy - oddVelocity / oddEnergy < 0 := by
  rw [suzukiDefectAngleTiltVelocity_eq_hazardFactor heven.ne' hodd.ne']
  have hfactor :
      0 < 2 * evenEnergy * oddEnergy / (evenEnergy + oddEnergy) ^ 2 := by
    exact div_pos (mul_pos (mul_pos (by norm_num) heven) hodd)
      (sq_pos_of_pos (add_pos heven hodd))
  constructor
  · intro h
    by_contra hgap
    exact (not_lt_of_ge (mul_nonneg hfactor.le (le_of_not_gt hgap))) h
  · exact mul_neg_of_pos_of_neg hfactor

/-! ## Stationary inverse-gap dispersion -/

/-- The squared shift-resolvent kernel has derivative twice its cube. -/
theorem hasDerivAt_suzukiShiftResolventKernel_sq
    {γ : Type*} {node : γ → ℝ} {lam : ℝ} {x : γ}
    (h : node x - lam ≠ 0) :
    HasDerivAt
      (fun l => suzukiShiftResolventKernel node l x ^ 2)
      (2 * suzukiShiftResolventKernel node lam x ^ 3) lam := by
  have hpow := (hasDerivAt_suzukiShiftResolventKernel h).pow 2
  apply hpow.congr_deriv
  ring

/-- Dominated differentiation upgrades a squared-resolvent matrix element to twice its
cubed-resolvent response. This is the analytic connector needed by the stationary variance
wall. -/
theorem hasDerivAt_integral_weighted_suzukiShiftResolventKernel_sq
    {γ : Type*} [MeasurableSpace γ] {μ : Measure γ}
    {node g : γ → ℝ} {lam : ℝ} {s : Set ℝ} {bound : γ → ℝ}
    (hs : s ∈ nhds lam)
    (hF_meas : ∀ᶠ l in nhds lam,
      AEStronglyMeasurable
        (fun x => g x * suzukiShiftResolventKernel node l x ^ 2) μ)
    (hF_int : Integrable
      (fun x => g x * suzukiShiftResolventKernel node lam x ^ 2) μ)
    (hF'_meas : AEStronglyMeasurable
      (fun x => 2 * (g x *
        suzukiShiftResolventKernel node lam x ^ 3)) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ l ∈ s,
      ‖2 * (g x * suzukiShiftResolventKernel node l x ^ 3)‖ ≤
        bound x)
    (bound_int : Integrable bound μ)
    (h_ne : ∀ᵐ x ∂μ, ∀ l ∈ s, node x - l ≠ 0) :
    HasDerivAt
      (fun l => ∫ x,
        g x * suzukiShiftResolventKernel node l x ^ 2 ∂μ)
      (2 * ∫ x,
        g x * suzukiShiftResolventKernel node lam x ^ 3 ∂μ) lam := by
  have hraw :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs hF_meas hF_int hF'_meas h_bound bound_int
      (h_ne.mono fun x hx l hl => by
        have hk := hasDerivAt_suzukiShiftResolventKernel_sq (hx l hl)
        apply (HasDerivAt.const_mul (g x) hk).congr_deriv
        ring)).2
  apply hraw.congr_deriv
  rw [integral_const_mul]

/-- Cubed-resolvent response of one weighted source spectral measure. Together with the
first- and squared-resolvent responses, this is the second moment of the inverse gap under the
resolvent-tilted source law. -/
def suzukiParityCubedSpectralEnergy
    {γ : Type*} [MeasurableSpace γ]
    (μ : Measure γ) (node weight : γ → ℝ) (lambda : ℝ) : ℝ :=
  ∫ x, weight x * suzukiShiftResolventKernel node lambda x ^ 3 ∂μ

/-- Normalized inverse-gap variance coordinate for a positive resolvent-tilted source law. -/
def suzukiParityTiltedInverseGapVariance
    (energy squaredEnergy cubedEnergy : ℝ) : ℝ :=
  cubedEnergy / energy - (squaredEnergy / energy) ^ 2

/-- At normalized first-moment balance, the derivative of the parity-angle velocity is the
stationary cubed-resolvent cross-Wronskian. -/
theorem hasDerivAt_suzukiDefectAngleTiltVelocity_of_balance
    {evenEnergy oddEnergy evenSquared oddSquared : ℝ → ℝ}
    {t evenCubed oddCubed : ℝ}
    (heven : HasDerivAt evenEnergy (evenSquared t) t)
    (hodd : HasDerivAt oddEnergy (oddSquared t) t)
    (hevenSquared : HasDerivAt evenSquared (2 * evenCubed) t)
    (hoddSquared : HasDerivAt oddSquared (2 * oddCubed) t)
    (heven0 : evenEnergy t ≠ 0)
    (hodd0 : oddEnergy t ≠ 0)
    (hsum : evenEnergy t + oddEnergy t ≠ 0)
    (hbalance :
      evenSquared t / evenEnergy t = oddSquared t / oddEnergy t) :
    HasDerivAt
      (fun u => suzukiDefectAngleTiltVelocity
        (evenEnergy u) (oddEnergy u) (evenSquared u) (oddSquared u))
      (4 * (evenCubed * oddEnergy t - evenEnergy t * oddCubed) /
        (evenEnergy t + oddEnergy t) ^ 2) t := by
  have hcross :
      evenSquared t * oddEnergy t - evenEnergy t * oddSquared t = 0 := by
    field_simp [heven0, hodd0] at hbalance
    linarith
  have hnum :=
    (hevenSquared.mul hodd).sub (heven.mul hoddSquared)
  have hden := (heven.add hodd).pow 2
  have hquot :=
    (hnum.div hden (pow_ne_zero 2 hsum)).const_mul 2
  have hderivValue :
      2 *
        (((2 * evenCubed * oddEnergy t +
                evenSquared t * oddSquared t -
                (evenSquared t * oddSquared t +
                  evenEnergy t * (2 * oddCubed))) *
              ((evenEnergy + oddEnergy) ^ 2) t -
            (evenSquared * oddEnergy -
              evenEnergy * oddSquared) t *
              (2 * (evenEnergy + oddEnergy) t ^ (2 - 1) *
                (evenSquared t + oddSquared t))) /
          ((evenEnergy + oddEnergy) ^ 2) t ^ 2) =
        4 * (evenCubed * oddEnergy t - evenEnergy t * oddCubed) /
          (evenEnergy t + oddEnergy t) ^ 2 := by
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    rw [hcross]
    simp only [zero_mul, sub_zero]
    field_simp [hsum]
    ring
  have hquot' := hquot.congr_deriv hderivValue
  apply hquot'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun u => by
    simp [suzukiDefectAngleTiltVelocity, div_eq_mul_inv]
    ring

/-- At stationary hazard balance, parity-angle acceleration is a positive multiple of the
difference between the even and odd resolvent-tilted inverse-gap variances. -/
theorem suzukiStationaryAngleAcceleration_eq_tiltedVarianceDifference
    {evenEnergy oddEnergy evenSquared oddSquared evenCubed oddCubed : ℝ}
    (heven : evenEnergy ≠ 0) (hodd : oddEnergy ≠ 0)
    (hsum : evenEnergy + oddEnergy ≠ 0)
    (hbalance : evenSquared / evenEnergy = oddSquared / oddEnergy) :
    4 * (evenCubed * oddEnergy - evenEnergy * oddCubed) /
          (evenEnergy + oddEnergy) ^ 2 =
      (4 * evenEnergy * oddEnergy / (evenEnergy + oddEnergy) ^ 2) *
        (suzukiParityTiltedInverseGapVariance
            evenEnergy evenSquared evenCubed -
          suzukiParityTiltedInverseGapVariance
            oddEnergy oddSquared oddCubed) := by
  rw [suzukiParityTiltedInverseGapVariance,
    suzukiParityTiltedInverseGapVariance, hbalance]
  field_simp [heven, hodd, hsum]
  ring

/-! ## Literal spectral-pair turning law -/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Suzuki spectral turning-point law.** A literal parity-resolvent excursion above a target,
with both endpoints below it, forces lower-pair credit to dominate on the rise, exact
credit/debt balance at an interior maximum, and inversion debt to dominate on the fall. -/
theorem suzukiParitySpectral_interiorExcursion_forces_creditBalanceDebt
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    {left middle right target : ℝ}
    (hleftMiddle : left < middle)
    (hmiddleRight : middle < right)
    (hangleCont : ContinuousOn
      (fun lambda =>
        GaloisForLFunctions.RHTower.suzukiDefectAngle
          (suzukiParitySpectralEnergy
            μ evenNode evenWeight lambda)
          (suzukiParitySpectralEnergy
            ν oddNode oddWeight lambda))
      (Icc left right))
    (hevenDeriv : ∀ lambda ∈ Ioo left right,
      HasDerivAt
        (suzukiParitySpectralEnergy μ evenNode evenWeight)
        (suzukiParitySquaredSpectralEnergy
          μ evenNode evenWeight lambda) lambda)
    (hoddDeriv : ∀ lambda ∈ Ioo left right,
      HasDerivAt
        (suzukiParitySpectralEnergy ν oddNode oddWeight)
        (suzukiParitySquaredSpectralEnergy
          ν oddNode oddWeight lambda) lambda)
    (hevenSquaredDeriv : ∀ lambda ∈ Ioo left right,
      HasDerivAt
        (suzukiParitySquaredSpectralEnergy μ evenNode evenWeight)
        (2 * suzukiParityCubedSpectralEnergy
          μ evenNode evenWeight lambda) lambda)
    (hoddSquaredDeriv : ∀ lambda ∈ Ioo left right,
      HasDerivAt
        (suzukiParitySquaredSpectralEnergy ν oddNode oddWeight)
        (2 * suzukiParityCubedSpectralEnergy
          ν oddNode oddWeight lambda) lambda)
    (hevenInt : ∀ lambda ∈ Ioo left right,
      Integrable
        (fun x => evenWeight x *
          suzukiShiftResolventKernel evenNode lambda x) μ)
    (hevenSqInt : ∀ lambda ∈ Ioo left right,
      Integrable
        (fun x => evenWeight x *
          suzukiShiftResolventKernel evenNode lambda x ^ 2) μ)
    (hoddInt : ∀ lambda ∈ Ioo left right,
      Integrable
        (fun y => oddWeight y *
          suzukiShiftResolventKernel oddNode lambda y) ν)
    (hoddSqInt : ∀ lambda ∈ Ioo left right,
      Integrable
        (fun y => oddWeight y *
          suzukiShiftResolventKernel oddNode lambda y ^ 2) ν)
    (hevenPos : ∀ lambda ∈ Icc left right,
      0 < suzukiParitySpectralEnergy
        μ evenNode evenWeight lambda)
    (hoddPos : ∀ lambda ∈ Icc left right,
      0 < suzukiParitySpectralEnergy
        ν oddNode oddWeight lambda)
    (hleft : GaloisForLFunctions.RHTower.suzukiDefectAngle
        (suzukiParitySpectralEnergy μ evenNode evenWeight left)
        (suzukiParitySpectralEnergy ν oddNode oddWeight left) < target)
    (hmiddle : target <
      GaloisForLFunctions.RHTower.suzukiDefectAngle
        (suzukiParitySpectralEnergy μ evenNode evenWeight middle)
        (suzukiParitySpectralEnergy ν oddNode oddWeight middle))
    (hright : GaloisForLFunctions.RHTower.suzukiDefectAngle
        (suzukiParitySpectralEnergy μ evenNode evenWeight right)
        (suzukiParitySpectralEnergy ν oddNode oddWeight right) < target) :
    ∃ rise peak fall : ℝ,
      rise ∈ Ioo left peak ∧
      peak ∈ Ioo left right ∧
      fall ∈ Ioo peak right ∧
      suzukiParitySpectralInversionDebt
          μ ν evenNode evenWeight oddNode oddWeight rise <
        suzukiParitySpectralLowerPairCredit
          μ ν evenNode evenWeight oddNode oddWeight rise ∧
      suzukiParitySpectralInversionDebt
          μ ν evenNode evenWeight oddNode oddWeight peak =
        suzukiParitySpectralLowerPairCredit
          μ ν evenNode evenWeight oddNode oddWeight peak ∧
      suzukiParitySpectralLowerPairCredit
          μ ν evenNode evenWeight oddNode oddWeight fall <
        suzukiParitySpectralInversionDebt
          μ ν evenNode evenWeight oddNode oddWeight fall ∧
      target <
        GaloisForLFunctions.RHTower.suzukiDefectAngle
          (suzukiParitySpectralEnergy μ evenNode evenWeight peak)
          (suzukiParitySpectralEnergy ν oddNode oddWeight peak) ∧
      suzukiParitySquaredSpectralEnergy
            μ evenNode evenWeight peak /
          suzukiParitySpectralEnergy
            μ evenNode evenWeight peak =
        suzukiParitySquaredSpectralEnergy
            ν oddNode oddWeight peak /
          suzukiParitySpectralEnergy
            ν oddNode oddWeight peak ∧
      suzukiParityTiltedInverseGapVariance
          (suzukiParitySpectralEnergy
            μ evenNode evenWeight peak)
          (suzukiParitySquaredSpectralEnergy
            μ evenNode evenWeight peak)
          (suzukiParityCubedSpectralEnergy
            μ evenNode evenWeight peak) ≤
        suzukiParityTiltedInverseGapVariance
          (suzukiParitySpectralEnergy
            ν oddNode oddWeight peak)
          (suzukiParitySquaredSpectralEnergy
            ν oddNode oddWeight peak)
          (suzukiParityCubedSpectralEnergy
            ν oddNode oddWeight peak) ∧
      IsLocalMax
        (fun lambda =>
          GaloisForLFunctions.RHTower.suzukiDefectAngle
            (suzukiParitySpectralEnergy
              μ evenNode evenWeight lambda)
            (suzukiParitySpectralEnergy
              ν oddNode oddWeight lambda))
        peak := by
  let angle : ℝ → ℝ := fun lambda =>
    GaloisForLFunctions.RHTower.suzukiDefectAngle
      (suzukiParitySpectralEnergy μ evenNode evenWeight lambda)
      (suzukiParitySpectralEnergy ν oddNode oddWeight lambda)
  let velocity : ℝ → ℝ := fun lambda =>
    suzukiDefectAngleTiltVelocity
      (suzukiParitySpectralEnergy μ evenNode evenWeight lambda)
      (suzukiParitySpectralEnergy ν oddNode oddWeight lambda)
      (suzukiParitySquaredSpectralEnergy μ evenNode evenWeight lambda)
      (suzukiParitySquaredSpectralEnergy ν oddNode oddWeight lambda)
  have hangleDeriv :
      ∀ lambda ∈ Ioo left right,
        HasDerivAt angle (velocity lambda) lambda := by
    intro lambda hlambda
    have heven := hevenPos lambda (Ioo_subset_Icc_self hlambda)
    have hodd := hoddPos lambda (Ioo_subset_Icc_self hlambda)
    simpa [angle, velocity] using
      hasDerivAt_suzukiDefectAngle
        (hevenDeriv lambda hlambda)
        (hoddDeriv lambda hlambda)
        (add_pos heven hodd).ne'
  obtain ⟨rise, peak, fall, hrise, hpeak, hfall,
      hriseVelocity, hpeakVelocity, hfallVelocity, hpeakAbove,
      hpeakLocalMax⟩ :=
    exists_rise_peak_fall_of_strict_interior_excursion
      angle velocity hleftMiddle hmiddleRight hangleCont hangleDeriv
      hleft hmiddle hright
  have hriseIcc : rise ∈ Icc left right :=
    Ioo_subset_Icc_self ⟨hrise.1, hrise.2.trans hpeak.2⟩
  have hfallIcc : fall ∈ Icc left right :=
    Ioo_subset_Icc_self ⟨hpeak.1.trans hfall.1, hfall.2⟩
  have hHazardRise :
      0 < suzukiParitySpectralHazardGap
        μ ν evenNode evenWeight oddNode oddWeight rise := by
    rw [suzukiParitySpectralHazardGap]
    exact
      (suzukiDefectAngleTiltVelocity_pos_iff_hazardGap_pos
        (hevenPos rise hriseIcc) (hoddPos rise hriseIcc)).mp
        hriseVelocity
  have hHazardPeak :
      suzukiParitySpectralHazardGap
          μ ν evenNode evenWeight oddNode oddWeight peak = 0 := by
    rw [suzukiParitySpectralHazardGap]
    exact
      (suzukiDefectAngleTiltVelocity_eq_zero_iff_hazardGap_eq_zero
        (hevenPos peak (Ioo_subset_Icc_self hpeak))
        (hoddPos peak (Ioo_subset_Icc_self hpeak))).mp
        hpeakVelocity
  have hmeanBalance :
      suzukiParitySquaredSpectralEnergy
            μ evenNode evenWeight peak /
          suzukiParitySpectralEnergy
            μ evenNode evenWeight peak =
        suzukiParitySquaredSpectralEnergy
            ν oddNode oddWeight peak /
          suzukiParitySpectralEnergy
            ν oddNode oddWeight peak := by
    rw [suzukiParitySpectralHazardGap] at hHazardPeak
    exact sub_eq_zero.mp hHazardPeak
  have hHazardFall :
      suzukiParitySpectralHazardGap
          μ ν evenNode evenWeight oddNode oddWeight fall < 0 := by
    rw [suzukiParitySpectralHazardGap]
    exact
      (suzukiDefectAngleTiltVelocity_neg_iff_hazardGap_neg
        (hevenPos fall hfallIcc) (hoddPos fall hfallIcc)).mp
        hfallVelocity
  have hcreditRise :=
    (suzukiParitySpectral_hazardGap_pos_iff_inversionDebt_lt_credit
      evenNode evenWeight oddNode oddWeight rise
      (hevenInt rise ⟨hrise.1, hrise.2.trans hpeak.2⟩)
      (hevenSqInt rise ⟨hrise.1, hrise.2.trans hpeak.2⟩)
      (hoddInt rise ⟨hrise.1, hrise.2.trans hpeak.2⟩)
      (hoddSqInt rise ⟨hrise.1, hrise.2.trans hpeak.2⟩)
      (hevenPos rise hriseIcc) (hoddPos rise hriseIcc)).mp hHazardRise
  have hbalancePeak :=
    (suzukiParitySpectral_hazardGap_eq_zero_iff_inversionDebt_eq_credit
      evenNode evenWeight oddNode oddWeight peak
      (hevenInt peak hpeak) (hevenSqInt peak hpeak)
      (hoddInt peak hpeak) (hoddSqInt peak hpeak)
      (hevenPos peak (Ioo_subset_Icc_self hpeak))
      (hoddPos peak (Ioo_subset_Icc_self hpeak))).mp hHazardPeak
  have hdebtFall :=
    (suzukiParitySpectral_hazardGap_neg_iff_credit_lt_inversionDebt
      evenNode evenWeight oddNode oddWeight fall
      (hevenInt fall ⟨hpeak.1.trans hfall.1, hfall.2⟩)
      (hevenSqInt fall ⟨hpeak.1.trans hfall.1, hfall.2⟩)
      (hoddInt fall ⟨hpeak.1.trans hfall.1, hfall.2⟩)
      (hoddSqInt fall ⟨hpeak.1.trans hfall.1, hfall.2⟩)
      (hevenPos fall hfallIcc) (hoddPos fall hfallIcc)).mp hHazardFall
  have hvelocityDeriv :
      HasDerivAt velocity
        (4 *
            (suzukiParityCubedSpectralEnergy
                μ evenNode evenWeight peak *
                suzukiParitySpectralEnergy
                  ν oddNode oddWeight peak -
              suzukiParitySpectralEnergy
                  μ evenNode evenWeight peak *
                suzukiParityCubedSpectralEnergy
                  ν oddNode oddWeight peak) /
          (suzukiParitySpectralEnergy
                μ evenNode evenWeight peak +
              suzukiParitySpectralEnergy
                ν oddNode oddWeight peak) ^ 2)
        peak := by
    dsimp only [velocity]
    exact hasDerivAt_suzukiDefectAngleTiltVelocity_of_balance
      (hevenDeriv peak hpeak) (hoddDeriv peak hpeak)
      (hevenSquaredDeriv peak hpeak) (hoddSquaredDeriv peak hpeak)
      (hevenPos peak (Ioo_subset_Icc_self hpeak)).ne'
      (hoddPos peak (Ioo_subset_Icc_self hpeak)).ne'
      (add_pos
        (hevenPos peak (Ioo_subset_Icc_self hpeak))
        (hoddPos peak (Ioo_subset_Icc_self hpeak))).ne'
      hmeanBalance
  have hangleDerivEq : deriv angle =ᶠ[nhds peak] velocity := by
    filter_upwards [Ioo_mem_nhds hpeak.1 hpeak.2] with lambda hlambda
    exact (hangleDeriv lambda hlambda).deriv
  have hangleSecond :
      HasDerivAt (deriv angle)
        (4 *
            (suzukiParityCubedSpectralEnergy
                μ evenNode evenWeight peak *
                suzukiParitySpectralEnergy
                  ν oddNode oddWeight peak -
              suzukiParitySpectralEnergy
                  μ evenNode evenWeight peak *
                suzukiParityCubedSpectralEnergy
                  ν oddNode oddWeight peak) /
          (suzukiParitySpectralEnergy
                μ evenNode evenWeight peak +
              suzukiParitySpectralEnergy
                ν oddNode oddWeight peak) ^ 2)
        peak :=
    hvelocityDeriv.congr_of_eventuallyEq hangleDerivEq
  have haccelerationNonpos :
      4 *
            (suzukiParityCubedSpectralEnergy
                μ evenNode evenWeight peak *
                suzukiParitySpectralEnergy
                  ν oddNode oddWeight peak -
              suzukiParitySpectralEnergy
                  μ evenNode evenWeight peak *
                suzukiParityCubedSpectralEnergy
                  ν oddNode oddWeight peak) /
          (suzukiParitySpectralEnergy
                μ evenNode evenWeight peak +
              suzukiParitySpectralEnergy
                ν oddNode oddWeight peak) ^ 2 ≤ 0 := by
    have hsecond :=
      suzukiSecondDeriv_nonpos_of_isLocalMax
        hpeakLocalMax (hangleDeriv peak hpeak).continuousAt
    rw [hangleSecond.deriv] at hsecond
    exact hsecond
  have haccelerationIdentity :=
    suzukiStationaryAngleAcceleration_eq_tiltedVarianceDifference
      (evenCubed :=
        suzukiParityCubedSpectralEnergy
          μ evenNode evenWeight peak)
      (oddCubed :=
        suzukiParityCubedSpectralEnergy
          ν oddNode oddWeight peak)
      (hevenPos peak (Ioo_subset_Icc_self hpeak)).ne'
      (hoddPos peak (Ioo_subset_Icc_self hpeak)).ne'
      (add_pos
        (hevenPos peak (Ioo_subset_Icc_self hpeak))
        (hoddPos peak (Ioo_subset_Icc_self hpeak))).ne'
      hmeanBalance
  have hfactorPos :
      0 <
        4 *
            suzukiParitySpectralEnergy
              μ evenNode evenWeight peak *
            suzukiParitySpectralEnergy
              ν oddNode oddWeight peak /
          (suzukiParitySpectralEnergy
                μ evenNode evenWeight peak +
              suzukiParitySpectralEnergy
                ν oddNode oddWeight peak) ^ 2 := by
    exact div_pos
      (mul_pos
        (mul_pos (by norm_num)
          (hevenPos peak (Ioo_subset_Icc_self hpeak)))
        (hoddPos peak (Ioo_subset_Icc_self hpeak)))
      (sq_pos_of_pos <| add_pos
        (hevenPos peak (Ioo_subset_Icc_self hpeak))
        (hoddPos peak (Ioo_subset_Icc_self hpeak)))
  have hvarianceOrder :
      suzukiParityTiltedInverseGapVariance
          (suzukiParitySpectralEnergy
            μ evenNode evenWeight peak)
          (suzukiParitySquaredSpectralEnergy
            μ evenNode evenWeight peak)
          (suzukiParityCubedSpectralEnergy
            μ evenNode evenWeight peak) ≤
        suzukiParityTiltedInverseGapVariance
          (suzukiParitySpectralEnergy
            ν oddNode oddWeight peak)
          (suzukiParitySquaredSpectralEnergy
            ν oddNode oddWeight peak)
          (suzukiParityCubedSpectralEnergy
            ν oddNode oddWeight peak) := by
    rw [haccelerationIdentity] at haccelerationNonpos
    by_contra h
    have hdiffPos :
        0 <
          suzukiParityTiltedInverseGapVariance
              (suzukiParitySpectralEnergy
                μ evenNode evenWeight peak)
              (suzukiParitySquaredSpectralEnergy
                μ evenNode evenWeight peak)
              (suzukiParityCubedSpectralEnergy
                μ evenNode evenWeight peak) -
            suzukiParityTiltedInverseGapVariance
              (suzukiParitySpectralEnergy
                ν oddNode oddWeight peak)
              (suzukiParitySquaredSpectralEnergy
                ν oddNode oddWeight peak)
              (suzukiParityCubedSpectralEnergy
                ν oddNode oddWeight peak) :=
      sub_pos.mpr (lt_of_not_ge h)
    exact (not_lt_of_ge haccelerationNonpos) (mul_pos hfactorPos hdiffPos)
  have hpeakLiteralLocalMax :
      IsLocalMax
        (fun lambda =>
          GaloisForLFunctions.RHTower.suzukiDefectAngle
            (suzukiParitySpectralEnergy
              μ evenNode evenWeight lambda)
            (suzukiParitySpectralEnergy
              ν oddNode oddWeight lambda))
        peak := by
    simpa only [angle] using hpeakLocalMax
  exact ⟨rise, peak, fall, hrise, hpeak, hfall,
    hcreditRise, hbalancePeak, hdebtFall, hpeakAbove,
    hmeanBalance, hvarianceOrder, hpeakLiteralLocalMax⟩

/-! ## Source-horizon provenance gate

The credit/debt profile is a nonlinear downstream statistic. The complete Riemann source theorem
shows that nonlinear postprocessing cannot repair upstream label blindness: if every bounded
source-to-parity carrier treats all high-exponent labels equally, then its entire shift profile
is identical at a point and its functional-equation reflection. Hence any source-derived Suzuki
profile that separates those points must already be label-sensitive at some shift. A norm-singular
or relation-valued construction lies outside the bounded-map type used here and remains live.
-/

/-- Functional-equation reflection of an open-strip point, viewed in the source half-plane. -/
def completeResolutionReflectedSourcePoint
    (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionRightHalfPlane :=
  ⟨1 - star s.1, by
    have hstarRe : (star s.1).re = s.1.re := by simp
    simp only [sub_re, one_re]
    rw [hstarRe]
    linarith [s.2.2]⟩

/-- Full shift profile produced from the labeled complete Riemann source by a bounded family of
linear parity carriers. -/
def suzukiSourceParityCarrierProfile
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : ℝ → CompleteResolutionSourceSpace →L[ℂ] F)
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) : ℝ → F :=
  fun lambda => T lambda (completeResolutionSourceEmbedding K s)

/-- A bounded label-blind source-to-parity family gives identical complete shift profiles at
reflected source points. -/
theorem suzukiLabelBlindParityCarrier_reflectionProfiles_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : ℝ → CompleteResolutionSourceSpace →L[ℂ] F)
    (hT : ∀ lambda, SourceLabelBlind (T lambda))
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    suzukiSourceParityCarrierProfile T K ⟨s.1, s.2.1⟩ =
      suzukiSourceParityCarrierProfile T K
        (completeResolutionReflectedSourcePoint s) := by
  funext lambda
  exact sourceLabelBlind_constant_on_completeResolutionSourceEmbedding
    (T lambda) (hT lambda) K _ _

/-- Arbitrary nonlinear downstream processing, including hazard ratios, Jordan credit/debt, and
integrated excursion budgets, remains reflection-blind after bounded label-blind transport. -/
theorem suzukiLabelBlindParityCarrier_postprocessing_reflectionBlind
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {G : Type*}
    (T : ℝ → CompleteResolutionSourceSpace →L[ℂ] F)
    (hT : ∀ lambda, SourceLabelBlind (T lambda))
    (postprocess : (ℝ → F) → G)
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    postprocess
        (suzukiSourceParityCarrierProfile T K ⟨s.1, s.2.1⟩) =
      postprocess
        (suzukiSourceParityCarrierProfile T K
          (completeResolutionReflectedSourcePoint s)) := by
  rw [suzukiLabelBlindParityCarrier_reflectionProfiles_eq T hT K s]

/-- **Suzuki source-provenance gate.** If any downstream statistic separates a source point from
its functional-equation reflection, at least one bounded source-to-parity carrier must distinguish
the high-exponent labels. Thus a reflection-separating Suzuki producer is label-sensitive or
outside the bounded carrier category before scalarization. -/
theorem suzukiReflectionSeparatingPostprocessing_forces_labelSensitive
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {G : Type*}
    (T : ℝ → CompleteResolutionSourceSpace →L[ℂ] F)
    (postprocess : (ℝ → F) → G)
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip)
    (hseparates :
      postprocess
          (suzukiSourceParityCarrierProfile T K ⟨s.1, s.2.1⟩) ≠
        postprocess
          (suzukiSourceParityCarrierProfile T K
            (completeResolutionReflectedSourcePoint s))) :
    ∃ lambda, ¬ SourceLabelBlind (T lambda) := by
  by_contra h
  push Not at h
  exact hseparates
    (suzukiLabelBlindParityCarrier_postprocessing_reflectionBlind
      T h postprocess K s)

end

end RHTower
