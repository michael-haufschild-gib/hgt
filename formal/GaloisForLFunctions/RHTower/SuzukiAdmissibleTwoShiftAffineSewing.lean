import GaloisForLFunctions.RHTower.SuzukiOppositeShiftCrossSewnExterior

/-!
# Suzuki admissible two-shift affine sewing

Suzuki's finite-aperture source space at real form shift `lambda` requires
`lambda < lambda_a`, where `lambda_a` is the unknown spectral floor.  Requiring an opposite
pair `lambda,-lambda` is therefore circular: such a nonzero pair exists exactly when
`lambda_a > 0`.  In contrast, every half-line below an arbitrary real floor contains two
distinct shifts.

This module proves that any two distinct shifted exterior channels recover any target shift by
an exact affine sewing law.  For

`E_eta(W,I) = G_eta W - I`,

put

`C = (beta-gamma) W_beta E_alpha - (alpha-gamma) W_alpha E_beta`.

Then, pointwise and without divisor hypotheses,

`C = E_gamma((beta-alpha) W_alpha W_beta,
  (beta-gamma) W_beta I_alpha - (alpha-gamma) W_alpha I_beta)`.

After projective normalization, changing either admissible source pair changes only an off-real
analytic interval-quotient correction.  Hence the complete nonreal Xi-pole germ is independent of
the source shifts, their gauges, and the chosen target.  At a hypothetical nonreal Xi zero its
order is `-1` and its normalized trailing coefficient is `ord(XiC)/z^2`.

All statements are unconditional.  No positivity of the Suzuki floor, aperture limit, estimate,
RH assumption, or numerical computation is used.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## Source admissibility without a positive floor -/

/-- Centered complex parameter corresponding to Suzuki's real form shift. -/
def suzukiCenteredShiftParameter (lambda : ℝ) : ℂ :=
  -I * (lambda : ℂ)

/-- The real-to-centered shift map loses no source parameter. -/
theorem suzukiCenteredShiftParameter_injective :
    Function.Injective suzukiCenteredShiftParameter := by
  intro alpha beta h
  have him := congrArg Complex.im h
  simp only [suzukiCenteredShiftParameter, mul_im, neg_re, I_re, neg_im, I_im,
    ofReal_re, ofReal_im, mul_zero] at him
  linarith

/-- An opposite pair lies below a real spectral floor exactly when its absolute shift does. -/
theorem suzuki_opposite_shifts_below_iff_abs_lt (lambda floor : ℝ) :
    lambda < floor ∧ -lambda < floor ↔ |lambda| < floor := by
  rw [abs_lt]
  constructor
  · rintro ⟨hplus, hminus⟩
    constructor <;> linarith
  · rintro ⟨hlower, hupper⟩
    constructor <;> linarith

/-- **Circularity certificate.**  A nonzero opposite source pair is admissible exactly when the
unknown spectral floor is positive. -/
theorem exists_nonzero_opposite_suzuki_shifts_below_iff (floor : ℝ) :
    (∃ lambda : ℝ, lambda ≠ 0 ∧ lambda < floor ∧ -lambda < floor) ↔ 0 < floor := by
  constructor
  · rintro ⟨lambda, hlambda, hplus, hminus⟩
    by_cases hsign : 0 < lambda
    · linarith
    · have hneg : lambda < 0 := lt_of_le_of_ne (le_of_not_gt hsign) hlambda
      linarith
  · intro hfloor
    refine ⟨floor / 2, by linarith, by linarith, by linarith⟩

/-- Every spectral floor, even a negative one, admits two distinct real source shifts. -/
theorem exists_distinct_suzuki_shifts_below (floor : ℝ) :
    ∃ alpha beta : ℝ, alpha < floor ∧ beta < floor ∧ alpha ≠ beta := by
  refine ⟨floor - 1, floor - 2, by linarith, by linarith, ?_⟩
  linarith

/-- The two unconditional real source shifts remain distinct after centering. -/
theorem exists_distinct_centered_suzuki_shifts_below (floor : ℝ) :
    ∃ alpha beta : ℝ,
      alpha < floor ∧ beta < floor ∧
        suzukiCenteredShiftParameter alpha ≠ suzukiCenteredShiftParameter beta := by
  obtain ⟨alpha, beta, halpha, hbeta, hab⟩ :=
    exists_distinct_suzuki_shifts_below floor
  exact ⟨alpha, beta, halpha, hbeta,
    fun h => hab (suzukiCenteredShiftParameter_injective h)⟩

/-! ## Exact affine sewing -/

/-- Characteristic product for affine sewing of source shifts `alpha` and `beta`. -/
def suzukiAffineSewnCharacteristic
    (alpha beta : ℂ) (WAlpha WBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  (beta - alpha) * WAlpha z * WBeta z

/-- Affinely sewn finite-interval contribution at target shift `gamma`. -/
def suzukiAffineSewnIntervalPart
    (alpha beta gamma : ℂ)
    (WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  (beta - gamma) * WBeta z * intervalAlpha z -
    (alpha - gamma) * WAlpha z * intervalBeta z

/-- Division-free affine sewing of two unrelated shifted exterior channels. -/
def suzukiAffineSewnExterior
    (alpha beta gamma : ℂ)
    (WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  (beta - gamma) * WBeta z *
      suzukiExteriorRemainder alpha WAlpha intervalAlpha z -
    (alpha - gamma) * WAlpha z *
      suzukiExteriorRemainder beta WBeta intervalBeta z

/-- Projective normalization of the affine-sewn exterior channel. -/
def suzukiAffineSewnNormalizedExterior
    (alpha beta gamma : ℂ)
    (WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiAffineSewnExterior alpha beta gamma
      WAlpha WBeta intervalAlpha intervalBeta z /
    suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z

/-- Barycentric interpolation of the two gauge-invariant interval quotients. -/
def suzukiAffineSewnIntervalQuotient
    (alpha beta gamma : ℂ)
    (WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((beta - gamma) * (intervalAlpha z / WAlpha z) -
      (alpha - gamma) * (intervalBeta z / WBeta z)) /
    (beta - alpha)

/-- The reciprocal shifted-Xi multiplier is an affine line in the shift parameter.  This
totalized identity remains valid at `z=0` and on the Xi divisor. -/
theorem suzukiShiftedXiMultiplier_affine_interpolation
    (alpha beta gamma z : ℂ) :
    (beta - gamma) * suzukiShiftedXiMultiplier alpha z -
        (alpha - gamma) * suzukiShiftedXiMultiplier beta z =
      (beta - alpha) * suzukiShiftedXiMultiplier gamma z := by
  rw [suzukiShiftedXiMultiplier_eq, suzukiShiftedXiMultiplier_eq,
    suzukiShiftedXiMultiplier_eq]
  simp only [suzukiShiftedXiDenominator]
  ring

/-- **Affine sewing law.**  Any two source shifts recover any target-shift exterior channel.
No source shift, target shift, or spectral divisor is excluded. -/
theorem suzukiAffineSewnExterior_eq_targetShift
    (alpha beta gamma : ℂ)
    (WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnExterior alpha beta gamma
        WAlpha WBeta intervalAlpha intervalBeta z =
      suzukiExteriorRemainder gamma
        (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta)
        (suzukiAffineSewnIntervalPart alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta) z := by
  simp only [suzukiAffineSewnExterior, suzukiExteriorRemainder,
    suzukiAffineSewnCharacteristic, suzukiAffineSewnIntervalPart]
  have h := suzukiShiftedXiMultiplier_affine_interpolation alpha beta gamma z
  linear_combination WAlpha z * WBeta z * h

/-- Two arbitrary distinct source shifts reconstruct Suzuki's distinguished zero-shift exterior
channel, even when zero is not source-admissible. -/
theorem suzukiAffineSewnExterior_eq_zeroShift
    (alpha beta : ℂ)
    (WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnExterior alpha beta 0
        WAlpha WBeta intervalAlpha intervalBeta z =
      suzukiExteriorRemainder 0
        (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta)
        (suzukiAffineSewnIntervalPart alpha beta 0
          WAlpha WBeta intervalAlpha intervalBeta) z :=
  suzukiAffineSewnExterior_eq_targetShift alpha beta 0
    WAlpha WBeta intervalAlpha intervalBeta z

/-! ## Independent gauges and projective descent -/

theorem suzukiAffineSewnCharacteristic_independentGauge
    (alpha beta : ℂ) (gAlpha gBeta WAlpha WBeta : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnCharacteristic alpha beta
        (fun w => gAlpha w * WAlpha w) (fun w => gBeta w * WBeta w) z =
      gAlpha z * gBeta z *
        suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z := by
  simp only [suzukiAffineSewnCharacteristic]
  ring

theorem suzukiAffineSewnIntervalPart_independentGauge
    (alpha beta gamma : ℂ)
    (gAlpha gBeta WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnIntervalPart alpha beta gamma
        (fun w => gAlpha w * WAlpha w) (fun w => gBeta w * WBeta w)
        (fun w => gAlpha w * intervalAlpha w)
        (fun w => gBeta w * intervalBeta w) z =
      gAlpha z * gBeta z *
        suzukiAffineSewnIntervalPart alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta z := by
  simp only [suzukiAffineSewnIntervalPart]
  ring

theorem suzukiAffineSewnExterior_independentGauge
    (alpha beta gamma : ℂ)
    (gAlpha gBeta WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnExterior alpha beta gamma
        (fun w => gAlpha w * WAlpha w) (fun w => gBeta w * WBeta w)
        (fun w => gAlpha w * intervalAlpha w)
        (fun w => gBeta w * intervalBeta w) z =
      gAlpha z * gBeta z *
        suzukiAffineSewnExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta z := by
  simp only [suzukiAffineSewnExterior, suzukiExteriorRemainder]
  ring

/-- Independent nonzero source gauges disappear after projective normalization. -/
theorem suzukiAffineSewnNormalizedExterior_independentGauge
    {alpha beta gamma z : ℂ}
    {gAlpha gBeta WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ}
    (hgAlpha : gAlpha z ≠ 0) (hgBeta : gBeta z ≠ 0) :
    suzukiAffineSewnNormalizedExterior alpha beta gamma
        (fun w => gAlpha w * WAlpha w) (fun w => gBeta w * WBeta w)
        (fun w => gAlpha w * intervalAlpha w)
        (fun w => gBeta w * intervalBeta w) z =
      suzukiAffineSewnNormalizedExterior alpha beta gamma
        WAlpha WBeta intervalAlpha intervalBeta z := by
  rw [suzukiAffineSewnNormalizedExterior, suzukiAffineSewnNormalizedExterior,
    suzukiAffineSewnExterior_independentGauge,
    suzukiAffineSewnCharacteristic_independentGauge]
  exact mul_div_mul_left _ _ (mul_ne_zero hgAlpha hgBeta)

/-- Barycentric interval quotient is separately invariant under both nonzero gauges. -/
theorem suzukiAffineSewnIntervalQuotient_independentGauge
    {alpha beta gamma z : ℂ}
    {gAlpha gBeta WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ}
    (hgAlpha : gAlpha z ≠ 0) (hgBeta : gBeta z ≠ 0) :
    suzukiAffineSewnIntervalQuotient alpha beta gamma
        (fun w => gAlpha w * WAlpha w) (fun w => gBeta w * WBeta w)
        (fun w => gAlpha w * intervalAlpha w)
        (fun w => gBeta w * intervalBeta w) z =
      suzukiAffineSewnIntervalQuotient alpha beta gamma
        WAlpha WBeta intervalAlpha intervalBeta z := by
  simp only [suzukiAffineSewnIntervalQuotient]
  rw [mul_div_mul_left _ _ hgAlpha, mul_div_mul_left _ _ hgBeta]

/-- **Projective affine descent.**  Away from characteristic divisors, normalized sewing is the
target Xi multiplier minus a barycentric interpolation of source interval quotients. -/
theorem suzukiAffineSewnNormalizedExterior_eq_targetShift
    {alpha beta gamma z : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : WAlpha z ≠ 0) (hWBeta : WBeta z ≠ 0) :
    suzukiAffineSewnNormalizedExterior alpha beta gamma
        WAlpha WBeta intervalAlpha intervalBeta z =
      suzukiShiftedXiMultiplier gamma z -
        suzukiAffineSewnIntervalQuotient alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta z := by
  rw [suzukiAffineSewnNormalizedExterior,
    suzukiAffineSewnExterior_eq_targetShift]
  simp only [suzukiExteriorRemainder, suzukiAffineSewnCharacteristic,
    suzukiAffineSewnIntervalPart, suzukiAffineSewnIntervalQuotient]
  have hba : beta - alpha ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp [hba, hWAlpha, hWBeta]

/-! ## Analytic closure and pair-choice descent -/

theorem analyticAt_suzukiAffineSewnCharacteristic
    {alpha beta : ℂ} {WAlpha WBeta : ℂ → ℂ} {z : ℂ}
    (hWAlpha : AnalyticAt ℂ WAlpha z) (hWBeta : AnalyticAt ℂ WBeta z) :
    AnalyticAt ℂ (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta) z := by
  exact (analyticAt_const.mul hWAlpha).mul hWBeta

theorem analyticAt_suzukiAffineSewnIntervalPart
    {alpha beta gamma : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ} {z : ℂ}
    (hWAlpha : AnalyticAt ℂ WAlpha z) (hWBeta : AnalyticAt ℂ WBeta z)
    (hIAlpha : AnalyticAt ℂ intervalAlpha z)
    (hIBeta : AnalyticAt ℂ intervalBeta z) :
    AnalyticAt ℂ
      (suzukiAffineSewnIntervalPart alpha beta gamma
        WAlpha WBeta intervalAlpha intervalBeta) z := by
  exact ((analyticAt_const.mul hWBeta).mul hIAlpha).sub
    ((analyticAt_const.mul hWAlpha).mul hIBeta)

theorem analyticAt_suzukiAffineSewnIntervalQuotient
    {alpha beta gamma : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ} {z : ℂ}
    (hWAlpha : AnalyticAt ℂ WAlpha z) (hWAlpha0 : WAlpha z ≠ 0)
    (hWBeta : AnalyticAt ℂ WBeta z) (hWBeta0 : WBeta z ≠ 0)
    (hIAlpha : AnalyticAt ℂ intervalAlpha z)
    (hIBeta : AnalyticAt ℂ intervalBeta z) :
    AnalyticAt ℂ
      (suzukiAffineSewnIntervalQuotient alpha beta gamma
        WAlpha WBeta intervalAlpha intervalBeta) z := by
  unfold suzukiAffineSewnIntervalQuotient
  exact ((analyticAt_const.mul (hIAlpha.div hWAlpha hWAlpha0)).sub
    (analyticAt_const.mul (hIBeta.div hWBeta hWBeta0))).div_const

/-- Product characteristic is nonzero off the real line when both source characteristics have
only real zeros and the shifts are distinct. -/
theorem suzukiAffineSewnCharacteristic_ne_zero_of_im_ne_zero
    {alpha beta : ℂ} {WAlpha WBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hrealAlpha : ∀ z, WAlpha z = 0 → z.im = 0)
    (hrealBeta : ∀ z, WBeta z = 0 → z.im = 0)
    {z : ℂ} (hz : z.im ≠ 0) :
    suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr hab.symm)
      (fun h => hz (hrealAlpha z h)))
    (fun h => hz (hrealBeta z h))

theorem suzukiAffineSewnCharacteristic_zero_im
    {alpha beta : ℂ} {WAlpha WBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hrealAlpha : ∀ z, WAlpha z = 0 → z.im = 0)
    (hrealBeta : ∀ z, WBeta z = 0 → z.im = 0)
    {z : ℂ}
    (hz : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z = 0) :
    z.im = 0 := by
  by_contra hzIm
  exact suzukiAffineSewnCharacteristic_ne_zero_of_im_ne_zero
    hab hrealAlpha hrealBeta hzIm hz

/-- Exact pair-change law: source-pair dependence is entirely in interval quotients; the target
Xi multiplier cancels. -/
theorem suzukiAffineSewnNormalizedExterior_pairChange
    {alpha beta delta epsilon gamma z : ℂ}
    {WAlpha WBeta WDelta WEpsilon intervalAlpha intervalBeta intervalDelta intervalEpsilon :
      ℂ → ℂ}
    (hab : alpha ≠ beta) (hde : delta ≠ epsilon)
    (hWAlpha : WAlpha z ≠ 0) (hWBeta : WBeta z ≠ 0)
    (hWDelta : WDelta z ≠ 0) (hWEpsilon : WEpsilon z ≠ 0) :
    suzukiAffineSewnNormalizedExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta z -
        suzukiAffineSewnNormalizedExterior delta epsilon gamma
          WDelta WEpsilon intervalDelta intervalEpsilon z =
      suzukiAffineSewnIntervalQuotient delta epsilon gamma
          WDelta WEpsilon intervalDelta intervalEpsilon z -
        suzukiAffineSewnIntervalQuotient alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta z := by
  rw [suzukiAffineSewnNormalizedExterior_eq_targetShift hab hWAlpha hWBeta,
    suzukiAffineSewnNormalizedExterior_eq_targetShift hde hWDelta hWEpsilon]
  ring

/-- **Off-real pair-choice invariance.**  For analytic all-real source characteristics, the
normalized channels from any two distinct shift pairs are analytic at exactly the same nonreal
points.  Thus arbitrary admissible shift selection cannot change the RH-bearing singular germ. -/
theorem analyticAt_suzukiAffineSewnNormalizedExterior_pair_iff
    {alpha beta delta epsilon gamma z : ℂ}
    {WAlpha WBeta WDelta WEpsilon intervalAlpha intervalBeta intervalDelta intervalEpsilon :
      ℂ → ℂ}
    (hab : alpha ≠ beta) (hde : delta ≠ epsilon)
    (hz : z.im ≠ 0)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hWDelta : ∀ w, AnalyticAt ℂ WDelta w)
    (hWEpsilon : ∀ w, AnalyticAt ℂ WEpsilon w)
    (hIAlpha : ∀ w, AnalyticAt ℂ intervalAlpha w)
    (hIBeta : ∀ w, AnalyticAt ℂ intervalBeta w)
    (hIDelta : ∀ w, AnalyticAt ℂ intervalDelta w)
    (hIEpsilon : ∀ w, AnalyticAt ℂ intervalEpsilon w)
    (hrealAlpha : ∀ w, WAlpha w = 0 → w.im = 0)
    (hrealBeta : ∀ w, WBeta w = 0 → w.im = 0)
    (hrealDelta : ∀ w, WDelta w = 0 → w.im = 0)
    (hrealEpsilon : ∀ w, WEpsilon w = 0 → w.im = 0) :
    AnalyticAt ℂ
        (suzukiAffineSewnNormalizedExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta) z ↔
      AnalyticAt ℂ
        (suzukiAffineSewnNormalizedExterior delta epsilon gamma
          WDelta WEpsilon intervalDelta intervalEpsilon) z := by
  have hA0 : WAlpha z ≠ 0 := fun h => hz (hrealAlpha z h)
  have hB0 : WBeta z ≠ 0 := fun h => hz (hrealBeta z h)
  have hD0 : WDelta z ≠ 0 := fun h => hz (hrealDelta z h)
  have hE0 : WEpsilon z ≠ 0 := fun h => hz (hrealEpsilon z h)
  let QA := suzukiAffineSewnIntervalQuotient alpha beta gamma
    WAlpha WBeta intervalAlpha intervalBeta
  let QD := suzukiAffineSewnIntervalQuotient delta epsilon gamma
    WDelta WEpsilon intervalDelta intervalEpsilon
  have hQA : AnalyticAt ℂ QA z :=
    analyticAt_suzukiAffineSewnIntervalQuotient
      (hWAlpha z) hA0 (hWBeta z) hB0 (hIAlpha z) (hIBeta z)
  have hQD : AnalyticAt ℂ QD z :=
    analyticAt_suzukiAffineSewnIntervalQuotient
      (hWDelta z) hD0 (hWEpsilon z) hE0 (hIDelta z) (hIEpsilon z)
  have hAevent : ∀ᶠ w in 𝓝 z, WAlpha w ≠ 0 :=
    (hWAlpha z).continuousAt.eventually_ne hA0
  have hBevent : ∀ᶠ w in 𝓝 z, WBeta w ≠ 0 :=
    (hWBeta z).continuousAt.eventually_ne hB0
  have hDevent : ∀ᶠ w in 𝓝 z, WDelta w ≠ 0 :=
    (hWDelta z).continuousAt.eventually_ne hD0
  have hEevent : ∀ᶠ w in 𝓝 z, WEpsilon w ≠ 0 :=
    (hWEpsilon z).continuousAt.eventually_ne hE0
  have hpair :
      (fun w =>
        suzukiAffineSewnNormalizedExterior alpha beta gamma
            WAlpha WBeta intervalAlpha intervalBeta w -
          suzukiAffineSewnNormalizedExterior delta epsilon gamma
            WDelta WEpsilon intervalDelta intervalEpsilon w) =ᶠ[𝓝 z]
        fun w => QD w - QA w := by
    filter_upwards [hAevent, hBevent, hDevent, hEevent] with w hAw hBw hDw hEw
    exact suzukiAffineSewnNormalizedExterior_pairChange
      hab hde hAw hBw hDw hEw
  have hdiff : AnalyticAt ℂ (fun w =>
      suzukiAffineSewnNormalizedExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta w -
        suzukiAffineSewnNormalizedExterior delta epsilon gamma
          WDelta WEpsilon intervalDelta intervalEpsilon w) z :=
    (hQD.sub hQA).congr hpair.symm
  constructor
  · intro hA
    have hmodel := hA.sub hdiff
    apply hmodel.congr
    filter_upwards with w
    simp only [Pi.sub_apply]
    ring
  · intro hD
    have hmodel := hD.add hdiff
    apply hmodel.congr
    filter_upwards with w
    simp only [Pi.add_apply]
    ring

/-! ## RH criteria for arbitrary admissible shift pairs -/

theorem riemannHypothesis_iff_suzukiAffineSewnExterior_analytic_offReal
    {alpha beta gamma : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ z, AnalyticAt ℂ WAlpha z)
    (hWBeta : ∀ z, AnalyticAt ℂ WBeta z)
    (hIAlpha : ∀ z, AnalyticAt ℂ intervalAlpha z)
    (hIBeta : ∀ z, AnalyticAt ℂ intervalBeta z)
    (hrealAlpha : ∀ z, WAlpha z = 0 → z.im = 0)
    (hrealBeta : ∀ z, WBeta z = 0 → z.im = 0) :
    RiemannHypothesis ↔
      ∀ z : ℂ, z.im ≠ 0 →
        AnalyticAt ℂ
          (suzukiAffineSewnExterior alpha beta gamma
            WAlpha WBeta intervalAlpha intervalBeta) z := by
  have hP : ∀ z, AnalyticAt ℂ
      (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta) z := fun z =>
    analyticAt_suzukiAffineSewnCharacteristic (hWAlpha z) (hWBeta z)
  have hJ : ∀ z, AnalyticAt ℂ
      (suzukiAffineSewnIntervalPart alpha beta gamma
        WAlpha WBeta intervalAlpha intervalBeta) z := fun z =>
    analyticAt_suzukiAffineSewnIntervalPart
      (hWAlpha z) (hWBeta z) (hIAlpha z) (hIBeta z)
  have hrealP : ∀ z,
      suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z = 0 → z.im = 0 :=
    fun _ => suzukiAffineSewnCharacteristic_zero_im hab hrealAlpha hrealBeta
  have hcriterion :=
    riemannHypothesis_iff_suzukiExteriorRemainder_analytic_offReal_of_realZeros
      (eta := gamma) hP hJ hrealP
  have hsew :
      suzukiAffineSewnExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta =
        suzukiExteriorRemainder gamma
          (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta)
          (suzukiAffineSewnIntervalPart alpha beta gamma
            WAlpha WBeta intervalAlpha intervalBeta) := by
    funext z
    exact suzukiAffineSewnExterior_eq_targetShift
      alpha beta gamma WAlpha WBeta intervalAlpha intervalBeta z
  rw [hsew]
  exact hcriterion

theorem riemannHypothesis_iff_suzukiAffineSewnNormalizedExterior_analytic_offReal
    {alpha beta gamma : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ z, AnalyticAt ℂ WAlpha z)
    (hWBeta : ∀ z, AnalyticAt ℂ WBeta z)
    (hIAlpha : ∀ z, AnalyticAt ℂ intervalAlpha z)
    (hIBeta : ∀ z, AnalyticAt ℂ intervalBeta z)
    (hrealAlpha : ∀ z, WAlpha z = 0 → z.im = 0)
    (hrealBeta : ∀ z, WBeta z = 0 → z.im = 0) :
    RiemannHypothesis ↔
      ∀ z : ℂ, z.im ≠ 0 →
        AnalyticAt ℂ
          (suzukiAffineSewnNormalizedExterior alpha beta gamma
            WAlpha WBeta intervalAlpha intervalBeta) z := by
  have hsew := riemannHypothesis_iff_suzukiAffineSewnExterior_analytic_offReal
    hab hWAlpha hWBeta hIAlpha hIBeta hrealAlpha hrealBeta (gamma := gamma)
  constructor
  · intro hRH z hz
    have hC := hsew.mp hRH z hz
    have hP := analyticAt_suzukiAffineSewnCharacteristic
      (alpha := alpha) (beta := beta)
      (hWAlpha z) (hWBeta z)
    have hP0 := suzukiAffineSewnCharacteristic_ne_zero_of_im_ne_zero
      hab hrealAlpha hrealBeta hz
    exact hC.div hP hP0
  · intro hN
    apply hsew.mpr
    intro z hz
    have hP := analyticAt_suzukiAffineSewnCharacteristic
      (alpha := alpha) (beta := beta)
      (hWAlpha z) (hWBeta z)
    have hP0 := suzukiAffineSewnCharacteristic_ne_zero_of_im_ne_zero
      hab hrealAlpha hrealBeta hz
    have hprod := hP.mul (hN z hz)
    apply hprod.congr
    filter_upwards [hP.continuousAt.eventually_ne hP0] with w hw
    change suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta w *
        (suzukiAffineSewnExterior alpha beta gamma
            WAlpha WBeta intervalAlpha intervalBeta w /
          suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta w) =
      suzukiAffineSewnExterior alpha beta gamma
        WAlpha WBeta intervalAlpha intervalBeta w
    rw [mul_comm, div_mul_cancel₀ _ hw]

/-! ## Universal Xi-pole germ -/

theorem meromorphicOrderAt_suzukiAffineSewnExterior_eq_neg_one
    {alpha beta gamma z : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ}
    (hab : alpha ≠ beta) (hz : XiC z = 0)
    (hWAlpha : AnalyticAt ℂ WAlpha z) (hWAlpha0 : WAlpha z ≠ 0)
    (hWBeta : AnalyticAt ℂ WBeta z) (hWBeta0 : WBeta z ≠ 0)
    (hIAlpha : AnalyticAt ℂ intervalAlpha z)
    (hIBeta : AnalyticAt ℂ intervalBeta z) :
    meromorphicOrderAt
        (suzukiAffineSewnExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta) z =
      ((-1 : ℤ) : WithTop ℤ) := by
  have hP := analyticAt_suzukiAffineSewnCharacteristic
    (alpha := alpha) (beta := beta) hWAlpha hWBeta
  have hP0 : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) hWAlpha0) hWBeta0
  have hJ := analyticAt_suzukiAffineSewnIntervalPart
    (alpha := alpha) (beta := beta) (gamma := gamma)
    hWAlpha hWBeta hIAlpha hIBeta
  have hsew :
      suzukiAffineSewnExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta =
        suzukiExteriorRemainder gamma
          (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta)
          (suzukiAffineSewnIntervalPart alpha beta gamma
            WAlpha WBeta intervalAlpha intervalBeta) := by
    funext w
    exact suzukiAffineSewnExterior_eq_targetShift
      alpha beta gamma WAlpha WBeta intervalAlpha intervalBeta w
  rw [hsew]
  exact meromorphicOrderAt_suzukiExteriorRemainder_eq_neg_one hz hP hP0 hJ

theorem meromorphicTrailingCoeffAt_suzukiAffineSewnExterior
    {alpha beta gamma z : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ}
    (hab : alpha ≠ beta) (hz : XiC z = 0)
    (hWAlpha : AnalyticAt ℂ WAlpha z) (hWAlpha0 : WAlpha z ≠ 0)
    (hWBeta : AnalyticAt ℂ WBeta z) (hWBeta0 : WBeta z ≠ 0)
    (hIAlpha : AnalyticAt ℂ intervalAlpha z)
    (hIBeta : AnalyticAt ℂ intervalBeta z) :
    meromorphicTrailingCoeffAt
        (suzukiAffineSewnExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta) z =
      ((analyticOrderAt XiC z).toNat : ℂ) *
        suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z / z ^ 2 := by
  have hP := analyticAt_suzukiAffineSewnCharacteristic
    (alpha := alpha) (beta := beta) hWAlpha hWBeta
  have hP0 : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) hWAlpha0) hWBeta0
  have hJ := analyticAt_suzukiAffineSewnIntervalPart
    (alpha := alpha) (beta := beta) (gamma := gamma)
    hWAlpha hWBeta hIAlpha hIBeta
  have hsew :
      suzukiAffineSewnExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta =
        suzukiExteriorRemainder gamma
          (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta)
          (suzukiAffineSewnIntervalPart alpha beta gamma
            WAlpha WBeta intervalAlpha intervalBeta) := by
    funext w
    exact suzukiAffineSewnExterior_eq_targetShift
      alpha beta gamma WAlpha WBeta intervalAlpha intervalBeta w
  rw [hsew]
  exact meromorphicTrailingCoeffAt_suzukiExteriorRemainder hz hP hP0 hJ

theorem meromorphicOrderAt_suzukiAffineSewnNormalizedExterior_eq_neg_one
    {alpha beta gamma z : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ}
    (hab : alpha ≠ beta) (hz : XiC z = 0)
    (hWAlpha : AnalyticAt ℂ WAlpha z) (hWAlpha0 : WAlpha z ≠ 0)
    (hWBeta : AnalyticAt ℂ WBeta z) (hWBeta0 : WBeta z ≠ 0)
    (hIAlpha : AnalyticAt ℂ intervalAlpha z)
    (hIBeta : AnalyticAt ℂ intervalBeta z) :
    meromorphicOrderAt
        (suzukiAffineSewnNormalizedExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta) z =
      ((-1 : ℤ) : WithTop ℤ) := by
  let C := suzukiAffineSewnExterior alpha beta gamma
    WAlpha WBeta intervalAlpha intervalBeta
  let P := suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta
  have hP : AnalyticAt ℂ P z :=
    analyticAt_suzukiAffineSewnCharacteristic
      (alpha := alpha) (beta := beta) hWAlpha hWBeta
  have hP0 : P z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) hWAlpha0) hWBeta0
  have hJ := analyticAt_suzukiAffineSewnIntervalPart
    (alpha := alpha) (beta := beta) (gamma := gamma)
    hWAlpha hWBeta hIAlpha hIBeta
  have hCeq : C = suzukiExteriorRemainder gamma P
      (suzukiAffineSewnIntervalPart alpha beta gamma
        WAlpha WBeta intervalAlpha intervalBeta) := by
    funext w
    exact suzukiAffineSewnExterior_eq_targetShift
      alpha beta gamma WAlpha WBeta intervalAlpha intervalBeta w
  have hC : MeromorphicAt C z := by
    rw [hCeq]
    exact (meromorphicAt_suzukiShiftedXiMultiplier gamma z).mul hP.meromorphicAt |>.sub
      hJ.meromorphicAt
  have hCorder : meromorphicOrderAt C z = ((-1 : ℤ) : WithTop ℤ) := by
    dsimp only [C]
    exact meromorphicOrderAt_suzukiAffineSewnExterior_eq_neg_one
      hab hz hWAlpha hWAlpha0 hWBeta hWBeta0 hIAlpha hIBeta
  have hPorder : meromorphicOrderAt P z = 0 := by
    rw [hP.meromorphicOrderAt_eq, hP.analyticOrderAt_eq_zero.mpr hP0]
    simp
  change meromorphicOrderAt (fun w => C w / P w) z = ((-1 : ℤ) : WithTop ℤ)
  rw [fun_meromorphicOrderAt_div hC hP.meromorphicAt, hCorder, hPorder]
  norm_num

/-- **Universal affine-sewn Xi-pole invariant.**  Projective normalization erases both source
shifts, the target shift, characteristic functions, interval terms, and independent gauges. -/
theorem meromorphicTrailingCoeffAt_suzukiAffineSewnNormalizedExterior
    {alpha beta gamma z : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta : ℂ → ℂ}
    (hab : alpha ≠ beta) (hz : XiC z = 0)
    (hWAlpha : AnalyticAt ℂ WAlpha z) (hWAlpha0 : WAlpha z ≠ 0)
    (hWBeta : AnalyticAt ℂ WBeta z) (hWBeta0 : WBeta z ≠ 0)
    (hIAlpha : AnalyticAt ℂ intervalAlpha z)
    (hIBeta : AnalyticAt ℂ intervalBeta z) :
    meromorphicTrailingCoeffAt
        (suzukiAffineSewnNormalizedExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta) z =
      ((analyticOrderAt XiC z).toNat : ℂ) / z ^ 2 := by
  let C := suzukiAffineSewnExterior alpha beta gamma
    WAlpha WBeta intervalAlpha intervalBeta
  let P := suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta
  have hP : AnalyticAt ℂ P z :=
    analyticAt_suzukiAffineSewnCharacteristic
      (alpha := alpha) (beta := beta) hWAlpha hWBeta
  have hP0 : P z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) hWAlpha0) hWBeta0
  have hJ := analyticAt_suzukiAffineSewnIntervalPart
    (alpha := alpha) (beta := beta) (gamma := gamma)
    hWAlpha hWBeta hIAlpha hIBeta
  have hCeq : C = suzukiExteriorRemainder gamma P
      (suzukiAffineSewnIntervalPart alpha beta gamma
        WAlpha WBeta intervalAlpha intervalBeta) := by
    funext w
    exact suzukiAffineSewnExterior_eq_targetShift
      alpha beta gamma WAlpha WBeta intervalAlpha intervalBeta w
  have hC : MeromorphicAt C z := by
    rw [hCeq]
    exact (meromorphicAt_suzukiShiftedXiMultiplier gamma z).mul hP.meromorphicAt |>.sub
      hJ.meromorphicAt
  have hCtrail : meromorphicTrailingCoeffAt C z =
      ((analyticOrderAt XiC z).toNat : ℂ) * P z / z ^ 2 := by
    dsimp only [C, P]
    exact meromorphicTrailingCoeffAt_suzukiAffineSewnExterior
      hab hz hWAlpha hWAlpha0 hWBeta hWBeta0 hIAlpha hIBeta
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact XiC_zero_ne hz
  have htrailDiv : meromorphicTrailingCoeffAt (C / P) z =
      ((analyticOrderAt XiC z).toNat : ℂ) / z ^ 2 := by
    rw [div_eq_mul_inv,
      hC.meromorphicTrailingCoeffAt_mul hP.meromorphicAt.inv,
      meromorphicTrailingCoeffAt_inv, hCtrail,
      hP.meromorphicTrailingCoeffAt_of_ne_zero hP0]
    field_simp [hP0, hz0]
  exact htrailDiv

/-! ## Opposite sewing is one nonzero specialization -/

theorem suzukiAffineSewnExterior_opposite_eq
    (eta : ℂ) (WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnExterior eta (-eta) 0
        WPlus WMinus intervalPlus intervalMinus z =
      -eta * suzukiCrossSewnExterior eta
        WPlus WMinus intervalPlus intervalMinus z := by
  simp only [suzukiAffineSewnExterior, suzukiCrossSewnExterior]
  ring

theorem suzukiAffineSewnCharacteristic_opposite_eq
    (eta : ℂ) (WPlus WMinus : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnCharacteristic eta (-eta) WPlus WMinus z =
      -eta * suzukiCrossSewnCharacteristic WPlus WMinus z := by
  simp only [suzukiAffineSewnCharacteristic, suzukiCrossSewnCharacteristic]
  ring

/-- For a nonzero opposite shift, affine normalization recovers the previous cross-sewn channel
exactly. -/
theorem suzukiAffineSewnNormalizedExterior_opposite_eq
    {eta z : ℂ} {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ}
    (heta : eta ≠ 0) :
    suzukiAffineSewnNormalizedExterior eta (-eta) 0
        WPlus WMinus intervalPlus intervalMinus z =
      suzukiCrossSewnNormalizedExterior eta
        WPlus WMinus intervalPlus intervalMinus z := by
  rw [suzukiAffineSewnNormalizedExterior,
    suzukiAffineSewnExterior_opposite_eq,
    suzukiAffineSewnCharacteristic_opposite_eq,
    suzukiCrossSewnNormalizedExterior]
  exact mul_div_mul_left _ _ (neg_ne_zero.mpr heta)

end

end RHTower
