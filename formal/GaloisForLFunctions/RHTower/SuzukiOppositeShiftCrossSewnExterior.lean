import GaloisForLFunctions.RHTower.SuzukiOppositeShiftParityHarmonicRecovery

/-!
# Suzuki opposite-shift cross-sewn exterior product

Actual finite-aperture source channels at opposite shifts need not have the same characteristic
function, interval contribution, or entire gauge.  Common-channel averaging therefore does not by
itself model Suzuki's source pair.

This module replaces that premise by a division-free cross-sewing.  If

`E_eta(W,I) = G_eta W - I`,

then arbitrary opposite channels satisfy

`W_- E_eta(W_+,I_+) + W_+ E_(-eta)(W_-,I_-)
  = E_0(2 W_+ W_-, W_- I_+ + W_+ I_-)`.

The product characteristic has only real zeros whenever both factors do.  Cross-sewing is
covariant under two unrelated gauges, and division by the product characteristic produces a
projectively gauge-invariant channel.  At every hypothetical nonreal Xi zero its pole is simple
and its trailing coefficient is the universal value `ord(XiC) / z²`, independent of shift,
characteristic functions, interval terms, and gauges.

Consequently RH is equivalent to off-real analyticity of either the cross-sewn channel or its
projective normalization.  These equivalences do not assert that source analyticity; they isolate
the exact distinct-channel producer statement still missing from Suzuki's route.

All results are unconditional.  No limit, estimate, RH assumption, or numerical computation is
used.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## Distinct-channel cross-sewing -/

/-- Product characteristic obtained by sewing two unrelated opposite-shift source lines. -/
def suzukiCrossSewnCharacteristic
    (WPlus WMinus : ℂ → ℂ) (z : ℂ) : ℂ :=
  2 * WPlus z * WMinus z

/-- Entire interval contribution compatible with the cross-sewn product characteristic. -/
def suzukiCrossSewnIntervalPart
    (WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ) (z : ℂ) : ℂ :=
  WMinus z * intervalPlus z + WPlus z * intervalMinus z

/-- Division-free cross-sewn exterior channel for genuinely different opposite-shift sources. -/
def suzukiCrossSewnExterior
    (eta : ℂ) (WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ) (z : ℂ) : ℂ :=
  WMinus z * suzukiExteriorRemainder eta WPlus intervalPlus z +
    WPlus z * suzukiExteriorRemainder (-eta) WMinus intervalMinus z

/-- Projective normalization of the cross-sewn channel by its product characteristic. -/
def suzukiCrossSewnNormalizedExterior
    (eta : ℂ) (WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus z /
    suzukiCrossSewnCharacteristic WPlus WMinus z

/-- **Cross-sewing law.**  Arbitrary distinct opposite-shift exterior channels project exactly to
one zero-shift exterior remainder with product characteristic.  The identity is pointwise
totalized and has no nonvanishing premise. -/
theorem suzukiCrossSewnExterior_eq_zeroShift
    (eta : ℂ) (WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ) (z : ℂ) :
    suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus z =
      suzukiExteriorRemainder 0
        (suzukiCrossSewnCharacteristic WPlus WMinus)
        (suzukiCrossSewnIntervalPart WPlus WMinus intervalPlus intervalMinus) z := by
  simp only [suzukiCrossSewnExterior, suzukiExteriorRemainder,
    suzukiCrossSewnCharacteristic, suzukiCrossSewnIntervalPart]
  have h := suzukiShiftedXiMultiplier_opposite_average eta z
  linear_combination WPlus z * WMinus z * h

/-! ## Two independent gauges and projective descent -/

/-- Product characteristic is covariant under two unrelated pointwise gauges. -/
theorem suzukiCrossSewnCharacteristic_independentGauge
    (gPlus gMinus WPlus WMinus : ℂ → ℂ) (z : ℂ) :
    suzukiCrossSewnCharacteristic
        (fun w => gPlus w * WPlus w) (fun w => gMinus w * WMinus w) z =
      gPlus z * gMinus z * suzukiCrossSewnCharacteristic WPlus WMinus z := by
  simp only [suzukiCrossSewnCharacteristic]
  ring

/-- Cross interval contribution has the same independent-gauge covariance. -/
theorem suzukiCrossSewnIntervalPart_independentGauge
    (gPlus gMinus WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ) (z : ℂ) :
    suzukiCrossSewnIntervalPart
        (fun w => gPlus w * WPlus w) (fun w => gMinus w * WMinus w)
        (fun w => gPlus w * intervalPlus w) (fun w => gMinus w * intervalMinus w) z =
      gPlus z * gMinus z *
        suzukiCrossSewnIntervalPart WPlus WMinus intervalPlus intervalMinus z := by
  simp only [suzukiCrossSewnIntervalPart]
  ring

/-- Cross-sewn exterior channel is covariant under two unrelated pointwise gauges.  No
nonvanishing or analyticity premise is needed for this polynomial identity. -/
theorem suzukiCrossSewnExterior_independentGauge
    (eta : ℂ) (gPlus gMinus WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ) (z : ℂ) :
    suzukiCrossSewnExterior eta
        (fun w => gPlus w * WPlus w) (fun w => gMinus w * WMinus w)
        (fun w => gPlus w * intervalPlus w) (fun w => gMinus w * intervalMinus w) z =
      gPlus z * gMinus z *
        suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus z := by
  simp only [suzukiCrossSewnExterior, suzukiExteriorRemainder]
  ring

/-- After division by product characteristic, independent nonzero gauges disappear pointwise. -/
theorem suzukiCrossSewnNormalizedExterior_independentGauge
    {eta z : ℂ} {gPlus gMinus WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ}
    (hgPlus : gPlus z ≠ 0) (hgMinus : gMinus z ≠ 0) :
    suzukiCrossSewnNormalizedExterior eta
        (fun w => gPlus w * WPlus w) (fun w => gMinus w * WMinus w)
        (fun w => gPlus w * intervalPlus w) (fun w => gMinus w * intervalMinus w) z =
      suzukiCrossSewnNormalizedExterior eta
        WPlus WMinus intervalPlus intervalMinus z := by
  rw [suzukiCrossSewnNormalizedExterior, suzukiCrossSewnNormalizedExterior,
    suzukiCrossSewnExterior_independentGauge,
    suzukiCrossSewnCharacteristic_independentGauge]
  exact mul_div_mul_left _ _ (mul_ne_zero hgPlus hgMinus)

/-- **Projective shift elimination.**  Away from the two characteristic divisors, normalized
cross-sewing removes the explicit opposite shift and is the zero-shift multiplier minus the
average of two independently gauge-invariant interval quotients. -/
theorem suzukiCrossSewnNormalizedExterior_eq_zeroShift
    {eta z : ℂ} {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ}
    (hWPlus : WPlus z ≠ 0) (hWMinus : WMinus z ≠ 0) :
    suzukiCrossSewnNormalizedExterior eta
        WPlus WMinus intervalPlus intervalMinus z =
      suzukiShiftedXiMultiplier 0 z -
        (2 : ℂ)⁻¹ * (intervalPlus z / WPlus z + intervalMinus z / WMinus z) := by
  rw [suzukiCrossSewnNormalizedExterior,
    suzukiCrossSewnExterior_eq_zeroShift]
  simp only [suzukiExteriorRemainder, suzukiCrossSewnCharacteristic,
    suzukiCrossSewnIntervalPart]
  field_simp [hWPlus, hWMinus]

/-! ## Analytic and real-zero closure -/

theorem analyticAt_suzukiCrossSewnCharacteristic
    {WPlus WMinus : ℂ → ℂ} {z : ℂ}
    (hWPlus : AnalyticAt ℂ WPlus z) (hWMinus : AnalyticAt ℂ WMinus z) :
    AnalyticAt ℂ (suzukiCrossSewnCharacteristic WPlus WMinus) z := by
  exact (analyticAt_const.mul hWPlus).mul hWMinus

theorem analyticAt_suzukiCrossSewnIntervalPart
    {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ} {z : ℂ}
    (hWPlus : AnalyticAt ℂ WPlus z) (hWMinus : AnalyticAt ℂ WMinus z)
    (hIPlus : AnalyticAt ℂ intervalPlus z) (hIMinus : AnalyticAt ℂ intervalMinus z) :
    AnalyticAt ℂ
      (suzukiCrossSewnIntervalPart WPlus WMinus intervalPlus intervalMinus) z := by
  exact (hWMinus.mul hIPlus).add (hWPlus.mul hIMinus)

/-- Product characteristic is nonzero at every nonreal point when each factor has only real
zeros. -/
theorem suzukiCrossSewnCharacteristic_ne_zero_of_im_ne_zero
    {WPlus WMinus : ℂ → ℂ}
    (hrealPlus : ∀ z, WPlus z = 0 → z.im = 0)
    (hrealMinus : ∀ z, WMinus z = 0 → z.im = 0)
    {z : ℂ} (hz : z.im ≠ 0) :
    suzukiCrossSewnCharacteristic WPlus WMinus z ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (fun h => hz (hrealPlus z h)))
    (fun h => hz (hrealMinus z h))

/-- Product of two all-real characteristic divisors again has only real zeros. -/
theorem suzukiCrossSewnCharacteristic_zero_im
    {WPlus WMinus : ℂ → ℂ}
    (hrealPlus : ∀ z, WPlus z = 0 → z.im = 0)
    (hrealMinus : ∀ z, WMinus z = 0 → z.im = 0)
    {z : ℂ} (hz : suzukiCrossSewnCharacteristic WPlus WMinus z = 0) :
    z.im = 0 := by
  by_contra hzIm
  exact suzukiCrossSewnCharacteristic_ne_zero_of_im_ne_zero
    hrealPlus hrealMinus hzIm hz

/-! ## Generic and cross-sewn RH criteria -/

/-- Generic real-zero form of exterior pole tomography.  The all-angle pencil used by the parent
theorem is sufficient but not necessary: one analytic characteristic factor with no nonreal zeros
already gives the exact RH criterion. -/
theorem riemannHypothesis_iff_suzukiExteriorRemainder_analytic_offReal_of_realZeros
    {W intervalPart : ℂ → ℂ} {eta : ℂ}
    (hW : ∀ z, AnalyticAt ℂ W z) (hI : ∀ z, AnalyticAt ℂ intervalPart z)
    (hreal : ∀ z, W z = 0 → z.im = 0) :
    RiemannHypothesis ↔
      ∀ z : ℂ, z.im ≠ 0 →
        AnalyticAt ℂ (suzukiExteriorRemainder eta W intervalPart) z := by
  constructor
  · intro hRH z hzIm
    have hXi : XiC z ≠ 0 := by
      intro hzero
      exact hzIm
        ((SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero.mp hRH) z hzero)
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      exact hzIm (by simp)
    exact (analyticAt_suzukiShiftedXiMultiplier_of_XiC_ne_zero
      (eta := eta) hz0 hXi).mul (hW z) |>.sub (hI z)
  · intro han
    rw [SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero]
    intro z hzero
    by_contra hzIm
    have hW0 : W z ≠ 0 := fun hzeroW => hzIm (hreal z hzeroW)
    have hpole := meromorphicOrderAt_suzukiExteriorRemainder_eq_neg_one
      (eta := eta) (W := W) (intervalPart := intervalPart)
      hzero (hW z) hW0 (hI z)
    have hnonneg := (han z hzIm).meromorphicOrderAt_nonneg
    rw [hpole] at hnonneg
    have hnot : ¬ (0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) := by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
    exact hnot hnonneg

/-- **Distinct-channel cross-sewn RH criterion.**  Opposite shifts may have unrelated entire
characteristic factors and interval parts.  Real-zero closure of their product and the exact
cross-sewing law reduce the pair to zero-shift exterior pole tomography. -/
theorem riemannHypothesis_iff_suzukiCrossSewnExterior_analytic_offReal
    {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ} {eta : ℂ}
    (hWPlus : ∀ z, AnalyticAt ℂ WPlus z)
    (hWMinus : ∀ z, AnalyticAt ℂ WMinus z)
    (hIPlus : ∀ z, AnalyticAt ℂ intervalPlus z)
    (hIMinus : ∀ z, AnalyticAt ℂ intervalMinus z)
    (hrealPlus : ∀ z, WPlus z = 0 → z.im = 0)
    (hrealMinus : ∀ z, WMinus z = 0 → z.im = 0) :
    RiemannHypothesis ↔
      ∀ z : ℂ, z.im ≠ 0 →
        AnalyticAt ℂ
          (suzukiCrossSewnExterior eta
            WPlus WMinus intervalPlus intervalMinus) z := by
  have hP : ∀ z, AnalyticAt ℂ
      (suzukiCrossSewnCharacteristic WPlus WMinus) z := fun z =>
    analyticAt_suzukiCrossSewnCharacteristic (hWPlus z) (hWMinus z)
  have hJ : ∀ z, AnalyticAt ℂ
      (suzukiCrossSewnIntervalPart WPlus WMinus intervalPlus intervalMinus) z := fun z =>
    analyticAt_suzukiCrossSewnIntervalPart
      (hWPlus z) (hWMinus z) (hIPlus z) (hIMinus z)
  have hrealP : ∀ z,
      suzukiCrossSewnCharacteristic WPlus WMinus z = 0 → z.im = 0 := fun _ =>
    suzukiCrossSewnCharacteristic_zero_im hrealPlus hrealMinus
  have hcriterion :=
    riemannHypothesis_iff_suzukiExteriorRemainder_analytic_offReal_of_realZeros
      (eta := (0 : ℂ)) hP hJ hrealP
  have hcross :
      suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus =
        suzukiExteriorRemainder 0
          (suzukiCrossSewnCharacteristic WPlus WMinus)
          (suzukiCrossSewnIntervalPart WPlus WMinus intervalPlus intervalMinus) := by
    funext z
    exact suzukiCrossSewnExterior_eq_zeroShift
      eta WPlus WMinus intervalPlus intervalMinus z
  rw [hcross]
  exact hcriterion

/-- **Projectively gauge-invariant RH criterion.**  Under the same source hypotheses, RH is
equivalent to off-real analyticity after division by product characteristic.  Independent
zero-free gauges disappear from this normalized channel. -/
theorem riemannHypothesis_iff_suzukiCrossSewnNormalizedExterior_analytic_offReal
    {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ} {eta : ℂ}
    (hWPlus : ∀ z, AnalyticAt ℂ WPlus z)
    (hWMinus : ∀ z, AnalyticAt ℂ WMinus z)
    (hIPlus : ∀ z, AnalyticAt ℂ intervalPlus z)
    (hIMinus : ∀ z, AnalyticAt ℂ intervalMinus z)
    (hrealPlus : ∀ z, WPlus z = 0 → z.im = 0)
    (hrealMinus : ∀ z, WMinus z = 0 → z.im = 0) :
    RiemannHypothesis ↔
      ∀ z : ℂ, z.im ≠ 0 →
        AnalyticAt ℂ
          (suzukiCrossSewnNormalizedExterior eta
            WPlus WMinus intervalPlus intervalMinus) z := by
  have hcross := riemannHypothesis_iff_suzukiCrossSewnExterior_analytic_offReal
    hWPlus hWMinus hIPlus hIMinus hrealPlus hrealMinus (eta := eta)
  constructor
  · intro hRH z hz
    have hC := hcross.mp hRH z hz
    have hP := analyticAt_suzukiCrossSewnCharacteristic
      (hWPlus z) (hWMinus z)
    have hP0 := suzukiCrossSewnCharacteristic_ne_zero_of_im_ne_zero
      hrealPlus hrealMinus hz
    exact hC.div hP hP0
  · intro hN
    apply hcross.mpr
    intro z hz
    have hP := analyticAt_suzukiCrossSewnCharacteristic
      (hWPlus z) (hWMinus z)
    have hP0 := suzukiCrossSewnCharacteristic_ne_zero_of_im_ne_zero
      hrealPlus hrealMinus hz
    have hprod := hP.mul (hN z hz)
    apply hprod.congr
    filter_upwards [hP.continuousAt.eventually_ne hP0] with w hw
    change suzukiCrossSewnCharacteristic WPlus WMinus w *
        (suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus w /
          suzukiCrossSewnCharacteristic WPlus WMinus w) =
      suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus w
    rw [mul_comm, div_mul_cancel₀ _ hw]

/-! ## Universal projective Xi-pole tomography -/

/-- A hypothetical Xi zero gives the cross-sewn channel one unavoidable simple pole whenever both
characteristic factors are analytic and nonzero there. -/
theorem meromorphicOrderAt_suzukiCrossSewnExterior_eq_neg_one
    {eta z : ℂ} {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ}
    (hz : XiC z = 0)
    (hWPlus : AnalyticAt ℂ WPlus z) (hWPlus0 : WPlus z ≠ 0)
    (hWMinus : AnalyticAt ℂ WMinus z) (hWMinus0 : WMinus z ≠ 0)
    (hIPlus : AnalyticAt ℂ intervalPlus z)
    (hIMinus : AnalyticAt ℂ intervalMinus z) :
    meromorphicOrderAt
        (suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus) z =
      ((-1 : ℤ) : WithTop ℤ) := by
  have hP := analyticAt_suzukiCrossSewnCharacteristic hWPlus hWMinus
  have hP0 : suzukiCrossSewnCharacteristic WPlus WMinus z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hWPlus0) hWMinus0
  have hJ := analyticAt_suzukiCrossSewnIntervalPart
    hWPlus hWMinus hIPlus hIMinus
  have hcross :
      suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus =
        suzukiExteriorRemainder 0
          (suzukiCrossSewnCharacteristic WPlus WMinus)
          (suzukiCrossSewnIntervalPart WPlus WMinus intervalPlus intervalMinus) := by
    funext w
    exact suzukiCrossSewnExterior_eq_zeroShift
      eta WPlus WMinus intervalPlus intervalMinus w
  rw [hcross]
  exact meromorphicOrderAt_suzukiExteriorRemainder_eq_neg_one hz hP hP0 hJ

/-- Exact cross-sewn pole coefficient before projective normalization. -/
theorem meromorphicTrailingCoeffAt_suzukiCrossSewnExterior
    {eta z : ℂ} {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ}
    (hz : XiC z = 0)
    (hWPlus : AnalyticAt ℂ WPlus z) (hWPlus0 : WPlus z ≠ 0)
    (hWMinus : AnalyticAt ℂ WMinus z) (hWMinus0 : WMinus z ≠ 0)
    (hIPlus : AnalyticAt ℂ intervalPlus z)
    (hIMinus : AnalyticAt ℂ intervalMinus z) :
    meromorphicTrailingCoeffAt
        (suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus) z =
      ((analyticOrderAt XiC z).toNat : ℂ) *
        suzukiCrossSewnCharacteristic WPlus WMinus z / z ^ 2 := by
  have hP := analyticAt_suzukiCrossSewnCharacteristic hWPlus hWMinus
  have hP0 : suzukiCrossSewnCharacteristic WPlus WMinus z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hWPlus0) hWMinus0
  have hJ := analyticAt_suzukiCrossSewnIntervalPart
    hWPlus hWMinus hIPlus hIMinus
  have hcross :
      suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus =
        suzukiExteriorRemainder 0
          (suzukiCrossSewnCharacteristic WPlus WMinus)
          (suzukiCrossSewnIntervalPart WPlus WMinus intervalPlus intervalMinus) := by
    funext w
    exact suzukiCrossSewnExterior_eq_zeroShift
      eta WPlus WMinus intervalPlus intervalMinus w
  rw [hcross]
  exact meromorphicTrailingCoeffAt_suzukiExteriorRemainder hz hP hP0 hJ

/-- Projective normalization retains the unavoidable simple Xi pole. -/
theorem meromorphicOrderAt_suzukiCrossSewnNormalizedExterior_eq_neg_one
    {eta z : ℂ} {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ}
    (hz : XiC z = 0)
    (hWPlus : AnalyticAt ℂ WPlus z) (hWPlus0 : WPlus z ≠ 0)
    (hWMinus : AnalyticAt ℂ WMinus z) (hWMinus0 : WMinus z ≠ 0)
    (hIPlus : AnalyticAt ℂ intervalPlus z)
    (hIMinus : AnalyticAt ℂ intervalMinus z) :
    meromorphicOrderAt
        (suzukiCrossSewnNormalizedExterior eta
          WPlus WMinus intervalPlus intervalMinus) z =
      ((-1 : ℤ) : WithTop ℤ) := by
  let C := suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus
  let P := suzukiCrossSewnCharacteristic WPlus WMinus
  have hP : AnalyticAt ℂ P z :=
    analyticAt_suzukiCrossSewnCharacteristic hWPlus hWMinus
  have hP0 : P z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hWPlus0) hWMinus0
  have hJ := analyticAt_suzukiCrossSewnIntervalPart
    hWPlus hWMinus hIPlus hIMinus
  have hCeq : C = suzukiExteriorRemainder 0 P
      (suzukiCrossSewnIntervalPart WPlus WMinus intervalPlus intervalMinus) := by
    funext w
    exact suzukiCrossSewnExterior_eq_zeroShift
      eta WPlus WMinus intervalPlus intervalMinus w
  have hC : MeromorphicAt C z := by
    rw [hCeq]
    exact (meromorphicAt_suzukiShiftedXiMultiplier 0 z).mul hP.meromorphicAt |>.sub
      hJ.meromorphicAt
  have hCorder : meromorphicOrderAt C z = ((-1 : ℤ) : WithTop ℤ) := by
    dsimp only [C]
    exact meromorphicOrderAt_suzukiCrossSewnExterior_eq_neg_one
      hz hWPlus hWPlus0 hWMinus hWMinus0 hIPlus hIMinus
  have hPorder : meromorphicOrderAt P z = 0 := by
    rw [hP.meromorphicOrderAt_eq, hP.analyticOrderAt_eq_zero.mpr hP0]
    simp
  change meromorphicOrderAt (fun w => C w / P w) z = ((-1 : ℤ) : WithTop ℤ)
  rw [fun_meromorphicOrderAt_div hC hP.meromorphicAt, hCorder, hPorder]
  norm_num

/-- **Universal projective Xi-pole invariant.**  After cross-sewing and division by product
characteristic, the exact pole coefficient is Xi multiplicity divided by `z²`; every dependence on
shift, source functions, interval terms, and independent gauges cancels. -/
theorem meromorphicTrailingCoeffAt_suzukiCrossSewnNormalizedExterior
    {eta z : ℂ} {WPlus WMinus intervalPlus intervalMinus : ℂ → ℂ}
    (hz : XiC z = 0)
    (hWPlus : AnalyticAt ℂ WPlus z) (hWPlus0 : WPlus z ≠ 0)
    (hWMinus : AnalyticAt ℂ WMinus z) (hWMinus0 : WMinus z ≠ 0)
    (hIPlus : AnalyticAt ℂ intervalPlus z)
    (hIMinus : AnalyticAt ℂ intervalMinus z) :
    meromorphicTrailingCoeffAt
        (suzukiCrossSewnNormalizedExterior eta
          WPlus WMinus intervalPlus intervalMinus) z =
      ((analyticOrderAt XiC z).toNat : ℂ) / z ^ 2 := by
  let C := suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus
  let P := suzukiCrossSewnCharacteristic WPlus WMinus
  have hP : AnalyticAt ℂ P z :=
    analyticAt_suzukiCrossSewnCharacteristic hWPlus hWMinus
  have hP0 : P z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hWPlus0) hWMinus0
  have hJ := analyticAt_suzukiCrossSewnIntervalPart
    hWPlus hWMinus hIPlus hIMinus
  have hCeq : C = suzukiExteriorRemainder 0 P
      (suzukiCrossSewnIntervalPart WPlus WMinus intervalPlus intervalMinus) := by
    funext w
    exact suzukiCrossSewnExterior_eq_zeroShift
      eta WPlus WMinus intervalPlus intervalMinus w
  have hC : MeromorphicAt C z := by
    rw [hCeq]
    exact (meromorphicAt_suzukiShiftedXiMultiplier 0 z).mul hP.meromorphicAt |>.sub
      hJ.meromorphicAt
  have hCtrail : meromorphicTrailingCoeffAt C z =
      ((analyticOrderAt XiC z).toNat : ℂ) * P z / z ^ 2 := by
    dsimp only [C, P]
    exact meromorphicTrailingCoeffAt_suzukiCrossSewnExterior
      hz hWPlus hWPlus0 hWMinus hWMinus0 hIPlus hIMinus
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

end

end RHTower
