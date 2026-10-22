import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma44
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalKernelContinuity

/-!
# Suzuki (2012), Lemma 4.5

For `omega > 1/2`, `a > 1`, and either sign, this module constructs the unique solution of

`X(x) + epsilon * integral_0^a h_omega(xy) X(y) dy = h_omega(ax)`

in `L²(0,a)`, proves its real-valuedness and exact lower support gap, and, for `omega > 1`,
constructs Suzuki's continuous representative vanishing on `[0,1/a]`.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- The two signs in Suzuki's integral equations. -/
inductive SuzukiHankelSign
  | positive
  | negative
  deriving DecidableEq

/-- Complex scalar attached to Suzuki's sign. -/
def SuzukiHankelSign.coeff : SuzukiHankelSign → ℂ
  | .positive => 1
  | .negative => -1

@[simp] theorem SuzukiHankelSign.coeff_positive :
    SuzukiHankelSign.positive.coeff = 1 := rfl

@[simp] theorem SuzukiHankelSign.coeff_negative :
    SuzukiHankelSign.negative.coeff = -1 := rfl

@[simp] theorem SuzukiHankelSign.star_coeff (epsilon : SuzukiHankelSign) :
    star epsilon.coeff = epsilon.coeff := by cases epsilon <;> simp

/-- Operator `1 + epsilon H_{omega,a}` in Suzuki's equation (402). -/
def suzukiHankelResolventOperator
    (epsilon : SuzukiHankelSign) (omega a : ℝ) (homega : 1 / 2 < omega) :
    IntervalL2 0 a →L[ℂ] IntervalL2 0 a :=
  1 + epsilon.coeff • suzukiCompressedHankelOperator omega a homega

/-- Both signed resolvents are units by Suzuki's exact Lemma 4.4. -/
theorem suzukiHankelResolventOperator_isUnit
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    IsUnit (suzukiHankelResolventOperator epsilon omega a homega) := by
  cases epsilon with
  | positive =>
      simpa [suzukiHankelResolventOperator] using
        suzuki2012_lemma_four_four_one_add_isUnit homega ha
  | negative =>
      simpa [suzukiHankelResolventOperator, sub_eq_add_neg] using
        suzuki2012_lemma_four_four_one_sub_isUnit homega ha

/-- Literal right-hand side `y ↦ h_omega(ay)` as an element of `L²(0,a)`. -/
def suzukiHankelBoundarySource
    (omega a : ℝ) (homega : 1 / 2 < omega) (ha : 1 < a) :
    IntervalL2 0 a :=
  suzukiCompressedHankelRow omega a homega ha a

theorem suzukiHankelBoundarySource_ae
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) :
    (suzukiHankelBoundarySource omega a homega ha : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      fun x => suzukiSourceHFinite omega (a * (x : ℝ)) := by
  exact suzukiCompressedHankelRow_ae homega ha (lt_trans zero_lt_one ha) le_rfl

/-- Suzuki's `phi_a^epsilon`, obtained by applying the exact inverse resolvent. -/
def suzukiHankelPhi
    (epsilon : SuzukiHankelSign) (omega a : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) : IntervalL2 0 a :=
  let hunit := suzukiHankelResolventOperator_isUnit epsilon homega ha
  ((↑(hunit.unit⁻¹) : IntervalL2 0 a →L[ℂ] IntervalL2 0 a)
    (suzukiHankelBoundarySource omega a homega ha))

/-- The constructed solution satisfies Suzuki's operator equation exactly. -/
theorem suzukiHankelPhi_resolvent_equation
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    suzukiHankelResolventOperator epsilon omega a homega
        (suzukiHankelPhi epsilon omega a homega ha) =
      suzukiHankelBoundarySource omega a homega ha := by
  let hunit := suzukiHankelResolventOperator_isUnit epsilon homega ha
  let U := hunit.unit
  have hU : (↑U : IntervalL2 0 a →L[ℂ] IntervalL2 0 a) =
      suzukiHankelResolventOperator epsilon omega a homega := hunit.unit_spec
  rw [← hU]
  change (↑U : IntervalL2 0 a →L[ℂ] IntervalL2 0 a)
      ((↑(U⁻¹) : IntervalL2 0 a →L[ℂ] IntervalL2 0 a)
        (suzukiHankelBoundarySource omega a homega ha)) = _
  rw [← mul_apply_eq_comp, Units.mul_inv]
  simp

/-- Suzuki's signed equation has at most one `L²(0,a)` solution. -/
theorem suzukiHankel_resolvent_unique
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a)
    {X : IntervalL2 0 a}
    (hX : suzukiHankelResolventOperator epsilon omega a homega X =
      suzukiHankelBoundarySource omega a homega ha) :
    X = suzukiHankelPhi epsilon omega a homega ha := by
  let hunit := suzukiHankelResolventOperator_isUnit epsilon homega ha
  let U := hunit.unit
  have hU : (↑U : IntervalL2 0 a →L[ℂ] IntervalL2 0 a) =
      suzukiHankelResolventOperator epsilon omega a homega := hunit.unit_spec
  have hphi := suzukiHankelPhi_resolvent_equation epsilon homega ha
  rw [← hU] at hX hphi
  have hcancel :
      (↑(U⁻¹) : IntervalL2 0 a →L[ℂ] IntervalL2 0 a)
          ((↑U : IntervalL2 0 a →L[ℂ] IntervalL2 0 a) X) =
        (↑(U⁻¹) : IntervalL2 0 a →L[ℂ] IntervalL2 0 a)
          ((↑U : IntervalL2 0 a →L[ℂ] IntervalL2 0 a)
            (suzukiHankelPhi epsilon omega a homega ha)) := by
    rw [hX, hphi]
  simpa only [← mul_apply_eq_comp, Units.inv_mul,
    one_apply_eq_self] using hcancel

/-- Pointwise-a.e. form of Suzuki's integral equation (402). -/
theorem suzukiHankelPhi_integral_equation_ae
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    ∀ᵐ x : ClosedInterval 0 a ∂volume,
      suzukiHankelPhi epsilon omega a homega ha x +
          epsilon.coeff * ∫ y : ClosedInterval 0 a,
            suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
              suzukiHankelPhi epsilon omega a homega ha y ∂volume =
        suzukiSourceHFinite omega (a * (x : ℝ)) := by
  let phi := suzukiHankelPhi epsilon omega a homega ha
  let T := suzukiCompressedHankelOperator omega a homega
  have hEq : phi + epsilon.coeff • T phi =
      suzukiHankelBoundarySource omega a homega ha := by
    simpa only [suzukiHankelResolventOperator, ContinuousLinearMap.add_apply,
      one_apply_eq_self, ContinuousLinearMap.smul_apply, smul_eq_mul] using
      suzukiHankelPhi_resolvent_equation epsilon homega ha
  have hadd := Lp.coeFn_add phi (epsilon.coeff • T phi)
  rw [hEq] at hadd
  filter_upwards [hadd, Lp.coeFn_smul epsilon.coeff (T phi),
    suzukiCompressedHankelOperator_coeFn omega a homega (by linarith) phi,
    suzukiHankelBoundarySource_ae homega ha] with x hxadd hxsmul hT hsource
  calc
    suzukiHankelPhi epsilon omega a homega ha x +
          epsilon.coeff * ∫ y : ClosedInterval 0 a,
            suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
              suzukiHankelPhi epsilon omega a homega ha y ∂volume =
        phi x + epsilon.coeff * T phi x := by rw [hT]
    _ = suzukiHankelBoundarySource omega a homega ha x := by
      simpa only [Pi.add_apply, hxsmul, Pi.smul_apply, smul_eq_mul] using hxadd.symm
    _ = suzukiSourceHFinite omega (a * (x : ℝ)) := hsource

/-- Every finite Hankel output vanishes a.e. below `1/a`, independently of its input. -/
theorem suzukiCompressedHankelOperator_ae_zero_below_reciprocal
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a)
    (f : IntervalL2 0 a) :
    ∀ᵐ x : ClosedInterval 0 a ∂volume,
      (x : ℝ) ≤ 1 / a →
        suzukiCompressedHankelOperator omega a homega f x = 0 := by
  filter_upwards [suzukiCompressedHankelOperator_coeFn omega a homega (by linarith) f] with x hT
  intro hx
  rw [hT]
  have hintegrand : (fun y : ClosedInterval 0 a =>
      suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y) = fun _ => 0 := by
    funext y
    have hxy : (x : ℝ) * (y : ℝ) ≤ 1 := by
      calc
        (x : ℝ) * (y : ℝ) ≤ (1 / a) * a :=
          mul_le_mul hx y.property.2 y.property.1 (one_div_nonneg.mpr (by linarith))
        _ = 1 := by field_simp
    rw [suzukiSourceHFinite, if_neg (not_lt_of_ge hxy), zero_mul]
  rw [hintegrand]
  simp

/-- Suzuki's solution has the exact lower support gap asserted in Lemma 4.5. -/
theorem suzukiHankelPhi_ae_zero_below_reciprocal
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    ∀ᵐ x : ClosedInterval 0 a ∂volume,
      (x : ℝ) ≤ 1 / a →
        suzukiHankelPhi epsilon omega a homega ha x = 0 := by
  filter_upwards [suzukiHankelPhi_integral_equation_ae epsilon homega ha,
    suzukiCompressedHankelOperator_ae_zero_below_reciprocal homega ha
      (suzukiHankelPhi epsilon omega a homega ha),
    suzukiCompressedHankelOperator_coeFn omega a homega (by linarith)
      (suzukiHankelPhi epsilon omega a homega ha)] with x heq hzero hT
  intro hx
  have hsource : suzukiSourceHFinite omega (a * (x : ℝ)) = 0 := by
    rw [suzukiSourceHFinite, if_neg]
    exact not_lt_of_ge (by
      calc
        a * (x : ℝ) ≤ a * (1 / a) := mul_le_mul_of_nonneg_left hx (by linarith)
        _ = 1 := by field_simp)
  have hIntegral : (∫ y : ClosedInterval 0 a,
      suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
        suzukiHankelPhi epsilon omega a homega ha y ∂volume) = 0 := by
    rw [← hT]
    exact hzero hx
  rw [hIntegral, mul_zero, add_zero, hsource] at heq
  exact heq

/-! ## Reality -/

private theorem star_IntervalL2_add
    {a : ℝ} (f g : IntervalL2 0 a) :
    star (f + g) = star f + star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g,
    Lp.coeFn_add (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g] with
      x hstar hadd haddStar hf hg
  rw [hstar]
  calc
    star ((f + g : IntervalL2 0 a) x) = star (f x + g x) := by
      rw [hadd, Pi.add_apply]
    _ = star (f x) + star (g x) := star_add _ _
    _ = (star f : IntervalL2 0 a) x + (star g : IntervalL2 0 a) x := by
      rw [hf, hg, Pi.star_apply, Pi.star_apply]
    _ = (star f + star g : IntervalL2 0 a) x := by
      rw [haddStar, Pi.add_apply]

private theorem star_IntervalL2_smul
    {a : ℝ} (c : ℂ) (f : IntervalL2 0 a) :
    star (c • f) = star c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_smul (star c) (star f), Lp.coeFn_star f] with
      x hstar hsmul hsmulStar hf
  rw [hstar]
  calc
    star ((c • f : IntervalL2 0 a) x) = star (c * f x) := by
      rw [hsmul, Pi.smul_apply, smul_eq_mul]
    _ = star c * star (f x) := map_mul (starRingEnd ℂ) c (f x)
    _ = star c * (star f : IntervalL2 0 a) x := by rw [hf, Pi.star_apply]
    _ = (star c • star f : IntervalL2 0 a) x := by
      rw [hsmulStar, Pi.smul_apply, smul_eq_mul]

theorem star_suzukiHankelBoundarySource
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) :
    star (suzukiHankelBoundarySource omega a homega ha) =
      suzukiHankelBoundarySource omega a homega ha := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (suzukiHankelBoundarySource omega a homega ha),
    suzukiHankelBoundarySource_ae homega ha] with x hstar hsource
  calc
    ((star (suzukiHankelBoundarySource omega a homega ha) : IntervalL2 0 a) :
        ClosedInterval 0 a → ℂ) x =
        star (suzukiHankelBoundarySource omega a homega ha x) := by
          simpa only [Pi.star_apply] using hstar
    _ = star (suzukiSourceHFinite omega (a * (x : ℝ))) := congrArg star hsource
    _ = suzukiSourceHFinite omega (a * (x : ℝ)) := by
      simpa only [starRingEnd_apply] using
        conj_suzukiSourceHFinite omega (a * (x : ℝ))
    _ = suzukiHankelBoundarySource omega a homega ha x := hsource.symm

/-- The literal finite Hankel operator commutes with pointwise complex conjugation. -/
theorem star_suzukiCompressedHankelOperator
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a)
    (f : IntervalL2 0 a) :
    star (suzukiCompressedHankelOperator omega a homega f) =
      suzukiCompressedHankelOperator omega a homega (star f) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (suzukiCompressedHankelOperator omega a homega f),
    suzukiCompressedHankelOperator_coeFn omega a homega (by linarith) f,
    suzukiCompressedHankelOperator_coeFn omega a homega (by linarith) (star f)] with
      x hstar hTf hTstar
  have hleft :
      ((star (suzukiCompressedHankelOperator omega a homega f) : IntervalL2 0 a) :
          ClosedInterval 0 a → ℂ) x =
        star (∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume) := by
    calc
      _ = star (suzukiCompressedHankelOperator omega a homega f x) := by
        simpa only [Pi.star_apply] using hstar
      _ = _ := congrArg star hTf
  rw [hleft, hTstar]
  change (starRingEnd ℂ) (∫ y : ClosedInterval 0 a,
      suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with y hy
  rw [Pi.star_apply] at hy
  rw [hy, map_mul, conj_suzukiSourceHFinite, starRingEnd_apply]

theorem star_suzukiHankelPhi
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    star (suzukiHankelPhi epsilon omega a homega ha) =
      suzukiHankelPhi epsilon omega a homega ha := by
  let phi := suzukiHankelPhi epsilon omega a homega ha
  let T := suzukiCompressedHankelOperator omega a homega
  have hEq : phi + epsilon.coeff • T phi =
      suzukiHankelBoundarySource omega a homega ha := by
    simpa only [suzukiHankelResolventOperator, ContinuousLinearMap.add_apply,
      one_apply_eq_self, ContinuousLinearMap.smul_apply, smul_eq_mul] using
      suzukiHankelPhi_resolvent_equation epsilon homega ha
  have hstar : star phi + epsilon.coeff • star (T phi) =
      star (suzukiHankelBoundarySource omega a homega ha) := by
    simpa only [star_IntervalL2_add, star_IntervalL2_smul,
      SuzukiHankelSign.star_coeff] using congrArg star hEq
  rw [star_suzukiCompressedHankelOperator homega ha,
    star_suzukiHankelBoundarySource homega ha] at hstar
  apply suzukiHankel_resolvent_unique epsilon homega ha
  simpa only [suzukiHankelResolventOperator, ContinuousLinearMap.add_apply,
    one_apply_eq_self, ContinuousLinearMap.smul_apply, smul_eq_mul] using hstar

/-- Suzuki's solution is real-valued almost everywhere. -/
theorem suzukiHankelPhi_real_ae
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    ∀ᵐ x : ClosedInterval 0 a ∂volume,
      (suzukiHankelPhi epsilon omega a homega ha x).im = 0 := by
  let phi := suzukiHankelPhi epsilon omega a homega ha
  have hcoe := Lp.coeFn_star phi
  rw [star_suzukiHankelPhi epsilon homega ha] at hcoe
  filter_upwards [hcoe] with x hx
  apply Complex.conj_eq_iff_im.mp
  have hx' : star (phi x) = phi x := by
    simpa only [Pi.star_apply] using hx.symm
  simpa only [starRingEnd_apply] using hx'

/-! ## Continuous representative for `omega > 1` -/

/-- Continuous pointwise realization of the finite Hankel integral for a fixed `L²` input. -/
def suzukiCompressedHankelContinuousOutput
    (omega a : ℝ) (homega : 1 / 2 < omega) (ha : 1 < a)
    (f : IntervalL2 0 a) : C(ClosedInterval 0 a, ℂ) where
  toFun x := suzukiCompressedHankelFunctionalContinuous omega a homega ha x f
  continuous_toFun :=
    ((ContinuousLinearMap.apply ℂ ℂ) f).continuous.comp
      (suzukiCompressedHankelFunctionalContinuous omega a homega ha).continuous

theorem suzukiCompressedHankelContinuousOutput_eq_integral
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a)
    (f : IntervalL2 0 a) (x : ClosedInterval 0 a) :
    suzukiCompressedHankelContinuousOutput omega a homega ha f x =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume := by
  change (complexMulBilinear.lpPairing volume 2 2
    (suzukiCompressedHankelRowContinuous omega a homega ha x)) f = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [suzukiCompressedHankelRowContinuous_ae omega a homega ha x] with y hy
  rw [hy]
  simp [complexMulBilinear]

/-- For `omega > 1`, the literal boundary source `x ↦ h_omega(ax)` is continuous on `[0,a]`. -/
def suzukiHankelBoundarySourceContinuous
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) :
    C(ClosedInterval 0 a, ℂ) where
  toFun x := suzukiSourceHFinite omega (a * (x : ℝ))
  continuous_toFun := continuousOn_iff_continuous_restrict.mp
    (show ContinuousOn (fun x : ℝ => suzukiSourceHFinite omega (a * x)) (Icc 0 a) from by
    intro (x : ℝ) hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx0
    · have hainv : 0 < 1 / a := one_div_pos.mpr (lt_trans zero_lt_one ha)
      have hev : (fun z : ℝ => suzukiSourceHFinite omega (a * z)) =ᶠ[𝓝[Icc 0 a] 0]
          fun _ => 0 := by
        have hsmall : ∀ᶠ z in 𝓝[Icc 0 a] 0, z ∈ Iio (1 / a) :=
          Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hainv)
        filter_upwards [hsmall, self_mem_nhdsWithin] with z hz hzIcc
        rw [suzukiSourceHFinite, if_neg]
        exact not_lt_of_ge (by
          calc
            a * z ≤ a * (1 / a) := mul_le_mul_of_nonneg_left hz.le (by linarith)
            _ = 1 := by field_simp)
      exact continuousWithinAt_const.congr_of_eventuallyEq hev (by
        simp [suzukiSourceHFinite])
    · have hax : 0 < a * x := mul_pos (lt_trans zero_lt_one ha) hx0
      exact ((continuousAt_suzukiSourceHFinite homega hax).comp
        (continuousAt_const.mul continuousAt_id)).continuousWithinAt)

@[simp] theorem suzukiHankelBoundarySourceContinuous_apply
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (x : ClosedInterval 0 a) :
    suzukiHankelBoundarySourceContinuous omega a homega ha x =
      suzukiSourceHFinite omega (a * (x : ℝ)) := rfl

/-- Suzuki's continuous representative, given by the literal right-hand side of equation (402). -/
def suzukiHankelPhiContinuous
    (epsilon : SuzukiHankelSign) (omega a : ℝ)
    (homega : 1 < omega) (ha : 1 < a) : C(ClosedInterval 0 a, ℂ) :=
  suzukiHankelBoundarySourceContinuous omega a homega ha -
    epsilon.coeff • suzukiCompressedHankelContinuousOutput omega a (by linarith) ha
      (suzukiHankelPhi epsilon omega a (by linarith) ha)

/-- The continuous representative is equal almost everywhere to Suzuki's `L²` solution. -/
theorem suzukiHankelPhiContinuous_ae
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    (suzukiHankelPhiContinuous epsilon omega a homega ha : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      (suzukiHankelPhi epsilon omega a (by linarith) ha : ClosedInterval 0 a → ℂ) := by
  let homegaHalf : 1 / 2 < omega := by linarith
  filter_upwards [suzukiHankelPhi_integral_equation_ae epsilon homegaHalf ha] with x heq
  rw [suzukiHankelPhiContinuous, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    suzukiHankelBoundarySourceContinuous_apply,
    suzukiCompressedHankelContinuousOutput_eq_integral homegaHalf ha]
  change suzukiSourceHFinite omega (a * (x : ℝ)) - epsilon.coeff *
      (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiHankelPhi epsilon omega a homegaHalf ha y ∂volume) = _
  simpa only using (sub_eq_iff_eq_add).2 heq.symm

/-- The continuous representative vanishes pointwise, not merely a.e., on `[0,1/a]`. -/
theorem suzukiHankelPhiContinuous_eq_zero_below_reciprocal
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a)
    (x : ClosedInterval 0 a) (hx : (x : ℝ) ≤ 1 / a) :
    suzukiHankelPhiContinuous epsilon omega a homega ha x = 0 := by
  let homegaHalf : 1 / 2 < omega := by linarith
  rw [suzukiHankelPhiContinuous, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    suzukiHankelBoundarySourceContinuous_apply,
    suzukiCompressedHankelContinuousOutput_eq_integral homegaHalf ha]
  change suzukiSourceHFinite omega (a * (x : ℝ)) - epsilon.coeff *
      (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiHankelPhi epsilon omega a homegaHalf ha y ∂volume) = 0
  have hsource : suzukiSourceHFinite omega (a * (x : ℝ)) = 0 := by
    rw [suzukiSourceHFinite, if_neg]
    exact not_lt_of_ge (by
      calc
        a * (x : ℝ) ≤ a * (1 / a) := mul_le_mul_of_nonneg_left hx (by linarith)
        _ = 1 := by field_simp)
  have hintegrand : (fun y : ClosedInterval 0 a =>
      suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
        suzukiHankelPhi epsilon omega a homegaHalf ha y) = fun _ => 0 := by
    funext y
    rw [suzukiSourceHFinite, if_neg, zero_mul]
    exact not_lt_of_ge (by
      calc
        (x : ℝ) * (y : ℝ) ≤ (1 / a) * a :=
          mul_le_mul hx y.property.2 y.property.1 (one_div_nonneg.mpr (by linarith))
        _ = 1 := by field_simp)
  rw [hsource, hintegrand]
  simp

/-- The continuous representative is pointwise real-valued. -/
theorem suzukiHankelPhiContinuous_real
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (x : ClosedInterval 0 a) :
    (suzukiHankelPhiContinuous epsilon omega a homega ha x).im = 0 := by
  let homegaHalf : 1 / 2 < omega := by linarith
  rw [suzukiHankelPhiContinuous, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    suzukiHankelBoundarySourceContinuous_apply,
    suzukiCompressedHankelContinuousOutput_eq_integral homegaHalf ha]
  change (suzukiSourceHFinite omega (a * (x : ℝ)) - epsilon.coeff *
      (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiHankelPhi epsilon omega a homegaHalf ha y ∂volume)).im = 0
  apply Complex.conj_eq_iff_im.mp
  have hIntegral :
      (starRingEnd ℂ) (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiHankelPhi epsilon omega a homegaHalf ha y ∂volume) =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiHankelPhi epsilon omega a homegaHalf ha y ∂volume := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [suzukiHankelPhi_real_ae epsilon homegaHalf ha] with y hy
    rw [map_mul, conj_suzukiSourceHFinite]
    have hphi : (starRingEnd ℂ)
        (suzukiHankelPhi epsilon omega a homegaHalf ha y) =
        suzukiHankelPhi epsilon omega a homegaHalf ha y :=
      Complex.conj_eq_iff_im.mpr hy
    rw [hphi]
  have hcoeff : (starRingEnd ℂ) epsilon.coeff = epsilon.coeff := by
    simpa only [starRingEnd_apply] using SuzukiHankelSign.star_coeff epsilon
  rw [map_sub, conj_suzukiSourceHFinite, map_mul, hcoeff, hIntegral]

/-- **Suzuki (2012), Lemma 4.5, exact bundled form.** -/
theorem suzuki2012_lemma_four_five
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    (suzukiHankelResolventOperator epsilon omega a homega
        (suzukiHankelPhi epsilon omega a homega ha) =
      suzukiHankelBoundarySource omega a homega ha) ∧
    (∀ X : IntervalL2 0 a,
      suzukiHankelResolventOperator epsilon omega a homega X =
        suzukiHankelBoundarySource omega a homega ha →
      X = suzukiHankelPhi epsilon omega a homega ha) ∧
    (∀ᵐ x : ClosedInterval 0 a ∂volume,
      (suzukiHankelPhi epsilon omega a homega ha x).im = 0) ∧
    (∀ᵐ x : ClosedInterval 0 a ∂volume,
      (x : ℝ) ≤ 1 / a → suzukiHankelPhi epsilon omega a homega ha x = 0) := by
  exact ⟨suzukiHankelPhi_resolvent_equation epsilon homega ha,
    fun _ hX => suzukiHankel_resolvent_unique epsilon homega ha hX,
    suzukiHankelPhi_real_ae epsilon homega ha,
    suzukiHankelPhi_ae_zero_below_reciprocal epsilon homega ha⟩

/-- Continuous clause of Suzuki (2012), Lemma 4.5. -/
theorem suzuki2012_lemma_four_five_continuous
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    (suzukiHankelPhiContinuous epsilon omega a homega ha : ClosedInterval 0 a → ℂ) =ᵐ[volume]
        (suzukiHankelPhi epsilon omega a (by linarith) ha : ClosedInterval 0 a → ℂ) ∧
    (∀ x : ClosedInterval 0 a,
      (suzukiHankelPhiContinuous epsilon omega a homega ha x).im = 0) ∧
    (∀ x : ClosedInterval 0 a, (x : ℝ) ≤ 1 / a →
      suzukiHankelPhiContinuous epsilon omega a homega ha x = 0) := by
  exact ⟨suzukiHankelPhiContinuous_ae epsilon homega ha,
    suzukiHankelPhiContinuous_real epsilon homega ha,
    suzukiHankelPhiContinuous_eq_zero_below_reciprocal epsilon homega ha⟩

end RHTower
