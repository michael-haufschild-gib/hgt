import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelDifferentialSystem

/-!
# Suzuki's canonical Hankel differential system: pointwise equations

This module proves Suzuki (2012), equations (407)--(409), on the exact arithmetic regular locus.
The spatial integration by parts is supplied by `SuzukiCanonicalHankelDifferentialSystem`; this
layer connects it to the literal global Fredholm equation and performs the printed rearrangements.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace
attribute [local instance 2000] NormedAddCommGroup.toAddCommGroup

/-- Pointwise form of Suzuki's defining Fredholm equation (405), using the literal global
continuous representative under the integral. -/
theorem suzukiHankelPhiGlobal_fredholm_equation
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hx : 0 ≤ x) :
    suzukiHankelPhiGlobal epsilon omega a homega ha x +
        epsilon.coeff * ∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega (x * (y : ℝ)) *
            suzukiHankelPhiGlobal epsilon omega a homega ha (y : ℝ) ∂volume =
      suzukiSourceHFinite omega (a * x) := by
  have h := suzukiHankelPhiGlobalContinuous_equation epsilon homega ha ⟨x, hx⟩
  exact h

/-- Equality of the two scaled derivatives of the product kernel `h_omega(a*x)` away from its
exact integer cusp locus. -/
theorem suzukiSourceHFinite_scaled_deriv_comm
    {omega a x : ℝ} (homega : 1 < omega) (ha : 0 < a) (hx : 0 < x)
    (hreg : ∀ n : ℕ, a * x ≠ (n : ℝ)) :
    (x : ℂ) * deriv (fun z : ℝ => suzukiSourceHFinite omega (a * z)) x =
      (a : ℂ) * deriv (fun b : ℝ => suzukiSourceHFinite omega (b * x)) a := by
  have hb : HasDerivAt (suzukiSourceHFinite omega)
      (deriv (suzukiSourceHFinite omega) (a * x)) (a * x) :=
    ((contDiffAt_one_suzukiSourceHFinite_of_not_nat homega (mul_pos ha hx) hreg).differentiableAt
      (by norm_num)).hasDerivAt
  have hax : HasDerivAt (fun z : ℝ => a * z) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  have hxa : HasDerivAt (fun b : ℝ => b * x) x a := by
    simpa using (hasDerivAt_id a).mul_const x
  have hleft := hb.scomp x hax
  have hright := hb.scomp a hxa
  have hleft' : HasDerivAt (fun z : ℝ => suzukiSourceHFinite omega (a * z))
      (a • deriv (suzukiSourceHFinite omega) (a * x)) x := by
    apply hleft.congr_of_eventuallyEq
    exact Eventually.of_forall fun _ => rfl
  have hright' : HasDerivAt (fun b : ℝ => suzukiSourceHFinite omega (b * x))
      (x • deriv (suzukiSourceHFinite omega) (a * x)) a := by
    apply hright.congr_of_eventuallyEq
    exact Eventually.of_forall fun _ => rfl
  rw [hleft'.deriv, hright'.deriv]
  simp only [Complex.real_smul]
  ring

/-- Suzuki (2012), equation (407), for the literal arithmetic kernel and Fredholm solution. -/
theorem suzuki_equation_407
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hx : x ∈ SuzukiHankelRegularX a) :
    suzukiHankelEulerPhi epsilon omega a homega ha x -
        (1 / 2 : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha x -
        epsilon.coeff * ∫ y in (0 : ℝ)..a,
          suzukiSourceHFinite omega (x * y) *
            (suzukiHankelEulerPhi epsilon omega a homega ha y +
              (1 / 2 : ℂ) *
                suzukiHankelPhiGlobal epsilon omega a homega ha y) =
      -epsilon.coeff * (a : ℂ) *
          suzukiHankelPhiGlobal epsilon omega a homega ha a *
          suzukiSourceHFinite omega (a * x) +
        (a : ℂ) * deriv
          (fun b : ℝ => suzukiSourceHFinite omega (b * x)) a := by
  let P : ℝ → ℂ := suzukiHankelPhiGlobal epsilon omega a homega ha
  let phi : C(ClosedInterval 0 a, ℂ) :=
    suzukiHankelPhiContinuous epsilon omega a homega ha
  let H : ℝ → ℂ := suzukiSourceHIntervalIntegral omega a phi
  have ha0 : 0 < a := by linarith
  have hreg : ∀ n : ℕ, a * x ≠ (n : ℝ) := by
    intro n hax
    apply hx.2 n
    calc
      x = (a * x) / a := by field_simp
      _ = (n : ℝ) / a := by rw [hax]
  have hPderiv := hasDerivAt_suzukiHankelPhiGlobal_spatial_formula
    epsilon homega ha hx
  change HasDerivAt P
    (deriv (fun z : ℝ => suzukiSourceHFinite omega (a * z)) x -
      epsilon.coeff * deriv H x) x at hPderiv
  have hEulerH0 := suzukiSourceHIntervalEuler_eq_integral_deriv
    homega ha0 hx.1 phi
  have hEulerH : (x : ℂ) * deriv H x =
      ∫ y in (0 : ℝ)..a,
        (y : ℂ) * deriv
            (fun z : ℝ => suzukiSourceHFinite omega (x * z)) y * P y := by
    rw [← integral_subtype_closedInterval_eq_intervalIntegral ha0.le]
    rw [hEulerH0]
    apply integral_congr_ae
    filter_upwards with y
    dsimp only [phi, P]
    rw [suzukiHankelPhiGlobal_eq_continuousRepresentative epsilon homega ha]
  have hibp := suzuki_spatial_integration_by_parts epsilon homega ha hx.1
  have hscale := suzukiSourceHFinite_scaled_deriv_comm
    homega ha0 hx.1 hreg
  simp only [suzukiHankelEulerPhi]
  rw [hPderiv.deriv]
  change
    ((x : ℂ) *
          (deriv (fun z : ℝ => suzukiSourceHFinite omega (a * z)) x -
            epsilon.coeff * deriv H x) + (1 / 2 : ℂ) * P x) -
        (1 / 2 : ℂ) * P x -
        epsilon.coeff *
          (∫ y in (0 : ℝ)..a,
            suzukiSourceHFinite omega (x * y) *
              (((y : ℂ) * deriv P y + (1 / 2 : ℂ) * P y) +
                (1 / 2 : ℂ) * P y)) = _
  have hmul :
      (x : ℂ) *
          (deriv (fun z : ℝ => suzukiSourceHFinite omega (a * z)) x -
            epsilon.coeff * deriv H x) =
        (x : ℂ) * deriv (fun z : ℝ => suzukiSourceHFinite omega (a * z)) x -
          epsilon.coeff * ((x : ℂ) * deriv H x) := by ring
  have hderivIntegral :
      (∫ y in (0 : ℝ)..a,
        (y : ℂ) * deriv (fun z : ℝ => suzukiSourceHFinite omega (x * z)) y * P y) =
      ∫ y in (0 : ℝ)..a,
        deriv (fun z : ℝ => suzukiSourceHFinite omega (x * z)) y *
          ((y : ℂ) * P y) := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hphiIntegral :
      (∫ y in (0 : ℝ)..a,
        suzukiSourceHFinite omega (x * y) *
          ((y : ℂ) * deriv P y + (1 / 2 : ℂ) * P y + (1 / 2 : ℂ) * P y)) =
      ∫ y in (0 : ℝ)..a,
        suzukiSourceHFinite omega (x * y) * ((y : ℂ) * deriv P y + P y) := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hibp' :
      (∫ y in (0 : ℝ)..a,
        suzukiSourceHFinite omega (x * y) * ((y : ℂ) * deriv P y + P y)) =
      suzukiSourceHFinite omega (x * a) * ((a : ℂ) * P a) -
        ∫ y in (0 : ℝ)..a,
          deriv (fun z : ℝ => suzukiSourceHFinite omega (x * z)) y *
            ((y : ℂ) * P y) := by
    simpa only [P] using hibp
  rw [hmul, hEulerH, hderivIntegral, hphiIntegral, hibp', hscale]
  dsimp only [P]
  have hderivComm :
      deriv (fun b : ℝ => suzukiSourceHFinite omega (b * x)) a =
        deriv (fun b : ℝ => suzukiSourceHFinite omega (x * b)) a := by
    congr 1
    funext b
    rw [mul_comm]
  rw [hderivComm]
  ring

/-- Continuity of a physical Hankel row on its compact integration interval, including the
origin where the arithmetic kernel has an exact support gap. -/
theorem continuousOn_suzukiHankelRow_Icc
    {omega a x : ℝ} (homega : 1 < omega) (ha : 0 < a) (hx : 0 < x) :
    ContinuousOn (fun y : ℝ => suzukiSourceHFinite omega (x * y)) (Icc 0 a) := by
  intro y hy
  rcases eq_or_lt_of_le hy.1 with rfl | hypos
  · have hrecip : 0 < 1 / x := one_div_pos.mpr hx
    have hev : (fun y : ℝ => suzukiSourceHFinite omega (x * y)) =ᶠ[nhds 0]
        fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hrecip] with z hz
      rw [suzukiSourceHFinite, if_neg]
      exact not_lt_of_ge (calc
        x * z ≤ x * (1 / x) := mul_le_mul_of_nonneg_left hz.le hx.le
        _ = 1 := by field_simp)
    exact (continuousAt_const.congr_of_eventuallyEq hev).continuousWithinAt
  · exact ((continuousAt_suzukiSourceHFinite homega (mul_pos hx hypos)).comp
      (continuousAt_const.mul continuousAt_id)).continuousWithinAt

/-- Integral linearity needed for Suzuki's passage from (407) to (408), with all cusp-crossing
integrability obligations discharged. -/
theorem suzukiHankelEuler_integral_add_half
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hx : 0 < x) :
    (∫ y in (0 : ℝ)..a,
        suzukiSourceHFinite omega (x * y) *
          (suzukiHankelEulerPhi epsilon omega a homega ha y +
            (1 / 2 : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha y)) =
      (∫ y in (0 : ℝ)..a,
        suzukiSourceHFinite omega (x * y) *
          suzukiHankelEulerPhi epsilon omega a homega ha y) +
      (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..a,
        suzukiSourceHFinite omega (x * y) *
          suzukiHankelPhiGlobal epsilon omega a homega ha y := by
  have hrow : ContinuousOn (fun y : ℝ => suzukiSourceHFinite omega (x * y))
      (uIcc 0 a) := by
    rw [uIcc_of_le (by linarith : 0 ≤ a)]
    exact continuousOn_suzukiHankelRow_Icc homega (by linarith) hx
  have hE : IntervalIntegrable (fun y : ℝ =>
      suzukiSourceHFinite omega (x * y) *
        suzukiHankelEulerPhi epsilon omega a homega ha y) volume 0 a :=
    (intervalIntegrable_suzukiHankelEulerPhi epsilon homega ha).continuousOn_mul hrow
  have hP0 : ContinuousOn (suzukiHankelPhiGlobal epsilon omega a homega ha)
      (uIcc 0 a) := by
    rw [uIcc_of_le (by linarith : 0 ≤ a)]
    exact (continuousOn_suzukiHankelPhiGlobal_nonnegative epsilon homega ha).mono
      (fun _ hy => hy.1)
  have hP : IntervalIntegrable (fun y : ℝ =>
      suzukiSourceHFinite omega (x * y) *
        suzukiHankelPhiGlobal epsilon omega a homega ha y) volume 0 a :=
    (hrow.mul hP0).intervalIntegrable
  rw [show (fun y : ℝ => suzukiSourceHFinite omega (x * y) *
      (suzukiHankelEulerPhi epsilon omega a homega ha y +
        (1 / 2 : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha y)) =
      fun y => suzukiSourceHFinite omega (x * y) *
          suzukiHankelEulerPhi epsilon omega a homega ha y +
        (1 / 2 : ℂ) * (suzukiSourceHFinite omega (x * y) *
          suzukiHankelPhiGlobal epsilon omega a homega ha y) by
        funext y; ring]
  rw [intervalIntegral.integral_add hE (hP.const_mul (1 / 2 : ℂ)),
    intervalIntegral.integral_const_mul]

/-- Suzuki (2012), equation (408), with the literal integrals and Euler field. -/
theorem suzuki_equation_408
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hx : 0 < x) :
    suzukiHankelEulerPhi epsilon omega a homega ha x -
        (1 / 2 : ℂ) *
          (suzukiSourceHFinite omega (a * x) - epsilon.coeff *
            ∫ y in (0 : ℝ)..a, suzukiSourceHFinite omega (x * y) *
              suzukiHankelPhiGlobal epsilon omega a homega ha y) -
        epsilon.coeff * ∫ y in (0 : ℝ)..a,
          suzukiSourceHFinite omega (x * y) *
            (suzukiHankelEulerPhi epsilon omega a homega ha y +
              (1 / 2 : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha y) =
      suzukiHankelEulerPhi epsilon omega a homega ha x -
        (1 / 2 : ℂ) * suzukiSourceHFinite omega (a * x) -
        epsilon.coeff * ∫ y in (0 : ℝ)..a,
          suzukiSourceHFinite omega (x * y) *
            suzukiHankelEulerPhi epsilon omega a homega ha y := by
  rw [suzukiHankelEuler_integral_add_half epsilon homega ha hx]
  ring

/-- Suzuki (2012), equation (409), derived from (407), integral linearity, and the literal
Fredholm equation (405). -/
theorem suzuki_equation_409
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hx : x ∈ SuzukiHankelRegularX a) :
    suzukiHankelEulerPhi epsilon omega a homega ha x -
        epsilon.coeff * ∫ y in (0 : ℝ)..a,
          suzukiSourceHFinite omega (x * y) *
            suzukiHankelEulerPhi epsilon omega a homega ha y =
      ((1 / 2 : ℂ) - epsilon.coeff * (a : ℂ) *
          suzukiHankelPhiGlobal epsilon omega a homega ha a) *
          suzukiSourceHFinite omega (a * x) +
        (a : ℂ) * deriv
          (fun b : ℝ => suzukiSourceHFinite omega (b * x)) a := by
  have h407 := suzuki_equation_407 epsilon homega ha hx
  rw [suzukiHankelEuler_integral_add_half epsilon homega ha hx.1] at h407
  have hfredSub := suzukiHankelPhiGlobal_fredholm_equation
    epsilon homega ha hx.1.le
  have hfred :
      suzukiHankelPhiGlobal epsilon omega a homega ha x +
          epsilon.coeff * ∫ y in (0 : ℝ)..a,
            suzukiSourceHFinite omega (x * y) *
              suzukiHankelPhiGlobal epsilon omega a homega ha y =
        suzukiSourceHFinite omega (a * x) := by
    rw [← integral_subtype_closedInterval_eq_intervalIntegral (by linarith : 0 ≤ a)]
    exact hfredSub
  linear_combination h407 + (1 / 2 : ℂ) * hfred

end RHTower
